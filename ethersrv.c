/*
 * ethersrv is serving files through the EtherDFS protocol. Runs on FreeBSD
 * and Linux.
 *
 * http://etherdfs.sourceforge.net
 *
 * ethersrv is distributed under the terms of the MIT License, as listed below.
 *
 * Copyright (C) 2017, 2018 Mateusz Viste
 * Copyright (c) 2020 Michael Ortmann
 * Copyright (c) 2023-2025 E. Voirin (oerg866)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include <arpa/inet.h>       /* htons() */
#include <errno.h>
#include <fcntl.h>           /* fcntl(), open() */
#if defined(__FreeBSD__) || defined(__APPLE__)
  #include <sys/types.h>     /* u_int32_t */
  #include <net/bpf.h>       /* BIOCSETIF */
  #include <net/ethernet.h>  /* ETHER_ADDR_LEN */
  #include <net/if_dl.h>     /* LLADDR */
  #include <sys/endian.h>
  #include <sys/sysctl.h>
#else
  #include <endian.h>        /* le16toh(), le32toh() */
  #include <net/ethernet.h>
  #include <netpacket/packet.h> /* sockaddr_ll */
#endif
#include <limits.h>          /* PATH_MAX and such */
#include <net/if.h>
#include <signal.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>          /* mempcy() */
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <stdint.h>          /* uint16_t, uint32_t */
#include <stdlib.h>          /* realpath() */
#include <time.h>            /* time() */
#include <unistd.h>          /* close(), getopt(), optind */

#include "debug.h"
#include "fs.h"
#include "lock.h"

/* program version */
#define PVER "20250324"

#define ETHERTYPE_DFS 0xEDF5

/* protocol version (single byte, must be in sync with etherdfs) */
#define PROTOVER 2


/* answer cache - last answers sent to clients - used if said client didn't
 * receive my answer, and re-sends his requests so I don't process this
 * request again (which might be dangerous in case of write requests, like
 * write to file, delete file, rename file, etc. For every client that ever
 * sent me a query, there is exactly one entry in the cache. */
#define ANSWCACHESZ 16
static struct struct_answcache {
  unsigned char frame[1520]; /* entire frame that was sent (first 6 bytes is the client's mac) */
  time_t timestamp; /* time of answer (so if cache full I can drop oldest) */
  unsigned short len;  /* frame's length */
} answcache[ANSWCACHESZ];

#define BUFF_LEN 2048

/* all the calls I support are in the range AL=0..2Eh - the list below serves
 * as a convenience to compare AL (subfunction) values */
enum AL_SUBFUNCTIONS {
  AL_INSTALLCHK = 0x00,
  AL_RMDIR      = 0x01,
  AL_MKDIR      = 0x03,
  AL_CHDIR      = 0x05,
  AL_CLSFIL     = 0x06,
  AL_CMMTFIL    = 0x07,
  AL_READFIL    = 0x08,
  AL_WRITEFIL   = 0x09,
  AL_LOCKFIL    = 0x0A,
  AL_UNLOCKFIL  = 0x0B,
  AL_DISKSPACE  = 0x0C,
  AL_SETATTR    = 0x0E,
  AL_GETATTR    = 0x0F,
  AL_RENAME     = 0x11,
  AL_DELETE     = 0x13,
  AL_OPEN       = 0x16,
  AL_CREATE     = 0x17,
  AL_FINDFIRST  = 0x1B,
  AL_FINDNEXT   = 0x1C,
  AL_SKFMEND    = 0x21,
  AL_UNKNOWN_2D = 0x2D,
  AL_SPOPNFIL   = 0x2E,
  AL_UNKNOWN    = 0xFF
};


/* an array with flags indicating whether given drive is FAT-based or not */
static unsigned char drivesfat[26]; /* 0 if not, non-zero otherwise */

/* the flag is set when ethersrv is expected to terminate */
static sig_atomic_t volatile terminationflag = 0;

static void sigcatcher(int sig) {
  switch (sig) {
    case SIGTERM:
    case SIGQUIT:
    case SIGINT:
      terminationflag = 1;
      break;
    default:
      break;
  }
}

/* returns a printable version of a FCB block (ie. with added null terminator), this is used only by debug routines */
#if DEBUG > 0
static char *pfcb(char *s) {
  static char r[12] = "FILENAMEEXT";
  memcpy(r, s, 11);
  return(r);
}
#endif

/* turns a character c into its low-case variant */
static char lochar(char c) {
  if ((c >= 'A') && (c <= 'Z')) c += ('a' - 'A');
  return(c);
}

/* turns a string into all-lower-case characters, up to n chars max */
static void lostring(char *s, int n) {
  while ((n-- != 0) && (*s != 0)) {
    *s = lochar(*s);
    s++;
  }
}

/* finds the cache entry related to given client */
static struct struct_answcache *findcacheentry(unsigned char *clientmac) {
  int i, oldest = 0;
  /* iterate through cache entries until matching mac is found */
  for (i = 0; i < ANSWCACHESZ; i++) {
    if (memcmp(answcache[i].frame, clientmac, 6) == 0) {
      return(&(answcache[i])); /* found! */
    }
    /* is this the oldest entry? remember it. */
    if (answcache[i].timestamp < answcache[oldest].timestamp) oldest = i;
  }
  /* if nothing found, over-write the oldest entry */
  return(&(answcache[oldest]));
}


/* checks whether dir is belonging to the root directory. returns 0 if so, 1
 * otherwise */
static int isroot(char *root, char *dir) {
  /* fast-forward to the 'virtual directory' part */
  while ((*root != 0) && (*dir != 0)) {
    root++;
    dir++;
  }
  /* skip any leading / */
  while (*dir == '/') dir++;
  /* is there any subsequent '/' ? if so, then it's not root */
  while (*dir != 0) {
    if (*dir == '/') return(0);
    dir++;
  }
  /* otherwise it's root */
  return(1);
}


/* explode a full X:\DIR\FILE????.??? search path into directory and mask */
static void explodepath(char *dir, char *file, char *source, int sourcelen) {
  int i, lastbackslash;
  /* if drive present, skip it */
  if (source[1] == ':') {
    source += 2;
    sourcelen -= 2;
  }
  /* find last slash or backslash and copy source into dir up to this last backslash */
  lastbackslash = 0;
  for (i = 0; i < sourcelen; i++) {
    if ((source[i] == '\\') || (source[i] == '/')) lastbackslash = i;
  }
  memcpy(dir, source, lastbackslash + 1);
  dir[lastbackslash + 1] = 0;
  /* copy file/mask into file */
  memcpy(file, source+lastbackslash+1, sourcelen - (lastbackslash + 1));
  file[sourcelen - (lastbackslash + 1)] = 0;
}


/* replaces all rep chars in string s by repby */
static void charreplace(char *s, char rep, char repby) {
  while (*s != 0) {
    if (*s == rep) *s = repby;
    s++;
  }
}

/* copies everything after last slash into dst */
static void copy_after_last_slash(char *dst, const char *src) {
    const char *last_slash = strrchr(src, '/');

    if (last_slash)
        strcpy(dst, last_slash + 1);
}



static int process(struct struct_answcache *answer, unsigned char *reqbuff, int reqbufflen, unsigned char *mymac, char **rootarray) {
  int query, reqdrv, reqflags;
  int reslen = 0;
  unsigned short *ax;     /* pointer to store the value of AX after the query */
  unsigned char *answ;    /* convenience pointer to answer->frame */
  unsigned short *wreqbuff; /* same as query, but word-based (16 bits) */
  unsigned short *wansw;  /* same as answer->frame, but word-based (16 bits) */
  char *root;
  answ = answer->frame;
  /* must be at least 60 bytes long */
  if (reqbufflen < 60) return(-1);
  /* does it match the cache entry (same seq and same mac and len > 0)? if so, just re-send it again */
  if ((answ[57] == reqbuff[57]) && (memcmp(answ, reqbuff + 6, 6) == 0) && (answer->len > 0)) {
  #if SIMLOSS > 0
    fprintf(stderr, "Cache HIT (seq %u)\n", answ[57]);
  #endif
    return(answer->len);
  }

  /* copy all headers as-is */
  memcpy(answ, reqbuff, 60);

  /* switch src and dst addresses so the reply header is ready */
  memcpy(answ, answ + 6, 6);  /* copy source mac into dst field */
  memcpy(answ + 6, mymac, 6); /* copy my mac into source field */
  /* remember the pointer to the AX result, and fetch reqdrv and AL query */
  ax = (uint16_t *)answ + 29;
  reqdrv = reqbuff[58] & 31; /* 5 lowest -> drive */
  reqflags = reqbuff[58] >> 5; /* 3 highest bits -> flags */
  reqflags = reqflags; /* just so the compiler won't complain (I don't use flags yet) */
  query = reqbuff[59];
  /* skip eth headers now, as well as padding, seq, reqdrv and AL */
  reqbuff += 60;
  answ += 60;
  reqbufflen -= 60;
  reslen = 0;
  /* set up wansw and wreqbuff */
  wansw = (uint16_t *)answ;
  wreqbuff = (uint16_t *)reqbuff;

  /* is the drive valid? (C: - Z:) */
  if ((reqdrv < 2) || (reqdrv > 25)) { /* 0=A, 1=B, 2=C, etc */
    fprintf(stderr, "invalid drive value: 0x%02Xh\n", reqdrv);
    return(-3);
  }
  /* do I know this drive? */
  root = rootarray[reqdrv];
  if (root == NULL) {
    fprintf(stderr, "unknown drive: %c: (%02Xh)\n", 'A' + reqdrv, reqdrv);
    return(-3);
  }
  /* assume success (hence AX == 0 most of the time) */
  *ax = 0;
  /* let's look at the exact query */
  DBG("Got query: %02Xh [%02X %02X %02X %02X]\n", query, reqbuff[0], reqbuff[1], reqbuff[2], reqbuff[3]);
  if (query == AL_DISKSPACE) {
    unsigned long long diskspace, freespace;
    DBG("DISKSPACE for drive '%c:'\n", 'A' + reqdrv);
    diskspace = diskinfo(root, &freespace);
    /* limit results to slightly under 2 GiB (otherwise MS-DOS is confused) */
    if (diskspace >= 2lu*1024*1024*1024) diskspace = 2lu*1024*1024*1024 - 1;
    if (freespace >= 2lu*1024*1024*1024) freespace = 2lu*1024*1024*1024 - 1;
    DBG("TOTAL: %llu KiB ; FREE: %llu KiB\n", diskspace >> 10, freespace >> 10);
    *ax = 1; /* AX: media id (8 bits) | sectors per cluster (8 bits) -- MSDOS tolerates only 1 here! */
    wansw[1] = htole16(32768);  /* CX: bytes per sector */
    diskspace >>= 15; /* space to number of 32K clusters */
    freespace >>= 15; /* space to number of 32K clusters */
    wansw[0] = htole16(diskspace); /* BX: total clusters */
    wansw[2] = htole16(freespace); /* DX: available clusters */
    reslen += 6;
  } else if ((query == AL_READFIL) && (reqbufflen == 8)) {  /* AL=08h */
    uint16_t len, fileid;
    uint32_t offset;
    long readlen;
    offset = le32toh(((uint32_t *)reqbuff)[0]);
    fileid = le16toh(wreqbuff[2]);
    len = le16toh(wreqbuff[3]);
    DBG("Asking for %u bytes of the file #%u, starting offset %u\n", len, fileid, offset);
    readlen = readfile(answ, fileid, offset, len);
    if (readlen < 0) {
      fprintf(stderr, "ERROR: invalid handle\n");
      *ax = 5; /* "access denied" */
    } else {
      reslen += readlen;
    }
  } else if ((query == AL_WRITEFIL) && (reqbufflen >= 6)) {  /* AL=09h */
    uint16_t fileid;
    uint32_t offset;
    long writelen;
    offset = le32toh(((uint32_t *)reqbuff)[0]);
    fileid = le16toh(wreqbuff[2]);
    DBG("Writing %u bytes into file #%u, starting offset %u\n", reqbufflen - 6, fileid, offset);
    writelen = writefile(reqbuff + 6, fileid, offset, reqbufflen - 6);
    if (writelen < 0) {
      fprintf(stderr, "ERROR: Access denied");
      *ax = 5; /* "access denied" */
    } else {
      wansw[0] = htole16(writelen);
      reslen += 2;
    }
  } else if ((query == AL_LOCKFIL) || (query == AL_UNLOCKFIL)) { /* 0x0A / 0x0B */
    /* I do nothing, except lying that lock/unlock succeeded */
  } else if (query == AL_FINDFIRST) { /* 0x1B */
    struct fileprops fprops;
    char directory[DIR_MAX];
    char host_directory[DIR_MAX];
    unsigned short dirss;
    char filemask[16], filemaskfcb[12];
    int offset;
    unsigned fattr;
    unsigned short fpos = 0;
    int flags;
    fattr = reqbuff[0];
    offset = sprintf(directory, "%s/", root);
    /* */
    /* explode the full "\DIR\FILE????.???" search path into directory and mask */
    explodepath(directory + offset, filemask, (char *)reqbuff + 1, reqbufflen - 1);
    lostring(directory + offset, -1);
    lostring(filemask, -1);
    charreplace(directory, '\\', '/');
    /* */
    filename2fcb(filemaskfcb, filemask);
    DBG("FindFirst in '%s'\nfilemask: '%s' (FCB '%s')\nattribs: 0x%2X\n", directory, filemask, pfcb(filemaskfcb), fattr);
    flags = 0;
    if (isroot(root, directory) != 0) flags |= FFILE_ISROOT;
    if (drivesfat[reqdrv] != 0) flags |= FFILE_ISFAT;

    /* try to get the host name for this string */
    if (shorttolong(host_directory, directory, root) != 0) {
      fprintf(stderr, "FINDFIRST Error (%s): Cannot obtain host path for directory.", directory);
      /* let the rest of the code path deal with error handling, whatever... */
    }

    dirss = getitemss(host_directory);
    if ((dirss == 0xffffu) || (findfile(&fprops, dirss, filemaskfcb, fattr, &fpos, flags) != 0)) {
      DBG("No matching file found\n");
      *ax = 0x12; /* 0x12 is "no more files" -- one would assume 0x02 "file not found" would be better, but that's not what MS-DOS 5.x does, some applications rely on a failing FFirst to return 0x12 (for example LapLink 5) */
    } else { /* found a file */
      DBG("found file: FCB '%s' (attr %02Xh)\n", pfcb(fprops.fcbname), fprops.fattr);
      answ[0] = fprops.fattr; /* fattr (1=RO 2=HID 4=SYS 8=VOL 16=DIR 32=ARCH 64=DEVICE) */
      memcpy(answ + 1, fprops.fcbname, 11);
      answ[12] = fprops.ftime & 0xff;
      answ[13] = (fprops.ftime >> 8) & 0xff;
      answ[14] = (fprops.ftime >> 16) & 0xff;
      answ[15] = (fprops.ftime >> 24) & 0xff;
      answ[16] = fprops.fsize & 0xff;         /* fsize */
      answ[17] = (fprops.fsize >> 8) & 0xff;  /* fsize */
      answ[18] = (fprops.fsize >> 16) & 0xff; /* fsize */
      answ[19] = (fprops.fsize >> 24) & 0xff; /* fsize */
      wansw[10] = htole16(dirss); /* dir id */
      wansw[11] = htole16(fpos); /* file position in dir */
      reslen = 24;
    }
  } else if (query == AL_FINDNEXT) { /* 0x1C */
    unsigned short fpos;
    struct fileprops fprops;
    char *fcbmask;
    unsigned char fattr;
    unsigned short dirss;
    int flags;
    dirss = le16toh(wreqbuff[0]);
    fpos = le16toh(wreqbuff[1]);
    fattr = reqbuff[4];
    fcbmask = (char *)reqbuff + 5;
    /* */
    DBG("FindNext looks for nth file %u in dir #%u\nfcbmask: '%s'\nattribs: 0x%2X\n", fpos, dirss, pfcb(fcbmask), fattr);
    flags = 0;
    if (isroot(root, sstoitem(dirss)) != 0) flags |= FFILE_ISROOT;
    if (drivesfat[reqdrv] != 0) flags |= FFILE_ISFAT;
    if (findfile(&fprops, dirss, fcbmask, fattr, &fpos, flags)) {
      DBG("No more matching files found\n");
      *ax = 0x12; /* "no more files" */
    } else { /* found a file */
      DBG("found file: FCB '%s' (attr %02Xh)\n", pfcb(fprops.fcbname), fprops.fattr);
      answ[0] = fprops.fattr; /* fattr (1=RO 2=HID 4=SYS 8=VOL 16=DIR 32=ARCH 64=DEVICE) */
      memcpy(answ + 1, fprops.fcbname, 11);
      answ[12] = fprops.ftime & 0xff;
      answ[13] = (fprops.ftime >> 8) & 0xff;
      answ[14] = (fprops.ftime >> 16) & 0xff;
      answ[15] = (fprops.ftime >> 24) & 0xff;
      answ[16] = fprops.fsize & 0xff;         /* fsize */
      answ[17] = (fprops.fsize >> 8) & 0xff;  /* fsize */
      answ[18] = (fprops.fsize >> 16) & 0xff; /* fsize */
      answ[19] = (fprops.fsize >> 24) & 0xff; /* fsize */
      wansw[10] = htole16(dirss); /* dir id */
      wansw[11] = htole16(fpos);  /* file position in dir */
      reslen = 24;
    }
  } else if ((query == AL_MKDIR) || (query == AL_RMDIR)) { /* MKDIR or RMDIR */
    char directory[DIR_MAX];
    char host_directory[DIR_MAX];
    int offset;
    offset = sprintf(directory, "%s/", root);
    /* explode the full "\DIR\FILE????.???" search path into directory and mask */
    memcpy(directory + offset, (char *)reqbuff, reqbufflen);
    directory[offset + reqbufflen] = 0;
    lostring(directory + offset, -1);
    charreplace(directory, '\\', '/');

    /* try to get the host name for this string */
    /* HACK: so we expect this to fail because, but shorttolong *does* append the last section of the requested path as is, so we just try with that */
    if (shorttolong(host_directory, directory, root) == 0) {
      fprintf(stderr, "MKDIR Error (%s): A file exists that matches this name pattern.\n", directory);
    }

    if (query == AL_MKDIR) {
      DBG("MKDIR '%s'\n", host_directory);
      if (makedir(host_directory) != 0) {
        *ax = 29;
        fprintf(stderr, "MKDIR Error: %s\n", strerror(errno));
      }
    } else {
      DBG("RMDIR '%s'\n", host_directory);
      if (remdir(host_directory) != 0) {
        *ax = 29;
        fprintf(stderr, "RMDIR Error: %s\n", strerror(errno));
      }
    }
  } else if (query == AL_CHDIR) { /* check if dir exist, return ax=0 if so, ax=3 otherwise */
    char directory[DIR_MAX];
    char host_directory[DIR_MAX];
    int offset;
    offset = sprintf(directory, "%s/", root);
    memcpy(directory + offset, (char *)reqbuff, reqbufflen);
    directory[offset + reqbufflen] = 0;
    lostring(directory + offset, -1);
    charreplace(directory, '\\', '/');
    DBG("CHDIR '%s'\n", directory);

    /* try to get the host name for this string */
    if (shorttolong(host_directory, directory, root) != 0) {
      fprintf(stderr, "CHDIR Error (%s): Cannot obtain host path for directory.\n", directory);
      *ax = 3;
    } else if (changedir(host_directory) != 0) {
      fprintf(stderr, "CHDIR Error (%s): %s\n", host_directory, strerror(errno));
      *ax = 3;
    }
  } else if (query == AL_CLSFIL) { /* AL_CLSFIL (0x06) */
    /* I do nothing, since I do not keep any open files around anyway.
     * just say 'ok' by sending back AX=0 */
    DBG("CLOSE FILE\n");
    *ax = 0;
  } else if ((query == AL_SETATTR) && (reqbufflen > 1)) { /* AL_SETATTR (0x0E) */
    char fullpathname[DIR_MAX];
    char host_fullpathname[DIR_MAX];
    int offset;
    unsigned char fattr;
    fattr = reqbuff[0];
    /* get full file path */
    offset = sprintf(fullpathname, "%s/", root);
    memcpy(fullpathname + offset, (char *)reqbuff + 1, reqbufflen - 1);
    fullpathname[offset + reqbufflen - 1] = 0;
    lostring(fullpathname + offset, -1);
    charreplace(fullpathname, '\\', '/');

    DBG("SETATTR [file: '%s', attr: 0x%02X]\n", fullpathname, fattr);

    /* try to get the host name for this string */
    if (shorttolong(host_fullpathname, fullpathname, root) != 0) {
      fprintf(stderr, "SETATTR Error (%s): Cannot obtain host path for directory.\n", fullpathname);
      *ax = 2;
    } else if (drivesfat[reqdrv] != 0) {
      /* set attr, but only if drive is FAT */
      if (setitemattr(host_fullpathname, fattr) != 0) *ax = 2;
    }
  } else if ((query == AL_GETATTR) && (reqbufflen > 0)) { /* AL_GETATTR (0x0F) */
    char fullpathname[DIR_MAX];
    char host_fullpathname[DIR_MAX];
    int offset;
    struct fileprops fprops;
    /* get full file path */
    offset = sprintf(fullpathname, "%s/", root);
    memcpy(fullpathname + offset, (char *)reqbuff, reqbufflen);
    fullpathname[offset + reqbufflen] = 0;
    lostring(fullpathname + offset, -1);
    charreplace(fullpathname, '\\', '/');

    DBG("GETATTR on file: '%s' (fatflag=%d)\n", fullpathname, drivesfat[reqdrv]);

    /* try to get the host name for this string */
    if (shorttolong(host_fullpathname, fullpathname, root) != 0) {
      fprintf(stderr, "GETATTR Error (%s): Cannot obtain host path for directory.\n", fullpathname);
      *ax = 2;
    } else if (getitemattr(host_fullpathname, &fprops, drivesfat[reqdrv]) == 0xFF) {
      DBG("no file found\n");
      *ax = 2;
    } else {
      DBG("found it (%lu bytes, attr 0x%02X)\n", fprops.fsize, fprops.fattr);
      answ[reslen++] = fprops.ftime & 0xff;
      answ[reslen++] = (fprops.ftime >> 8) & 0xff;
      answ[reslen++] = (fprops.ftime >> 16) & 0xff;
      answ[reslen++] = (fprops.ftime >> 24) & 0xff;
      answ[reslen++] = fprops.fsize & 0xff;
      answ[reslen++] = (fprops.fsize >> 8) & 0xff;
      answ[reslen++] = (fprops.fsize >> 16) & 0xff;
      answ[reslen++] = (fprops.fsize >> 24) & 0xff;
      answ[reslen++] = fprops.fattr;
    }
  } else if ((query == AL_RENAME) && (reqbufflen > 2)) { /* AL_RENAME (0x11) */
    /* query is LSSS...DDD... */
    char fn1[1024], fn2[1024];
    char host_fn1[1024];
    int fn1len, fn2len, offset;
    offset = sprintf(fn1, "%s/", root);
    sprintf(fn2, "%s/", root);
    fn1len = reqbuff[0];
    fn2len = reqbufflen - (1 + fn1len);
    if (reqbufflen > fn1len) {
      memcpy(fn1 + offset, reqbuff + 1, fn1len);
      fn1[fn1len + offset] = 0;
      lostring(fn1 + offset, -1);
      charreplace(fn1, '\\', '/');
      memcpy(fn2 + offset, reqbuff + 1 + fn1len, fn2len);
      fn2[fn2len + offset] = 0;
      lostring(fn2 + offset, -1);
      charreplace(fn2, '\\', '/');

      DBG("RENAME src='%s' dst='%s'\n", fn1, fn2);

      /* try to get the host name for this string */
      if (shorttolong(host_fn1, fn1, root) != 0) {
        fprintf(stderr, "RENAME Error (%s): Cannot obtain host path for directory.\n", fn1);
      } else {
        if (getitemattr(fn2, NULL, 0) != 0xff) {
          /* if fn2 destination exists, abort with errcode=5 (as does MS-DOS 5) */
            DBG("ERROR: '%s' exists already\n", fn2);
            *ax = 5;
          } else {
            DBG("'%s' doesn't exist -> proceed with renaming\n", fn2);
            if (renfile(host_fn1, fn2) != 0) *ax = 5;
          }
      }
    } else {
      *ax = 2;
    }
  } else if (query == AL_DELETE) {
    char fullpathname[DIR_MAX];
    char host_fullpathname[DIR_MAX];
    int offset;
    /* compute full path/file first */
    offset = sprintf(fullpathname, "%s/", root);
    memcpy(fullpathname + offset, reqbuff, reqbufflen);
    fullpathname[reqbufflen + offset] = 0;
    lostring(fullpathname + offset, -1);
    charreplace(fullpathname, '\\', '/');
    DBG("DELETE '%s'\n", fullpathname);

    
    /* try to get the host name for this string */
    if (shorttolong(host_fullpathname, fullpathname, root) != 0) {
      fprintf(stderr, "DELETE Error (%s): Cannot obtain host path for directory.\n", fullpathname);
      *ax = 2;
    } else if (getitemattr(host_fullpathname, NULL, drivesfat[reqdrv]) & 1) { /* is it read-only? */    
      *ax = 5; /* "access denied" */
    } else if (delfiles(host_fullpathname) < 0) {
      *ax = 2;
    }
  } else if ((query == AL_OPEN) || (query == AL_CREATE) || (query == AL_SPOPNFIL)) { /* OPEN is only about "does this file exist", and CREATE "please create or truncate this file", while SPOPNFIL is a combination of both with extra flags */
    struct fileprops fprops;
    char directory[DIR_MAX];
    char host_directory[DIR_MAX];
    char fname[DIR_MAX];
    char fnamefcb[12];
    char fullpathname[DIR_MAX];
    char host_fullpathname[DIR_MAX*2+1];
    int offset;
    int fileres;
    unsigned short stackattr, actioncode, spopen_openmode, spopres = 0;
    unsigned char resopenmode;
    /* fetch args */
    stackattr = le16toh(wreqbuff[0]);
    actioncode = le16toh(wreqbuff[1]);
    spopen_openmode = le16toh(wreqbuff[2]);
    /* compute full path/file */
    offset = sprintf(fullpathname, "%s/", root);
    memcpy(fullpathname + offset, reqbuff + 6, reqbufflen - 6);
    fullpathname[reqbufflen + offset - 6] = 0;
    lostring(fullpathname + offset, -1);
    charreplace(fullpathname, '\\', '/');
    /* compute directory and 'search mask' */
    offset = sprintf(directory, "%s/", root);
    explodepath(directory + offset, fname, (char *)reqbuff+6, reqbufflen-6);

    lostring(directory + offset, -1);
    charreplace(directory, '\\', '/');

    /* does the directory exist? */
    if ((shorttolong(host_directory, directory, root) != 0) || (changedir(host_directory) != 0)) {
      DBG("open/create/spop failed because directory does not exist\n");
      *ax = 3; /* "path not found" */
    } else {
      /* Directory exists, attempt to get host version of the full path name, hoping it exists. */
      if (shorttolong(host_fullpathname, fullpathname, root) == 0) {
        /* if it does, copy its filename to host_fname.*/
        DBG("Exists, pre:  fname '%s' host_fullpathname '%s'\n", fname, host_fullpathname);
        copy_after_last_slash(fname, host_fullpathname);
        DBG("Exists, post: fname '%s' host_fullpathname '%s'\n", fname, host_fullpathname);
      } else {
        /* if it doesn't exist, make file name lowercase and then craft the host full path name */
        sprintf(host_fullpathname, "%s/%s", host_directory, fname);
      }

      /* compute a FCB-style version of the filename */
      filename2fcb(fnamefcb, fname);
      /* */
      DBG("stack word: %04X\n", stackattr);
      DBG("looking for file '%s' (FCB '%s') in '%s'\n", fname, pfcb(fnamefcb), directory);
      /* open or create file, depending on exact subfunction */
      if (query == AL_CREATE) {
        DBG("CREATEFIL / stackattr (attribs)=%04Xh / fn='%s'\n", stackattr, fullpathname);
        fileres = createfile(&fprops, host_directory, fname, stackattr & 0xff, drivesfat[reqdrv]);
        resopenmode = 2; /* read/write */
      } else if (query == AL_SPOPNFIL) {
        /* actioncode contains instructions about how to behave...
         *   high nibble = action if file does NOT exist:
         *     0000 fail
         *     0001 create
         *   low nibble = action if file DOES exist
         *     0000 fail
         *     0001 open
         *     0010 replace/open */
        int attr;
        DBG("SPOPNFIL / stackattr=%04Xh / action=%04Xh / openmode=%04Xh / fn='%s'\n", stackattr, actioncode, spopen_openmode, fullpathname);
        /* see if file exists (and is a file) */
        attr = getitemattr(host_fullpathname, &fprops, drivesfat[reqdrv]);
        resopenmode = spopen_openmode & 0x7f; /* that's what PHANTOM.C does */
        if (attr == 0xff) { /* file not found - look at high nibble of action code */
          DBG("file doesn't exist -> ");
          if ((actioncode & 0xf0) == 16) { /* create */
            DBG("create file host_fullpathname='%s' fname='%s'\n", host_fullpathname, fname);
            fileres = createfile(&fprops, host_directory, fname, stackattr & 0xff, drivesfat[reqdrv]);
            if (fileres == 0) spopres = 2; /* spopres == 2 means 'file created' */
          } else { /* fail */
            DBG("fail\n");
            fileres = 1;
          }
        } else if ((attr & (FAT_VOL | FAT_DIR)) != 0) { /* item is a DIR or a VOL */
          DBG("fail: item '%s' is either a DIR or a VOL\n", fullpathname);
          fileres = 1;
        } else { /* file found (not a VOL, not a dir) - look at low nibble of action code */
          DBG("file exists already (attr %02Xh) -> ", attr);
          if ((actioncode & 0x0f) == 1) { /* open */
            DBG("open file\n");
            fileres = 0;
            spopres = 1; /* spopres == 1 means 'file opened' */
          } else if ((actioncode & 0x0f) == 2) { /* truncate */
            DBG("truncate file host_fullpathname='%s' fname='%s'\n", host_fullpathname, fname);
            fileres = createfile(&fprops, host_directory, fname, stackattr & 0xff, drivesfat[reqdrv]);
            if (fileres == 0) spopres = 3; /* spopres == 3 means 'file truncated' */
          } else { /* fail */
            DBG("fail\n");
            fileres = 1;
          }
        }
      } else { /* simple 'OPEN' */
        int attr;
        DBG("OPENFIL / stackattr (open modes)=%04Xh / fn='%s'\n", stackattr, fullpathname);
        resopenmode = stackattr & 0xff;
        attr = getitemattr(host_fullpathname, &fprops, drivesfat[reqdrv]);
        /* check that item exists, and is neither a volume nor a directory */
        if ((attr != 0xff) && ((attr & (FAT_VOL | FAT_DIR)) == 0)) {
          fileres = 0;
        } else {
          fileres = 1;
        }
      }
      if (fileres != 0) {
        DBG("open/create/spop failed with fileres = %d\n", fileres);
        *ax = 2;
      } else { /* success (found a file, created it or truncated it) */
        unsigned short fileid;
        fileid = getitemss(host_fullpathname);
        DBG("found file: '%s' FCB '%s' (id %04X)\n", host_fullpathname, pfcb(fprops.fcbname), fileid);
        DBG("     fsize: %lu\n", fprops.fsize);
        DBG("     fattr: %02Xh\n", fprops.fattr);
        DBG("     ftime: %04lX\n", fprops.ftime);
        if (fileid == 0xffffu) {
          fprintf(stderr, "ERROR: failed to get a proper fileid!\n");
          return(-1);
        }
        answ[reslen++] = fprops.fattr; /* fattr (1=RO 2=HID 4=SYS 8=VOL 16=DIR 32=ARCH 64=DEVICE) */
        memcpy(answ + reslen, fprops.fcbname, 11);
        reslen += 11;
        answ[reslen++] = fprops.ftime & 0xff; /* time: YYYYYYYM MMMDDDDD hhhhhmmm mmmsssss */
        answ[reslen++] = (fprops.ftime >> 8) & 0xff;
        answ[reslen++] = (fprops.ftime >> 16) & 0xff;
        answ[reslen++] = (fprops.ftime >> 24) & 0xff;
        answ[reslen++] = fprops.fsize & 0xff;         /* fsize */
        answ[reslen++] = (fprops.fsize >> 8) & 0xff;  /* fsize */
        answ[reslen++] = (fprops.fsize >> 16) & 0xff; /* fsize */
        answ[reslen++] = (fprops.fsize >> 24) & 0xff; /* fsize */
        answ[reslen++] = fileid & 0xff;
        answ[reslen++] = fileid >> 8;
        /* CX result (only relevant for SPOPNFIL) */
        answ[reslen++] = spopres & 0xff;
        answ[reslen++] = spopres >> 8;
        answ[reslen++] = resopenmode;
      }
    }
  } else if ((query == AL_SKFMEND) && (reqbufflen == 6)) { /* SKFMEND (0x21) */
    /* translate a 'seek from end' offset into an 'seek from start' offset */
    int32_t offs = le32toh(((uint32_t *)reqbuff)[0]);
    long fsize;
    unsigned short fss = le16toh(((unsigned short *)reqbuff)[2]);
    DBG("SKFMEND on file #%u at offset %d\n", fss, offs);
    /* if arg is positive, zero it out */
    if (offs > 0) offs = 0;
    /* */
    fsize = getfopsize(fss);
    if (fsize < 0) {
      DBG("ERROR: file not found or other error\n");
      *ax = 2;
    } else { /* compute new offset and send it back */
      DBG("file #%u is %lu bytes long\n", fss, fsize);
      offs += fsize;
      if (offs < 0) offs = 0;
      DBG("new offset: %d\n", offs);
      ((uint32_t *)answ)[0] = htole32(offs);
      reslen = 4;
    }
  } else { /* unknown query - ignore */
    return(-1);
  }
  return(reslen + 60);
}


static int raw_sock(const char *const interface, void *const hwaddr) {
  struct ifreq iface;
  int socketfd, fl;
#if defined(__FreeBSD__) || defined(__APPLE__)
  #define PATH_BPF "/dev/bpf"
  int i = 0;
  char filename[sizeof PATH_BPF "-9223372036854775808"]; /* 29 */
  int immediate = 1;
  static struct bpf_insn bf_insn[] = {
    /* Make sure this is an ETHERTYPE_DFS packet... */
    BPF_STMT(BPF_LD + BPF_H + BPF_ABS, 12),
    BPF_JUMP(BPF_JMP + BPF_JEQ + BPF_K, ETHERTYPE_DFS, 0, 1),
    /* If we passed all the tests, ask for the whole packet. */
    BPF_STMT(BPF_RET+BPF_K, (u_int)-1),
    /* Otherwise, drop it. */
    BPF_STMT(BPF_RET+BPF_K, 0),
  };
  struct bpf_program bf_program = {
    sizeof (bf_insn) / (sizeof bf_insn[0]),
    bf_insn 
  };
  int mib[] = {CTL_NET, AF_ROUTE, 0, 0, NET_RT_IFLIST, 0};
  size_t len;
  char *buf;
  struct if_msghdr *ifm;
  struct sockaddr_dl *sdl;
#else
  struct sockaddr_ll addr;
  int result;
  int ifindex;
#endif

  if ((interface == NULL) || (*interface == 0)) {
    errno = EINVAL;
    return(-1);
  }

#if defined(__FreeBSD__) || defined(__APPLE__)
  do {
    snprintf(filename, sizeof(filename), PATH_BPF "%i", i++);
    socketfd = open(filename, O_RDWR);
  } while ((socketfd < 0) && (errno == EBUSY));
#else
  socketfd = socket(AF_PACKET, SOCK_RAW, htons(ETHERTYPE_DFS));
#endif

  if (socketfd == -1) return(-1);

  do {
    memset(&iface, 0, sizeof iface);
    strncpy(iface.ifr_name, interface, sizeof iface.ifr_name - 1);
#if defined(__FreeBSD__) || defined(__APPLE__)
    if (ioctl(socketfd, BIOCSETIF, &iface) < 0) {
      DBG("ERROR: could not bind %s to %s: %s\n", filename, iface.ifr_name, strerror(errno));
      break;
    }
    if (ioctl(socketfd, BIOCIMMEDIATE, &immediate) < 0) {
      DBG("ERROR1: could not enable \"immediate mode\": %s\n", strerror(errno));
      break;
    }
    if (ioctl(socketfd, BIOCSETF, &bf_program) < 0) {
      DBG("ERROR: could not set the bpf program: %s\n", strerror(errno));
      break;
    }
    if ((mib[5] = if_nametoindex(interface)) == 0) {
      DBG("ERROR: if_nametoindex(): %s\n", strerror(errno));
      break;
    }
    if (sysctl(mib, 6, NULL, &len, NULL, 0) < 0) {
      DBG("ERROR: sysctl(): %s\n", strerror(errno));
      break;
    }
    if ((buf = malloc(len)) == NULL) {
      DBG("ERROR: malloc(): %s\n", strerror(errno));
      break;
    }
    if (sysctl(mib, 6, buf, &len, NULL, 0) < 0) {
      DBG("ERROR: sysctl(): %s\n", strerror(errno));
      break;
    }
    ifm = (struct if_msghdr *) buf;
    sdl = (struct sockaddr_dl *) (ifm + 1);
    memcpy(hwaddr, LLADDR(sdl), ETHER_ADDR_LEN);
#else
    result = ioctl(socketfd, SIOCGIFINDEX, &iface);
    if (result == -1) break;
    ifindex = iface.ifr_ifindex;

    memset(&iface, 0, sizeof(iface));
    strncpy(iface.ifr_name, interface, sizeof iface.ifr_name - 1);
    result = ioctl(socketfd, SIOCGIFFLAGS, &iface);
    if (result == -1) break;
    iface.ifr_flags |= IFF_PROMISC;
    result = ioctl(socketfd, SIOCSIFFLAGS, &iface);
    if (result == -1) break;

    memset(&iface, 0, sizeof iface);
    strncpy(iface.ifr_name, interface, sizeof iface.ifr_name - 1);
    result = ioctl(socketfd, SIOCGIFHWADDR, &iface);
    if (result == -1) break;

    memset(&addr, 0, sizeof addr);
    addr.sll_family = AF_PACKET;
    addr.sll_protocol = htons(ETHERTYPE_DFS);
    addr.sll_ifindex = ifindex;
    addr.sll_hatype = 0;
    addr.sll_pkttype = PACKET_HOST | PACKET_BROADCAST;
    addr.sll_halen = ETH_ALEN; /* Assume ethernet! */
    memcpy(&addr.sll_addr, &iface.ifr_hwaddr.sa_data, addr.sll_halen);
    if (hwaddr != NULL) memcpy(hwaddr, &iface.ifr_hwaddr.sa_data, ETH_ALEN);

    if (bind(socketfd, (struct sockaddr *)&addr, sizeof addr)) break;

    errno = 0;
#endif
    /* unblock socket, better safe than sorry */ 
    if ((fl = fcntl(socketfd, F_GETFL)) < 0) {
      DBG("ERROR: fcntl(): %s\n", strerror(errno));
      break;
    }
    fl |= O_NONBLOCK;
    if ((fl = fcntl(socketfd, F_SETFL, fl)) < 0) {
      DBG("ERROR: fcntl(): %s\n", strerror(errno));
      break;
    }

    return(socketfd);
  } while (0);

  {
    const int saved_errno = errno;
    close(socketfd);
    errno = saved_errno;
    return(-1);
  }
}


/* used for debug output of frames on screen */
#if DEBUG > 0
static void dumpframe(unsigned char *frame, int len) {
  int i, b;
  int lines;
  const int LINEWIDTH=16;
  lines = (len + LINEWIDTH - 1) / LINEWIDTH; /* compute the number of lines */
  /* display line by line */
  for (i = 0; i < lines; i++) {
    /* read the line and output hex data */
    for (b = 0; b < LINEWIDTH; b++) {
      int offset = (i * LINEWIDTH) + b;
      if (b == LINEWIDTH / 2) printf(" ");
      if (offset < len) {
        printf(" %02X", frame[offset]);
      } else {
        printf("   ");
      }
    }
    printf(" | "); /* delimiter between hex and ascii */
    /* now output ascii data */
    for (b = 0; b < LINEWIDTH; b++) {
      int offset = (i * LINEWIDTH) + b;
      if (b == LINEWIDTH / 2) printf(" ");
      if (offset >= len) {
        printf(" ");
        continue;
      }
      if ((frame[offset] >= ' ') && (frame[offset] <= '~')) {
        printf("%c", frame[offset]);
      } else {
        printf(".");
      }
    }
    /* newline and loop */
    printf("\n");
  }
}
#endif

/* compare two chunks of data, returns 0 if data is the same, non-zero otherwise */
static int cmpdata(unsigned char *d1, unsigned char *d2, int len) {
  while (len-- > 0) {
    if (*d1 != *d2) return(1);
    d1++;
    d2++;
  }
  return(0);
}

/* compute the BSD checksum of l bytes starting at ptr */
static unsigned short bsdsum(unsigned char *ptr, unsigned short l) {
  unsigned short res = 0;
  for (; l > 0; l--) {
    res = (res << 15) | (res >> 1);
    res += *ptr;
    ptr++;
  }
  return(res);
}

static void help(void) {
  printf("EtherDFS Server (ethersrv) version " PVER "\n"
         "(C) 2017, 2018 Mateusz Viste, 2020 Michael Ortmann, 2023-2025 E. Voirin (oerg866)\n"
         "http://etherdfs.sourceforge.net\n"
         "\n"
         "usage: ethersrv [options] interface rootpath1 [rootpath2] ... [rootpathN]\n"
         "\n"
         "Options:\n"
         "  -f        Keep in foreground (do not daemonize)\n"
         "  -h        Display this information\n"
  );
}

/* daemonize the process, return 0 on success, non-zero otherwise */
static int daemonize(void) {
  pid_t mypid;

  /* I don't want to get notified about SIGHUP */
  signal(SIGHUP, SIG_IGN);

  /* fork off */
  mypid = fork();
  if (mypid == 0) { /* I'm the child, do nothing */
    /* nothing to do - just continue */
  } else if (mypid > 0) { /* I'm the parent - quit now */
    exit(0);
  } else {  /* error condition */
    return(-2);
  }
  return(0);
}

/* generates a formatted MAC address printout and returns a static buffer */
static char *printmac(unsigned char *b) {
  static char macbuf[18];
  sprintf(macbuf, "%02X:%02X:%02X:%02X:%02X:%02X", b[0], b[1], b[2], b[3], b[4], b[5]);
  return(macbuf);
}


int main(int argc, char **argv) {
  int sock, len, i, r;
  unsigned char *buff;
  unsigned char cksumflag;
  unsigned short edf5framelen;
  unsigned char mymac[6];
  char *intname, *root[26];
  struct struct_answcache *cacheptr;
  int opt;
  int daemon = 1; /* daemonize self by default */
#if defined(__FreeBSD__) || defined(__APPLE__)
  int bpf_len;
  unsigned char *bpf_buf;
  struct bpf_hdr *bf_hdr;
#endif
  #define lockfile "/var/run/ethersrv.lock"

  while ((opt = getopt(argc, argv, "fh")) != -1) {
    switch (opt) {
      case 'f': /* -f: no daemon */
        daemon = 0;
        break;
      case 'h': /* -h: help */
        help();
        return(0);
      case '?': /* error */
        help();
        return(1);
    }
  }
  /* I expect at least two positional arguments, and not more than 26 */
  if (argc - optind < 2 || argc - optind > 26) {
    help();
    return(1);
  }
  intname = argv[optind++];
  /* load all "virtual drive" paths */
  for (i = 0; i < 26; i++) root[i] = NULL;
  for (i = 0; i < (argc - optind); i++) {
    char tmppath[PATH_MAX];
    if (realpath(argv[i + optind], tmppath) == NULL) {
      fprintf(stderr, "ERROR: failed to resolve path '%s'\n", argv[i + optind]);
      return(1);
    }
    root[i + 2] = strdup(tmppath);
    if (isfat(root[i + 2]) == 0) {
      drivesfat[i + 2] = 1;
    } else {
      drivesfat[i + 2] = 0;
      fprintf(stderr, "WARNING: the path '%s' doesn't seem to be stored on a FAT filesystem! DOS attributes won't be supported.\n\n", root[i + 2]);
    }
  }

  sock = raw_sock(intname, mymac);
  if (sock == -1) {
    fprintf(stderr, "Error: failed to open socket (%s)\n"
                    "\n"
                    "Usually ethersrv requires to be launched as root to\n"
                    "be able to handle raw (ethernet) sockets. Are you root?\n", strerror(errno));
    return(1);
  }

  /* setup signals catcher */
  signal(SIGTERM, sigcatcher);
  signal(SIGQUIT, sigcatcher);
  signal(SIGINT, sigcatcher);

  /* acquire the lock file (fail if already exists - likely ethersrv runs already) */
  if (lockme(lockfile) != 0) {
    fprintf(stderr, "Error: failed to acquire a lock. Is ethersrv running already? If not, and you're really sure of that, then delete the lock file at '%s'.\n", lockfile);
    return(1);
  }
  printf("Listening on '%s' [%s]\n", intname, printmac(mymac));
  for (i = 2; i < 26; i++) {
    if (root[i] == NULL) break;
    printf("Drive %c: mapped to %s\n", 'A' + i, root[i]);
  }

  if (daemon != 0) {
    if (daemonize() != 0) {
      fprintf(stderr, "Error: failed to daemonize!\n");
      return(1);
    }
  }
#if defined(__FreeBSD__) || defined(__APPLE__)
  if (ioctl(sock, BIOCGBLEN, &bpf_len) < 0) {
    DBG("ERROR1: could not get the required buffer length for reads on bpf files: %s\n", strerror(errno));
    return(1);
  }
  if ((bpf_buf = malloc(bpf_len)) == NULL) {
    DBG("ERROR: malloc(): %s\n", strerror(errno));
    return(1);
  }
#else
  if ((buff = malloc(BUFF_LEN)) == NULL) {
    DBG("ERROR: malloc(): %s\n", strerror(errno));
    return(1);
  }
#endif

  /* main loop */
  while (1) {
#if DEBUG > 0
    struct timeval stimeout = {10, 0}; /* set timeout to 10s */
#endif
    /* prepare the set of descriptors to be monitored later through select() */
    fd_set fdset;
    FD_ZERO(&fdset);
    FD_SET(sock, &fdset);
    /* wait for something to happen on my socket */
#if DEBUG > 0
    r = select(sock + 1, &fdset, NULL, NULL, &stimeout);
#else
    r = select(sock + 1, &fdset, NULL, NULL, NULL);
#endif
    if (!r)
      continue; /* timeout / heartbeat */
    if (r < 0) {
      if (terminationflag)
        break;
      DBG("ERROR: select(): %s\n", strerror(errno));
      continue;
    }
#if defined(__FreeBSD__) || defined(__APPLE__)
    if ((len = read(sock, bpf_buf, bpf_len)) < (int) sizeof (struct bpf_hdr)) {
      DBG("ERROR: read(): %s\n", strerror(errno));
      continue;
    }
    bf_hdr = (struct bpf_hdr *) bpf_buf;
    buff = bpf_buf + bf_hdr->bh_hdrlen;
#else
    len = recv(sock, buff, BUFF_LEN, MSG_DONTWAIT);
#endif
    if (len < 60) continue; /* restart if less than 60 bytes or negative */
    /* validate this is for me (or broadcast) */
    if ((cmpdata(mymac, buff, 6) != 0) && (cmpdata((unsigned char *)"\xff\xff\xff\xff\xff\xff", buff, 6) != 0)) continue; /* skip anything that is not for me */
    /* is this ETHERTYPE_DFS? */
    if (((unsigned short *)buff)[6] != htons(ETHERTYPE_DFS)) {
      fprintf(stderr, "Error: Received non-ETHERTYPE_DFS frame\n");
      continue;
    }
    /* validate protocol version matches what I expect */
    if ((buff[56] & 127) != PROTOVER) {
      fprintf(stderr, "Error: unsupported protocol version from %s\n", buff + 6);
      continue;
    }
    cksumflag = buff[56] >> 7;
    /* trim of padding, if any, or reject frame if it came truncated */
    edf5framelen = le16toh(((unsigned short *)buff)[26]);
    if (edf5framelen == 0) {
      /* nothing to do, edf5framelen is not provided */
    } else if (edf5framelen > len) { /* frame seems truncated */
      fprintf(stderr, "Error: received a truncated frame from %s\n", printmac(buff + 6));
      continue;
    } else if (edf5framelen < 60) { /* obvious error */
      fprintf(stderr, "Error: received a malformed frame from %s\n", printmac(buff + 6));
      continue;
    } else { /* edf5framelen seems sane, use it instead of the Ethernet length */
      #if DEBUG > 0
        if (len != edf5framelen) {
          DBG("Note: Received frame with padding from %s (edf5len = %u, ethernet len = %u)\n", printmac(buff + 6), edf5framelen, len);
        }
      #endif
      len = edf5framelen;
    }
    /* */
  #if DEBUG > 0
    DBG("Received frame of %d bytes (cksum = %s)\n", len, (cksumflag != 0)?"ENABLED":"DISABLED");
    dumpframe(buff, len);
  #endif
   #if SIMLOSS > 0
    /* simulated frame LOSS (input) */
    if ((rand() & 31) == 0) {
      fprintf(stderr, "INPUT LOSS!\n");
      continue;
    }
   #endif
    /* validate the CKSUM, if any */
    if (cksumflag != 0) {
      unsigned short cksum_remote, cksum_mine;
      cksum_mine = bsdsum(buff + 56, len - 56);
      cksum_remote = le16toh(((unsigned short *)buff)[27]);
      if (cksum_mine != cksum_remote) {
        fprintf(stderr, "CHECKSUM MISMATCH! Computed: 0x%02Xh Received: 0x%02Xh\n", cksum_mine, cksum_remote);
        continue;
      }
    }
    /* */
    cacheptr = findcacheentry(buff + 6);
    /* process frame */
    len = process(cacheptr, buff, len, mymac, root);
    /* update cache entry */
    if (len >= 0) {
      cacheptr->len = len;
      cacheptr->timestamp = time(NULL);
    } else {
      cacheptr->len = 0;
    }
    /* */
   #if SIMLOSS > 0
    /* simulated frame LOSS (output) */
    if ((rand() & 31) == 0) {
      fprintf(stderr, "OUTPUT LOSS!\n");
      continue;
    }
   #endif
    DBG("---------------------------------\n");
    if (len > 0) {
      /* fill in frame's length */
      cacheptr->frame[52] = len & 0xff;
      cacheptr->frame[53] = (len >> 8) & 0xff;
      /* fill in checksum into the answer */
      if (cksumflag != 0) {
        unsigned short newcksum = bsdsum(cacheptr->frame + 56, len - 56);
        cacheptr->frame[54] = newcksum & 0xff;
        cacheptr->frame[55] = (newcksum >> 8) & 0xff;
        cacheptr->frame[56] |= 128; /* make sure to set the CKS bit */
      } else {
        cacheptr->frame[54] = 0;
        cacheptr->frame[55] = 0;
        cacheptr->frame[56] &= 127; /* make sure to reset the CKS bit */
      }
  #if DEBUG > 0
      DBG("Sending back an answer of %d bytes\n", len);
      dumpframe(cacheptr->frame, len);
  #endif
#if defined(__FreeBSD__) || defined(__APPLE__)
      i = write(sock, cacheptr->frame, len);
      if (i < 0) {
        fprintf(stderr, "ERROR: write() returned %d (%s)\n", i, strerror(errno));
      } else if (i != len) {
        fprintf(stderr, "ERROR: write() sent less than expected (%d != %d)\n", i, len);
      }
#else
      i = send(sock, cacheptr->frame, len, 0);
      if (i < 0) {
        fprintf(stderr, "ERROR: send() returned %d (%s)\n", i, strerror(errno));
      } else if (i != len) {
        fprintf(stderr, "ERROR: send() sent less than expected (%d != %d)\n", i, len);
      }
#endif
    } else {
      fprintf(stderr, "Query ignored (result: %d)\n", len);
    }
    DBG("---------------------------------\n");
  }
  /* remove the lock file and quit */
  unlockme(lockfile);
  return(0);
}
