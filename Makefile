#
# ethersrv makefile for FreeBSD and Linux (GCC and Clang)
# http://etherdfs.sourceforge.net
#
# Copyright (C) 2017, 2018 Mateusz Viste
# Copyright (C) 2020 Michael Ortmann
# Copyright (C) 2023-2025 E. Voirin (oerg866)
#

CFLAGS := -DDEBUG=1 -O2 -Wall -std=gnu89 -pedantic -Wextra -s -Wno-long-long -Wno-variadic-macros -Wformat-security -D_FORTIFY_SOURCE=1

CC ?= gcc

ethersrv: ethersrv.c fs.c fs.h lock.c lock.h debug.h
	$(CC) ethersrv.c fs.c lock.c -o ethersrv $(CFLAGS)

clean:
	rm -f ethersrv *.o
