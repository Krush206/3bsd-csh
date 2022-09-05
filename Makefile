#	$OpenBSD: Makefile,v 1.10 2010/01/04 17:50:36 deraadt Exp $
#
# C Shell with process control; VM/UNIX VAX Makefile
# Bill Joy UC Berkeley; Jim Kulp IIASA, Austria
#
# To profile, put -DPROF in DEFS and -pg in CFLAGS, and recompile.

PROG=	csh
DFLAGS=-DBUILTIN -DFILEC -DNLS -DSHORT_STRINGS
#CFLAGS+=-g
#CFLAGS+=-Wall
CFLAGS+=-I. ${DFLAGS}
SRCS=	alloc.c char.c const.c csh.c dir.c dol.c error.c exec.c exp.c file.c \
	func.c glob.c hist.c init.c lex.c misc.c parse.c proc.c \
	sem.c set.c str.c time.c

CLEANFILES+=error.h const.h

const.h: error.h

error.h: error.c
	@rm -f $@
	@echo '/* Do not edit this file, make creates it. */' > $@
	@echo '#ifndef _h_sh_err' >> $@
	@echo '#define _h_sh_err' >> $@
	egrep 'ERR_' ${.CURDIR}$*.c | egrep '^#define' >> $@
	@echo '#endif /* _h_sh_err */' >> $@

const.h: const.c
	@rm -f $@
	@echo '/* Do not edit this file, make creates it. */' > $@
	${CC} -E ${CFLAGS} ${.CURDIR}$*.c | egrep 'Char STR' | \
	    sed -e 's/Char \([a-zA-Z0-9_]*\)\(.*\)/extern Char \1[];/' | \
	    sort >> $@
	@echo 'Type in "make csh" to build.'

.depend alloc.o: const.h error.h 

csh:
	${CC} ${CFLAGS} ${SRCS}
