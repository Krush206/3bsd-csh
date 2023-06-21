#	$NetBSD: Makefile,v 1.42 2018/06/10 17:55:11 christos Exp $
#	@(#)Makefile	8.1 (Berkeley) 5/31/93
#
# C Shell with process control; VM/UNIX VAX Makefile
# Bill Joy UC Berkeley; Jim Kulp IIASA, Austria
#
# To profile, put -DPROF in DFLAGS and -pg in COPTS, and recompile.

WARNS=6

PROG=	csh
DFLAGS=-DEDIT -DBUILTIN -DFILEC -DNLS -DSHORT_STRINGS
# - Editor history not always aligned with shell history,
#   should implement internally
# - Does not handle escaped prompts.
# - Does not do completion
CFLAGS+=-Wall -I${PREFIX}/include -L${PREFIX}/lib ${DFLAGS}
SRCS=	alloc.c char.c const.c csh.c dir.c dol.c err.c exec.c exp.c file.c \
	func.c glob.c hist.c init.c lex.c misc.c parse.c printf.c proc.c \
	sem.c set.c str.c time.c

MLINKS=	csh.1 limit.1 csh.1 alias.1 csh.1 bg.1 csh.1 dirs.1 csh.1 fg.1 \
	csh.1 foreach.1 csh.1 history.1 csh.1 jobs.1 csh.1 popd.1 \
	csh.1 pushd.1 csh.1 rehash.1 csh.1 repeat.1 csh.1 suspend.1 \
	csh.1 stop.1 csh.1 source.1

DPSRCS+=	errnum.h const.h
CLEANFILES+=	errnum.h const.h

all:
	(\
	echo "#ifndef _PATHNAMES_H_" ;\
	echo "#define _PATHNAMES_H_" ;\
	echo "#define _PATH_BIN \"${PREFIX}/bin\"" ;\
	echo "#define _PATH_DOTCSHRC \"${PREFIX}/etc/csh.cshrc\"" ;\
	echo "#define _PATH_DOTLOGIN \"${PREFIX}/etc/csh.login\"" ;\
	echo "#define _PATH_DOTLOGOUT \"${PREFIX}/etc/csh.logout\"" ;\
	echo "#define _PATH_LOGIN \"${PREFIX}/usr/bin/login\"" ;\
	echo "#define _PATH_USRBIN \"${PREFIX}/usr/bin\"" ;\
	echo "#endif /* !_PATHNAMES_H_ */" ;\
	) > pathnames.h
	${CC} -o ${PROG} ${CFLAGS} ${SRCS} -lbsd -ledit -landroid-glob

install:
	install -Dm755 ${PROG} ${PREFIX}/bin/${PROG}
	install -Dm600 ${PROG}.1 ${PREFIX}/share/man/man1/${PROG}.1

errnum.h: err.c
	rm -f $@
	(\
	echo '/* Do not edit this file, make creates it. */' ;\
	echo '#ifndef _h_sh_errnum' ;\
	echo '#define _h_sh_errnum' ;\
	egrep 'ERR_' ${.CURDIR}*.[ch] | egrep '#define' | sed -e 's/.*#define/#define/' ;\
	echo '#endif /* _h_sh_errnum */' ;\
	) > $@

const.c: errnum.h
const.h: const.c
	rm -f $@
	echo '/* Do not edit this file, make creates it. */' > $@
	${CC} -E ${CFLAGS} ${.CURDIR}*.[ch] | egrep 'Char STR' | \
	    sed -e 's/Char \([a-zA-Z0-9_]*\)\(.*\)/extern Char \1[];/' -e 's/.*extern/extern/' | \
	    sort >> $@

SUBDIR.roff+=USD.doc

COPTS.err.c = -Wno-format-nonliteral
COPTS.printf.c = -Wno-format-nonliteral
COPTS.proc.c = -Wno-format-nonliteral
