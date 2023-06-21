#ifndef _h_sh_errnum
#define _h_sh_errnum
#define ERR_NAME	0x10000000
#define ERR_SILENT	0x20000000
#define ERR_OLD		0x40000000
#define ERR_SYNTAX	0
#define ERR_NOTALLOWED	1
#define ERR_WTOOLONG	2
#define ERR_LTOOLONG	3
#define ERR_DOLZERO	4
#define ERR_DOLQUEST	5
#define ERR_INCBR	6
#define ERR_EXPORD	7
#define ERR_BADMOD	8
#define ERR_SUBSCRIPT	9
#define ERR_BADNUM	10
#define ERR_NOMORE	11
#define ERR_FILENAME	12
#define ERR_GLOB	13
#define ERR_COMMAND	14
#define ERR_TOOFEW	15
#define ERR_TOOMANY	16
#define ERR_DANGER	17
#define ERR_EMPTYIF	18
#define ERR_IMPRTHEN	19
#define ERR_NOPAREN	20
#define ERR_NOTFOUND	21
#define ERR_MASK	22
#define ERR_LIMIT	23
#define ERR_TOOLARGE	24
#define ERR_SCALEF	25
#define ERR_UNDVAR	26
#define ERR_DEEP	27
#define ERR_BADSIG	28
#define ERR_UNKSIG	29
#define ERR_VARBEGIN	30
#define ERR_VARTOOLONG	31
#define ERR_VARALNUM	32
#define ERR_JOBCONTROL	33
#define ERR_EXPRESSION	34
#define ERR_NOHOMEDIR	35
#define ERR_CANTCHANGE	36
#define ERR_NULLCOM	37
#define ERR_ASSIGN	38
#define ERR_UNKNOWNOP	39
#define ERR_AMBIG	40
#define ERR_EXISTS	41
#define ERR_INTR	42
#define ERR_RANGE	43
#define ERR_OVERFLOW	44
#define ERR_VARMOD	45
#define ERR_NOSUCHJOB	46
#define ERR_TERMINAL	47
#define ERR_NOTWHILE	48
#define ERR_NOPROC	49
#define ERR_NOMATCH	50
#define ERR_MISSING	51
#define ERR_UNMATCHED	52
#define ERR_NOMEM	53
#define ERR_PIPE	54
#define ERR_SYSTEM	55
#define ERR_STRING	56
#define ERR_JOBS	57
#define ERR_JOBARGS	58
#define ERR_JOBCUR	59
#define ERR_JOBPREV	60
#define ERR_JOBPAT	61
#define ERR_NESTING	62
#define ERR_JOBCTRLSUB	63
#define ERR_BADPLPS	64
#define ERR_STOPPED	65
#define ERR_NODIR	66
#define ERR_EMPTY	67
#define ERR_BADDIR	68
#define ERR_DIRUS	69
#define ERR_HFLAG	70
#define ERR_NOTLOGIN	71
#define ERR_DIV0	72
#define ERR_MOD0	73
#define ERR_BADSCALE	74
#define ERR_SUSPLOG	75
#define ERR_UNKUSER	76
#define ERR_NOHOME	77
#define ERR_HISTUS	78
#define ERR_SPDOLLT	79
#define ERR_NEWLINE	80
#define ERR_SPSTAR	81
#define ERR_DIGIT	82
#define ERR_VARILL	83
#define ERR_NLINDEX	84
#define ERR_EXPOVFL	85
#define ERR_VARSYN	86
#define ERR_BADBANG	87
#define ERR_NOSUBST	88
#define ERR_BADSUBST	89
#define ERR_LHS		90
#define ERR_RHSLONG	91
#define ERR_BADBANGMOD	92
#define ERR_MODFAIL	93
#define ERR_SUBOVFL	94
#define ERR_BADBANGARG	95
#define ERR_NOSEARCH	96
#define ERR_NOEVENT	97
#define ERR_TOOMANYRP	98
#define ERR_TOOMANYLP	99
#define ERR_BADPLP	100
#define ERR_MISRED	101
#define ERR_OUTRED	102
#define ERR_REDPAR	103
#define ERR_INRED	104
#define ERR_ALIASLOOP	105
#define ERR_HISTLOOP	106
#define ERR_ARCH        107
#define ERR_FILEINQ	108
#define ERR_SELOVFL	109
#define ERR_INVALID	110
#define ERR_FLAGS	((int)0xf0000000)
#define ERR_NAME	0x10000000
#define ERR_SILENT	0x20000000
#define ERR_OLD		0x40000000
#define ERR_SYNTAX	0
#define ERR_NOTALLOWED	1
#define ERR_WTOOLONG	2
#define ERR_LTOOLONG	3
#define ERR_DOLZERO	4
#define ERR_DOLQUEST	5
#define ERR_INCBR	6
#define ERR_EXPORD	7
#define ERR_BADMOD	8
#define ERR_SUBSCRIPT	9
#define ERR_BADNUM	10
#define ERR_NOMORE	11
#define ERR_FILENAME	12
#define ERR_GLOB	13
#define ERR_COMMAND	14
#define ERR_TOOFEW	15
#define ERR_TOOMANY	16
#define ERR_DANGER	17
#define ERR_EMPTYIF	18
#define ERR_IMPRTHEN	19
#define ERR_NOPAREN	20
#define ERR_NOTFOUND	21
#define ERR_MASK	22
#define ERR_LIMIT	23
#define ERR_TOOLARGE	24
#define ERR_SCALEF	25
#define ERR_UNDVAR	26
#define ERR_DEEP	27
#define ERR_BADSIG	28
#define ERR_UNKSIG	29
#define ERR_VARBEGIN	30
#define ERR_VARTOOLONG	31
#define ERR_VARALNUM	32
#define ERR_JOBCONTROL	33
#define ERR_EXPRESSION	34
#define ERR_NOHOMEDIR	35
#define ERR_CANTCHANGE	36
#define ERR_NULLCOM	37
#define ERR_ASSIGN	38
#define ERR_UNKNOWNOP	39
#define ERR_AMBIG	40
#define ERR_EXISTS	41
#define ERR_INTR	42
#define ERR_RANGE	43
#define ERR_OVERFLOW	44
#define ERR_VARMOD	45
#define ERR_NOSUCHJOB	46
#define ERR_TERMINAL	47
#define ERR_NOTWHILE	48
#define ERR_NOPROC	49
#define ERR_NOMATCH	50
#define ERR_MISSING	51
#define ERR_UNMATCHED	52
#define ERR_NOMEM	53
#define ERR_PIPE	54
#define ERR_SYSTEM	55
#define ERR_STRING	56
#define ERR_JOBS	57
#define ERR_JOBARGS	58
#define ERR_JOBCUR	59
#define ERR_JOBPREV	60
#define ERR_JOBPAT	61
#define ERR_NESTING	62
#define ERR_JOBCTRLSUB	63
#define ERR_BADPLPS	64
#define ERR_STOPPED	65
#define ERR_NODIR	66
#define ERR_EMPTY	67
#define ERR_BADDIR	68
#define ERR_DIRUS	69
#define ERR_HFLAG	70
#define ERR_NOTLOGIN	71
#define ERR_DIV0	72
#define ERR_MOD0	73
#define ERR_BADSCALE	74
#define ERR_SUSPLOG	75
#define ERR_UNKUSER	76
#define ERR_NOHOME	77
#define ERR_HISTUS	78
#define ERR_SPDOLLT	79
#define ERR_NEWLINE	80
#define ERR_SPSTAR	81
#define ERR_DIGIT	82
#define ERR_VARILL	83
#define ERR_NLINDEX	84
#define ERR_EXPOVFL	85
#define ERR_VARSYN	86
#define ERR_BADBANG	87
#define ERR_NOSUBST	88
#define ERR_BADSUBST	89
#define ERR_LHS		90
#define ERR_RHSLONG	91
#define ERR_BADBANGMOD	92
#define ERR_MODFAIL	93
#define ERR_SUBOVFL	94
#define ERR_BADBANGARG	95
#define ERR_NOSEARCH	96
#define ERR_NOEVENT	97
#define ERR_TOOMANYRP	98
#define ERR_TOOMANYLP	99
#define ERR_BADPLP	100
#define ERR_MISRED	101
#define ERR_OUTRED	102
#define ERR_REDPAR	103
#define ERR_INRED	104
#define ERR_ALIASLOOP	105
#define ERR_HISTLOOP	106
#define ERR_ARCH        107
#define ERR_FILEINQ	108
#define ERR_SELOVFL	109
#define ERR_INVALID	110
#endif /* _h_sh_errnum */
