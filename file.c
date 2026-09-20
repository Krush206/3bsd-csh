/* $NetBSD: file.c,v 1.33 2020/09/29 02:58:51 msaitoh Exp $ */

/*-
 * Copyright (c) 1980, 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#ifdef __linux__
#include <bsd/sys/cdefs.h>
#else
#include <sys/cdefs.h>
#endif
#ifndef lint
#if 0
static char sccsid[] = "@(#)file.c	8.2 (Berkeley) 3/19/94";
#else
__RCSID("$NetBSD: file.c,v 1.33 2020/09/29 02:58:51 msaitoh Exp $");
#endif
#endif /* not lint */

#ifdef FILEC

#include <sys/ioctl.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <linux/tty.h>

#include <dirent.h>
#include <pwd.h>
#include <termios.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>

#include <string.h>

#include "csh.h"
#include "extern.h"

/*
 * Tenex style file name recognition, .. and more.
 * History:
 *	Author: Ken Greer, Sept. 1975, CMU.
 *	Finally got around to adding to the Cshell., Ken Greer, Dec. 1981.
 */

#define ON	1
#define OFF	0
#ifndef TRUE
#define TRUE 1
#endif
#ifndef FALSE
#define FALSE 0
#endif

#define ESC '\033'

typedef enum {
    LIST, RECOGNIZE
}       COMMAND;

static void catn(Char *, Char *, size_t);
static void copyn(Char *, Char *, size_t);
static Char filetype(Char *, Char *);
static void print_by_column(Char *, Char *[], size_t);
static Char *tilde(Char *, Char *);
static void beep(void);
static void extract_dir_and_name(Char *, Char *, Char *);
static Char *getentry(DIR *);
static void free_items(Char **, size_t);
static size_t tsearch(Char *, COMMAND, size_t);
static int recognize(Char *, Char *, size_t, size_t);
static int is_prefix(Char *, Char *);
static int is_suffix(Char *, Char *);
static int ignored(Char *);

/*
 * Put this here so the binary can be patched with adb to enable file
 * completion by default.  Filec controls completion, nobeep controls
 * ringing the terminal bell on incomplete expansions.
 */
int filec = 0;

/*
 * Concatenate src onto tail of des.
 * Des is a string whose maximum length is count.
 * Always null terminate.
 */
static void
catn(Char *des, Char *src, size_t count)
{
    while (count-- > 0 && *des)
	des++;
    while (count-- > 0)
	if ((*des++ = *src++) == 0)
	    return;
    *des = '\0';
}

/*
 * Like strncpy but always leave room for trailing \0
 * and always null terminate.
 */
static void
copyn(Char *des, Char *src, size_t count)
{
    while (count-- > 0)
	if ((*des++ = *src++) == 0)
	    return;
    *des = '\0';
}

static Char
filetype(Char *dir, Char *file)
{
    struct stat statb;
    Char path[MAXPATHLEN];

    catn(Strcpy(path, dir), file, sizeof(path) / sizeof(Char));
    if (lstat(short2str(path), &statb) == 0) {
	switch (statb.st_mode & S_IFMT) {
	case S_IFDIR:
	    return ('/');
	case S_IFLNK:
	    if (stat(short2str(path), &statb) == 0 &&	/* follow it out */
		S_ISDIR(statb.st_mode))
		return ('>');
	    else
		return ('@');
	case S_IFSOCK:
	    return ('=');
	default:
	    if (statb.st_mode & 0111)
		return ('*');
	}
    }
    return (' ');
}

static struct winsize win;

/*
 * Print sorted down columns
 */
static void
print_by_column(Char *dir, Char *items[], size_t count)
{
    size_t c, columns, i, maxwidth, r, rows;

    maxwidth = 0;

    if (ioctl(SHOUT, TIOCGWINSZ, (ioctl_t) & win) < 0 || win.ws_col == 0)
	win.ws_col = 80;
    for (i = 0; i < count; i++)
	maxwidth = maxwidth > (r = Strlen(items[i])) ? maxwidth : r;
    maxwidth += 2;		/* for the file tag and space */
    columns = win.ws_col / maxwidth;
    if (columns == 0)
	columns = 1;
    rows = (count + (columns - 1)) / columns;
    for (r = 0; r < rows; r++) {
	for (c = 0; c < columns; c++) {
	    i = c * rows + r;
	    if (i < count) {
		size_t w;

		(void)fprintf(cshout, "%s", vis_str(items[i]));
		(void)fputc(dir ? filetype(dir, items[i]) : ' ', cshout);
		if (c < columns - 1) {	/* last column? */
		    w = Strlen(items[i]) + 1;
		    for (; w < maxwidth; w++)
			(void) fputc(' ', cshout);
		}
	    }
	}
	(void)fputc('\r', cshout);
	(void)fputc('\n', cshout);
    }
}

/*
 * Expand file name with possible tilde usage
 *	~person/mumble
 * expands to
 *	home_directory_of_person/mumble
 */
static Char *
tilde(Char *new, Char *old)
{
    static Char person[40];
    struct passwd *pw;
    Char *o, *p;

    if (old[0] != '~')
	return (Strcpy(new, old));

    for (p = person, o = &old[1]; *o && *o != '/'; *p++ = *o++)
	continue;
    *p = '\0';
    if (person[0] == '\0')
	(void)Strcpy(new, value(STRhome));
    else {
	pw = getpwnam(short2str(person));
	if (pw == NULL)
	    return (NULL);
	(void)Strcpy(new, str2short(pw->pw_dir));
    }
    (void)Strcat(new, o);
    return (new);
}

static void
beep(void)
{
    if (adrof(STRnobeep) == 0)
	(void)write(SHOUT, "\007", 1);
}

/*
 * Parse full path in file into 2 parts: directory and file names
 * Should leave final slash (/) at end of dir.
 */
static void
extract_dir_and_name(Char *path, Char *dir, Char *name)
{
    Char *p;

    p = Strrchr(path, '/');
    if (p == NULL) {
	copyn(name, path, MAXNAMLEN);
	dir[0] = '\0';
    }
    else {
	copyn(name, ++p, MAXNAMLEN);
	copyn(dir, path, (size_t)(p - path));
    }
}

static Char *
getentry(DIR *dir_fd)
{
    struct dirent *dirp;

    if ((dirp = readdir(dir_fd)) != NULL)
	return (str2short(dirp->d_name));
    return (NULL);
}

static void
free_items(Char **items, size_t numitems)
{
    size_t i;

    for (i = 0; i < numitems; i++)
	xfree(items[i]);
    xfree(items);
}

#define FREE_ITEMS(items, numitems) { \
	sigset_t nsigset, osigset;\
\
	sigemptyset(&nsigset);\
	(void) sigaddset(&nsigset, SIGINT);\
	(void) sigprocmask(SIG_BLOCK, &nsigset, &osigset);\
	free_items(items, numitems);\
	(void) sigprocmask(SIG_SETMASK, &osigset, NULL);\
}

/*
 * Perform a RECOGNIZE or LIST command on string "word".
 */
static size_t
tsearch(Char *word, COMMAND command, size_t max_word_length)
{
    Char dir[MAXPATHLEN + 1], extended_name[MAXNAMLEN + 1];
    Char name[MAXNAMLEN + 1], tilded_dir[MAXPATHLEN + 1];
    DIR *dir_fd;
    Char *entry;
    int ignoring;
    size_t name_length, nignored, numitems;
    Char **items = NULL;
    size_t maxitems = 0;

    numitems = 0;
    ignoring = TRUE;
    nignored = 0;

    extract_dir_and_name(word, dir, name);
    if (tilde(tilded_dir, dir) == 0)
        return (0);
    dir_fd = opendir(*tilded_dir ? short2str(tilded_dir) : ".");
    if (dir_fd == NULL)
        return (0);

again:				/* search for matches */
    name_length = Strlen(name);
    for (numitems = 0; (entry = getentry(dir_fd)) != NULL;) {
	if (!is_prefix(name, entry))
	    continue;
	/* Don't match . files on null prefix match */
	if (name_length == 0 && entry[0] == '.')
	    continue;
	if (command == LIST) {
	    if ((size_t)numitems >= maxitems) {
		maxitems += 1024;
		if (items == NULL)
			items = xmalloc(sizeof(*items) * maxitems);
		else
			items = xrealloc(items, sizeof(*items) * maxitems);
 	    }
	    items[numitems] = xmalloc((size_t) (Strlen(entry) + 1) *
	        sizeof(Char));
	    copyn(items[numitems], entry, MAXNAMLEN);
	    numitems++;
	}
	else {			/* RECOGNIZE command */
	    if (ignoring && ignored(entry))
		nignored++;
	    else if (recognize(extended_name,
	        entry, name_length, ++numitems))
		break;
	}
    }
    if (ignoring && numitems == 0 && nignored > 0) {
	ignoring = FALSE;
	nignored = 0;
	rewinddir(dir_fd);
	goto again;
    }

    (void)closedir(dir_fd);
    if (numitems == 0)
	return (0);
    if (command == RECOGNIZE) {
	/* put back dir part */
	copyn(word, dir, max_word_length);
	/* add extended name */
	catn(word, extended_name, max_word_length);
	return (numitems);
    }
    else {			/* LIST */
	qsort(items, numitems, sizeof(items[0]), 
		(int (*) (const void *, const void *)) sortscmp);
	print_by_column(tilded_dir, items, numitems);
	if (items != NULL)
	    FREE_ITEMS(items, numitems);
    }
    return (0);
}

/*
 * Object: extend what user typed up to an ambiguity.
 * Algorithm:
 * On first match, copy full entry (assume it'll be the only match)
 * On subsequent matches, shorten extended_name to the first
 * Character mismatch between extended_name and entry.
 * If we shorten it back to the prefix length, stop searching.
 */
static int
recognize(Char *extended_name, Char *entry, size_t name_length, size_t numitems)
{
    if (numitems == 1)		/* 1st match */
	copyn(extended_name, entry, MAXNAMLEN);
    else {			/* 2nd & subsequent matches */
	Char *ent, *x;
	size_t len = 0;

	x = extended_name;
	for (ent = entry; *x && *x == *ent++; x++, len++)
	    continue;
	*x = '\0';		/* Shorten at 1st Char diff */
	if (len == name_length)	/* Ambiguous to prefix? */
	    return (-1);	/* So stop now and save time */
    }
    return (0);
}

/*
 * Return true if check matches initial Chars in template.
 * This differs from PWB imatch in that if check is null
 * it matches anything.
 */
static int
is_prefix(Char *check, Char *template)
{
    do
	if (*check == 0)
	    return (TRUE);
    while (*check++ == *template++);
    return (FALSE);
}

/*
 *  Return true if the Chars in template appear at the
 *  end of check, I.e., are its suffix.
 */
static int
is_suffix(Char *check, Char *template)
{
    Char *c, *t;

    for (c = check; *c++;)
	continue;
    for (t = template; *t++;)
	continue;
    for (;;) {
	if (t == template)
	    return 1;
	if (c == check || *--t != *--c)
	    return 0;
    }
}

ssize_t
tenex(Char *inputline, size_t inputline_size)
{
    struct termios saved, raw;
    static Char delims[] = {' ', '\'', '"', '\t', ';', '&', '<',
	'>', '(', ')', '|', '^', '%', '\0'};
    size_t cursor = 0, length = 0;
    ssize_t nread = -1;

    if (tcgetattr(SHIN, &saved) < 0)
	return (-1);
    raw = saved;
    raw.c_iflag &= ~(ICRNL | INLCR | IGNCR | IXON);
    raw.c_lflag &= ~(ICANON | ECHO | ECHOE | ECHOK | ECHONL | ECHOCTL | IEXTEN);
    raw.c_cc[VMIN] = 1;
    raw.c_cc[VTIME] = 0;
    if (tcsetattr(SHIN, TCSADRAIN, &raw) < 0)
	return (-1);

    inputline[0] = '\0';
    for (;;) {
	unsigned char ch;
	size_t i;

	nread = read(SHIN, &ch, 1);
	if (nread <= 0)
	    break;
	if (ch == '\r' || ch == '\n') {
	    if (length + 1 >= inputline_size) {
		nread = -1;
		break;
	    }
	    inputline[length++] = '\n';
	    inputline[length] = '\0';
	    (void)fputc('\n', cshout);
	    nread = (ssize_t)length;
	    break;
	}
	if (ch == saved.c_cc[VERASE] || ch == '\b' || ch == '\177') {
	    if (cursor != 0) {
		(void)memmove(&inputline[cursor - 1], &inputline[cursor],
		    (length - cursor + 1) * sizeof(*inputline));
		cursor--;
		length--;
	    }
	} else if (ch == saved.c_cc[VKILL]) {
	    cursor = length = 0;
	    inputline[0] = '\0';
	} else if (ch == '\027') {
	    size_t old_cursor = cursor;

	    while (cursor != 0 && inputline[cursor - 1] == ' ')
		cursor--;
	    while (cursor != 0 && inputline[cursor - 1] != ' ')
		cursor--;
	    (void)memmove(&inputline[cursor], &inputline[old_cursor],
		(length - old_cursor + 1) * sizeof(*inputline));
	    length -= old_cursor - cursor;
	} else if (ch == ESC) {
	    Char *word_start;
	    size_t space_left, numitems;

	    for (word_start = &inputline[cursor]; word_start > inputline;
		--word_start)
		if (Strchr(delims, word_start[-1]))
		    break;
	    space_left = inputline_size -
		(size_t)(word_start - inputline) - 1;
	    numitems = tsearch(word_start, RECOGNIZE, space_left);
	    length = Strlen(inputline);
	    cursor = length;
	    if (numitems != 1)
		beep();
	} else if (ch == '\004') {
	    Char *word_start;
	    size_t space_left;

	    for (word_start = &inputline[cursor]; word_start > inputline;
		--word_start)
		if (Strchr(delims, word_start[-1]))
		    break;
	    (void)fputc('\n', cshout);
	    space_left = inputline_size -
		(size_t)(word_start - inputline) - 1;
	    (void)tsearch(word_start, LIST, space_left);
	} else if (ch >= ' ' && ch != '\177' &&
	    length + 1 < inputline_size) {
	    (void)memmove(&inputline[cursor + 1], &inputline[cursor],
		(length - cursor + 1) * sizeof(*inputline));
	    inputline[cursor++] = ch;
	    length++;
	} else
	    beep();

	(void)fputc('\r', cshout);
	printprompt();
	(void)fprintf(cshout, "%s", vis_str(inputline));
	(void)fputs("\033[K", cshout);
	for (i = cursor; i < length; i++)
	    (void)fputc('\b', cshout);
	(void)fflush(cshout);
    }
    (void)tcsetattr(SHIN, TCSADRAIN, &saved);
    return (nread);
}

static int
ignored(Char *entry)
{
    struct varent *vp;
    Char **cp;

    if ((vp = adrof(STRfignore)) == NULL || (cp = vp->vec) == NULL)
	return (FALSE);
    for (; *cp != NULL; cp++)
	if (is_suffix(entry, *cp))
	    return (TRUE);
    return (FALSE);
}
#endif				/* FILEC */
