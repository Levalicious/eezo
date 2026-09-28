<$MKROOT/$objtype/mkfile

TARG=eezo

OFILES=\
	main.$O\
	stg.$O\
	io.$O\

HFILES=\
	stg.h\
	io.h\
	../libeezo/native.h\
	../libeezo/term.h\

CFLAGS=-Wall -O2 -I..
LIBEEZO=../libeezo/libeezo.a
LIBFILES=$LIBEEZO

<$MKROOT/proto/mkone

# the library, a real prerequisite of the program: built in its directory when its sources change (mkone LIBFILES)
$LIBEEZO: `ls ../libeezo/*.[ch]`
	cd ../libeezo && mk libeezo.a

