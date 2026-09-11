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

LIBS=../libeezo

<$MKROOT/proto/mkone

# relink when the library changes (mkone LIBS= links it but does not depend on it)
$PROG: ../libeezo/libeezo.a
