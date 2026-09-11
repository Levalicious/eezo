<$MKROOT/$objtype/mkfile

TARG=eezo

OFILES=\
	main.$O\
	stg.$O\

HFILES=\
	stg.h\
	../libeezo/native.h\
	../libeezo/term.h\

LIBS=../libeezo

<$MKROOT/proto/mkone
