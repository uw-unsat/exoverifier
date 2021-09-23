CC=gcc
CFLAGS=`pkg-config gtk+-2.0 --cflags`
LDADD=`pkg-config gtk+-2.0 --libs`
OBJECTS=callbacks.o interface.o main.o support.o
PROGRAM=xc32sat

all: ${OBJECTS}
	${CC} -o ${PROGRAM} ${OBJECTS} ${LDADD}

clean:
	rm -f *.o *.exe temp_in temp_out ${PROGRAM} 
