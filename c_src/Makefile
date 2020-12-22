#@BEGIN-C_SRC-DEFAULT-RULES@
ERL=$(shell readlink -f `which erl`)
ERL_TOP=$(ERL:%/bin/erl=%)
OS=$(shell uname -s)
CFLAGS=-MMD -MF .$<.d -I$(ERL_TOP)/usr/include
#@END-C_SRC-DEFAULT-RULES@
CC=gcc
CSOURCES=varp_nif.c xnif_funcs.c
OBJS=$(CSOURCES:%.c=%.o)

CFLAGS+= -std=c99 -fomit-frame-pointer -O3 -Wno-incompatible-pointer-types -Wno-unused-result -Wunused

VARP_DIR=$(realpath ..)
VERSION=$(shell git describe --always --tags)
TARGET=../priv/varp_nif.so

LDFLAGS+=-shared

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CC)  $(LDFLAGS) -o $@ $(OBJS)

%.o:	%.c
	$(CC) $(CFLAGS) -c -fPIC $<

clean:
	rm -rf *.o $(TARGET)
