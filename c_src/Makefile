#@BEGIN-C_SRC-DEFAULT-RULES@
ERL=$(shell readlink -f "`which erl`")
ERL_TOP=$(ERL:%/bin/erl=%)
OS=$(shell uname -s)
CFLAGS=-MMD -MF .$<.d -I"$(ERL_TOP)/usr/include"
#@END-C_SRC-DEFAULT-RULES@

CSOURCES=varp_nif.c xnif_funcs.c
PRIVDIR=../priv

# -Wno-incompatible-pointer-types -Wno-unused-result
WARN = -Wno-unused-result -Wall -Wunused -Wsign-compare -Wformat
OPT = -O3  -fomit-frame-pointer -march=native
CFLAGS += -DDLOG_DEFAULT=DLOG_NONE              # -DEBUG_MEM 
CFLAGS += $(WARN) $(OPT) -fpic                  # -std=c99 
LDFLAGS+=-shared

ifneq (, $(findstring CYGWIN,$(OS)))
CC=x86_64-w64-mingw32-gcc
LIBS=-luser32 -ladvapi32 -mwindows
CFLAGS += -D__WIN32__ -DWIN32 -D_MT -D_DLL 
LDFLAGS += -lkernel32 $(LIBS)
VARP_NIF=$(PRIVDIR)/varp_nif.dll
VARP_EXE=$(PRIVDIR)/Varp.exe
OBJS=$(CSOURCES:%.c=%.o)
else
CC=gcc
LIBS=
VARP_NIF=$(PRIVDIR)/varp_nif.so
VARP_EXEC=
OBJS=$(CSOURCES:%.c=%.o)
endif

VARP_DIR=$(realpath ..)
VERSION=$(shell git describe --always --tags)

all: $(VARP_NIF) $(VARP_EXE)

$(VARP_NIF): $(OBJS)
	$(CC)  $(LDFLAGS) -o $@ $(OBJS)

ifneq (, $(findstring CYGWIN,$(OS)))
$(VARP_EXE): varp.c varp_res.o
	$(CC) -o $(VARP_EXE) varp.c varp_res.o -mwindows $(LIBS)
endif

%.o:	%.c
	$(CC) $(CFLAGS) -c $<

varp_res.o: varp.rc
	windres -i varp.rc -o varp_res.o

.%.d:	;

-include .*.d

clean:
	rm -rf *.o .*.d $(VARP_NIF) $(VARP_EXE)
