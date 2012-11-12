#
# Compile the bit_nif.c
#

include $(HOME)/erlang/eapi/make/eapi_drv.mk

OBJS = varc_nif.o
ARCH = -arch i386 -arch x86_64
CFLAGS = $(ARCH) -no-cpp-precomp -Wall -I$(ERL_C_INCLUDE_DIR)

../priv/varc_nif.so: $(OBJS)
	$(LD_SHARED) $(ARCH) -o $@ $(OBJS)

%.o:	%.c
	$(CC) -c $(CFLAGS) $<
