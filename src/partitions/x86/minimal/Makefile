include ../toolchain.mk

CFLAGS=-m32 -c -nostdlib --freestanding -I$(LIBPIP)/include/
ASFLAGS=$(CFLAGS)
LDFLAGS=-L$(LIBPIP)/lib -melf_i386 -Tlink.ld -lpip

ASSOURCES=$(wildcard *.s)
CSOURCES=$(wildcard *.c)

ASOBJ=$(ASSOURCES:.s=.o)
COBJ=$(CSOURCES:.c=.o)

EXEC=minimal.bin

all: $(EXEC)
	@echo Done.

clean:
	rm -f $(ASOBJ) $(COBJ) $(EXEC)

$(EXEC): $(ASOBJ) $(COBJ)
	$(LD) $^ -o $@ $(LDFLAGS)

%.o: %.s
	$(AS) $(ASFLAGS) $< -o $@

%.o: %.c
	$(CC) $(CFLAGS) $< -o $@
