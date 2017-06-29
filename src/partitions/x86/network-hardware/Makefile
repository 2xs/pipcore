include ../toolchain.mk



CFLAGS=-m32 -c -nostdlib --freestanding -I$(LIBPIP)/include/
ASFLAGS=$(CFLAGS)

LDFLAGS=-L$(LIBPIP)/lib -I$(LIBPIP)/include/ -melf_i386 -Tlink.ld -lpip
LDFLAGS2=-L$(LIBPIP)/lib -I$(LIBPIP)/include/ -melf_i386 -Tlinkelf.ld -lpip


ASSOURCES=$(wildcard *.S)
CSOURCES:=$(wildcard *.c)
ASOBJ=$(ASSOURCES:.S=.o)
COBJ=$(CSOURCES:.c=.o)

EXEC=minimal.bin

all: $(EXEC)
	@echo Done.

clean:
	rm -f $(ASOBJ) $(COBJ) $(EXEC)

$(EXEC): $(ASOBJ) $(COBJ)
	$(LD) $^ -o $@ $(LDFLAGS)
	$(LD) $^ -o minimal.elf $(LDFLAGS2)

%.o: %.s
	$(AS) $(ASFLAGS) $< -o $@

%.o: %.c
	$(CC) $(CFLAGS) $< -o $@
