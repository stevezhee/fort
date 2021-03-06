.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

PREFIX    ?=
PRJ       := efm32hg-fort
LDSCRIPT  := efm32hg.ld
OPT_LEVEL := z
ARCH      := cortex-m0plus
C_STD     := c11
DBG_LEVEL := 3
Q         := @

OUT := .
CSRC:= $(wildcard src/*.c)
FSRC:= src/blink.fort
HS_FILES=$(shell find ../../src -name \*.hs) $(shell find ../../app -name \*.hs)
OBJ := $(addprefix $(OUT)/, $(filter %.o,$(CSRC:.c=.o) $(addsuffix .o, $(FSRC))))

CC = $(PREFIX)clang
LD = $(PREFIX)ld.lld
LLC = $(PREFIX)llc
SIZE = $(PREFIX)llvm-size
COPY = $(PREFIX)llvm-objcopy
DUMP = $(PREFIX)llvm-objdump
CP = cp -a

TARGET:=$(OUT)/$(PRJ).elf
TARGET_LST:=$(OUT)/$(PRJ).lst
TARGET_BIN:=$(OUT)/$(PRJ).bin
TARGET_MAP:=$(OUT)/$(PRJ).map
TARGET_DFU:=$(OUT)/$(PRJ).dfu

ARCH_FLAGS := --target=armv6-none-eabi
ARCH_FLAGS += -mthumb
ARCH_FLAGS += -march=armv6m
ARCH_FLAGS += -mcpu=cortex-m0plus
ARCH_FLAGS += -mfloat-abi=soft
ARCH_FLAGS += -mfpu=none

LLC_FLAGS := -march=arm
LLC_FLAGS += -mcpu=cortex-m0plus
LLC_FLAGS += -float-abi=soft
LLC_FLAGS += -mattr=+strict-align
LLC_FLAGS += -mtriple=armv6-none-eabi

CFLAGS := $(ARCH_FLAGS)
CFLAGS += -ffreestanding
CFLAGS += -O$(OPT_LEVEL)
CFLAGS += -std=$(C_STD)
CFLAGS += -Wall
CFLAGS += -g$(DBG_LEVEL)

LDFLAGS := --Bstatic
LDFLAGS += --build-id
LDFLAGS += --gc-sections
LDFLAGS += --Map $(TARGET_MAP)
LDFLAGS += --script $(LDSCRIPT)

all: $(TARGET_BIN) $(TARGET_LST) $(TARGET_DFU) size

$(OUT)/$(FSRC).hs: $(FSRC) $(HS_FILES)
	stack --stack-yaml ../../stack.yaml runghc -- -i../../src ../../app/Main.hs $<

$(OUT)/$(FSRC).ll: $(OUT)/$(FSRC).hs
	stack --stack-yaml ../../stack.yaml runghc -- -i../../src $<

$(OUT)/$(FSRC).s: $(OUT)/$(FSRC).ll
	@echo LLC $^
	$(Q)$(LLC) $(LLC_FLAGS) $<

$(OUT)/$(FSRC).o: $(OUT)/$(FSRC).s
	@echo CC $^
	$(Q)$(CC) $(ARCH_FLAGS) -o $@ -c $<

$(OUT)/src/start.o: src/start.c
	@echo CC $^
	@mkdir -p $(dir $@)
	$(Q)$(CC) -o $@ $(CFLAGS) -c $<

$(TARGET): $(OBJ)
	@echo LD $@
	$(Q)$(LD) -o $@ $(LDFLAGS) $(OBJ)

$(TARGET_LST): $(TARGET)
	@echo LIST on $@
	$(Q)$(DUMP) -s -S $< > $@

$(TARGET_BIN): $(TARGET)
	@echo COPY to $@
	$(Q)$(COPY) -O binary $< $@

$(TARGET_DFU): $(TARGET_BIN)
	@echo DFU to $@
	$(Q)$(CP) $(TARGET_BIN) $@
	$(Q)dfu-suffix -v 1209 -p 70b1 -a $@

size: $(TARGET)
	$(Q)$(SIZE) $<

clean:
	@echo CLEAN
	$(Q)rm -f $(OUT)/src/*.ll
	$(Q)rm -f $(OUT)/src/*.s
	$(Q)rm -f $(OUT)/src/*.o
	$(Q)rm -f $(OUT)/src/*.hs
	$(Q)rm -f $(OUT)/*.bin
	$(Q)rm -f $(OUT)/*.dfu
	$(Q)rm -f $(OUT)/*.elf
	$(Q)rm -f $(OUT)/*.lst
	$(Q)rm -f $(OUT)/*.map

rebuild: clean all

flash: rebuild
	@echo DOWNLOAD
	$(Q)dfu-util --download $(TARGET_DFU)

print-%  : ; @echo $* = $($*)

.PHONY: all clean list size rebuild flash
