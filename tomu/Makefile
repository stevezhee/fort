.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

PREFIX    ?=
PRJ       := tomu-fort
LDSCRIPT  := tomu.ld
OPT_LEVEL := z
ARCH      := cortex-m0plus
C_STD     := c11
DBG_LEVEL := 3
Q         :=

OUT := generated
CSRC:= $(wildcard src/*.c)
FSRC:= $(wildcard src/*.fort)
HS_FILES=$(shell find ../src -name \*.hs) $(shell find ../app -name \*.hs)
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

$(OUT)/src/main.fort.hs: src/main.fort $(HS_FILES)
	stack --stack-yaml ../stack.yaml runghc -- -i../src ../app/Main.hs $<

$(OUT)/src/main.fort.ll: $(OUT)/src/main.fort.hs
	stack --stack-yaml ../stack.yaml runghc -- -i../src $<

$(OUT)/src/main.fort.s: $(OUT)/src/main.fort.ll
	@echo LLC $^
	$(Q)$(LLC) $(LLC_FLAGS) $<

$(OUT)/src/main.fort.o: $(OUT)/src/main.fort.s
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
	@rm -fR $(OUT)

rebuild: clean all

flash: rebuild
	@echo DOWNLOAD
	$(Q)dfu-util --download $(TARGET_DFU)

print-%  : ; @echo $* = $($*)

.PHONY: all clean list size rebuild flash
