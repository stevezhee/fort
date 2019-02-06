.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

TEST_DIR=test
HS_FILES=$(shell find src -name \*.hs) $(shell find app -name \*.hs)
FORT_FILES=$(wildcard $(TEST_DIR)/*.fort)
# GEN_FILE_NAMES=$(FORT_FILES:$(TEST_DIR)/%.fort=%)
# GEN_HS_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.hs)
# GEN_LL_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.ll)
# GEN_S_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.s)
# GEN_O_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.o)
# OUT_FILE=a.out

# .PRECIOUS: $(GEN_HS_FILES) $(GEN_LL_FILES) $(GEN_S_FILES) $(GEN_O_FILES)

.PHONY: all
all: # coverage run
	echo $(HS_FILES)

# .PHONY: run
# run: $(OUT_FILE)
# 	./$<

%.fort.hs: %.fort $(HS_FILES)
	stack runghc -- -isrc app/Main.hs $<

%.fort.ll: %.fort.hs
	stack runghc -- -isrc $<

%.fort.s: %.fort.ll
	llc $<
	@echo generated asm $@!

%.fort.o: %.fort.s
	clang -o $@ -c $^
	@echo generated object file $@!

# $(OUT_FILE): main.c $(GEN_O_FILES)
# 	clang -lc $^

# .PHONY: coverage
# coverage: $(HS_FILES)
# 	stack test --coverage

.PHONY: clean
clean:
	stack clean
	rm -f a.out
	rm test/*.ll
	rm test/*.s
	rm test/*.o
	rm test/*.fort.hs
# 	rm -f $(GEN_PATH)/*.*
