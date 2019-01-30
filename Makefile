TEST_DIR=test
GEN_DIR=generated
GEN_PATH=$(GEN_DIR)/$(TEST_DIR)
DIRS = $(TEST_DIR) $(GEN_DIR) $(GEN_PATH)
HS_FILES=$(shell find src -name \*.hs) $(shell find app -name \*.hs)
FORT_FILES=$(wildcard $(TEST_DIR)/*.fort)
GEN_FILE_NAMES=$(FORT_FILES:$(TEST_DIR)/%.fort=%)
GEN_HS_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.hs)
GEN_LL_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.ll)
GEN_S_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.s)
GEN_O_FILES=$(GEN_FILE_NAMES:%=$(GEN_PATH)/%.fort.o)
OUT_FILE=a.out

.PRECIOUS: $(GEN_HS_FILES) $(GEN_LL_FILES) $(GEN_S_FILES) $(GEN_O_FILES)

.PHONY: all
all: coverage run

$(DIRS):
	mkdir -p $@

.PHONY: run
run: $(OUT_FILE)
	./$<

$(GEN_PATH)/%.fort.hs: test/%.fort $(HS_FILES) | $(GEN_PATH)
	stack runghc -- -isrc app/Main.hs $<

$(GEN_PATH)/%.fort.ll: $(GEN_PATH)/%.fort.hs $(HS_FILES) | $(GEN_PATH)
	stack runghc -- -isrc $<

$(GEN_PATH)/%.fort.s: $(GEN_PATH)/%.fort.ll | $(GEN_PATH)
	llc $^

$(GEN_PATH)/%.fort.o: $(GEN_PATH)/%.fort.s | $(GEN_PATH)
	clang -o $@ -c $^

$(OUT_FILE): main.c $(GEN_O_FILES)
	clang -lc $^

.PHONY: coverage
coverage: $(HS_FILES)
	stack test --coverage

.PHONY: clean
clean:
	stack clean
	rm -f a.out
	rm -f $(GEN_PATH)/*.*
