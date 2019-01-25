TEST_DIR=test
GEN_DIR=generated
GEN_PATH=$(GEN_DIR)/$(TEST_DIR)
TEST_FILES=$(wildcard $(TEST_DIR)/*.fort)
LL_TEST_FILES=$(addprefix $(GEN_DIR)/, $(addsuffix .ll, $(TEST_FILES)))
S_TEST_FILES=$(addsuffix .s, $(basename $(LL_TEST_FILES)))
O_TEST_FILES=$(addsuffix .o, $(basename $(LL_TEST_FILES)))
HS_FILES=$(wildcard src/**/*.hs) $(wildcard app/**/*.hs)
OUT_FILE=a.out


.PRECIOUS: $(GEN_PATH)/%.fort.hs $(GEN_PATH)/%.fort.ll $(GEN_PATH)/%.fort.s

.PHONY: all
all: coverage run

DIRS = $(TEST_DIR) $(GEN_DIR) $(GEN_PATH)
$(DIRS):
	mkdir -p $@

.PHONY: run
run: $(OUT_FILE) $(HS_FILES)
	./$<

$(GEN_PATH)/%.fort.hs: test/%.fort $(HS_FILES) | $(GEN_PATH)
	stack runghc -- -isrc app/Main.hs $<

$(GEN_PATH)/%.fort.ll: $(GEN_PATH)/%.fort.hs $(HS_FILES) | $(GEN_PATH)
	stack runghc -- -isrc $<

$(GEN_PATH)/%.fort.s: $(GEN_PATH)/%.fort.ll | $(GEN_PATH)
	llc $^

$(GEN_PATH)/%.fort.o: $(GEN_PATH)/%.fort.s | $(GEN_PATH)
	clang -o $@ -c $^

$(OUT_FILE): main.c $(O_TEST_FILES)
	clang $^

.PHONY: coverage
coverage: $(HS_FILES)
	stack test --coverage

.PHONY: clean
clean:
	stack clean
	rm -f a.out
	rm -f $(GEN_PATH)/*.*
