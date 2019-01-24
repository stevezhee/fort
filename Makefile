TEST_DIR=test
GEN_DIR=generated
GEN_PATH=$(GEN_DIR)/$(TEST_DIR)
TEST_FILES=$(wildcard $(TEST_DIR)/*.fort)
LL_TEST_FILES=$(addprefix $(GEN_DIR)/, $(addsuffix .ll, $(TEST_FILES)))
S_TEST_FILES=$(addsuffix .s, $(basename $(LL_TEST_FILES)))
O_TEST_FILES=$(addsuffix .o, $(basename $(LL_TEST_FILES)))

HS_FILES=src/Fort.hs src/LLVM.hs src/Parser.hs app/Main.hs test/Spec.hs

.PHONY: clean all run $(TEST_FILES)

.PRECIOUS: $(GEN_PATH)/%.fort.hs $(GEN_PATH)/%.fort.ll $(GEN_PATH)/%.fort.s

all: coverage $(O_TEST_FILES) run

run: a.out $(HS_FILES)
	./a.out

$(GEN_PATH)/%.fort.hs: test/%.fort $(HS_FILES)
	stack runghc -- -isrc app/Main.hs $<

$(GEN_PATH)/%.fort.ll: $(GEN_PATH)/%.fort.hs $(HS_FILES)
	stack runghc -- -isrc $<

$(GEN_PATH)/%.fort.s: $(GEN_PATH)/%.fort.ll
	llc $^

$(GEN_PATH)/%.fort.o: $(GEN_PATH)/%.fort.s
	clang -o $@ -c $^

a.out: main.c $(GEN_PATH)/powi.fort.o $(GEN_PATH)/address.fort.o $(GEN_PATH)/array.fort.o
	clang $^

coverage: $(HS_FILES)
	stack test --coverage

clean:
	stack clean
	rm -f a.out
	rm -f $(GEN_PATH)/*.*
