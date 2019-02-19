.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

TEST_DIR=test
HS_FILES=$(shell find src -name \*.hs) $(shell find app -name \*.hs)
FORT_FILES=$(wildcard $(TEST_DIR)/*.fort)
# FORT_FILES=test/powi.fort
# FORT_FILES=test/todd.fort
# FORT_FILES=test/enum.fort
# FORT_FILES=test/array.fort
FORT_FILES=test/fannkuch-redux.fort
# FORT_FILES=test/struct.fort
# FORT_FILES=test/char.fort
# FORT_FILES=test/address.fort test/powi.fort
GEN_HS_FILES=$(addsuffix .hs, $(FORT_FILES))
LL_FILES=$(addsuffix .ll, $(FORT_FILES))
O_FILES=$(addsuffix .o, $(FORT_FILES))
OUT_FILE=a.out

.PHONY: all
all: $(O_FILES)

.PHONY: run
run: $(OUT_FILE)
	./$< | tee ./a.out.actual
	diff a.out.expected a.out.actual

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

$(OUT_FILE): main.c $(O_FILES)
	clang -lc $^

.PHONY: coverage
coverage: $(HS_FILES) test/Spec.hs
	stack test --coverage

.PHONY: clean
clean:
	stack clean
	rm -f a.out
	rm test/*.ll
	rm test/*.s
	rm test/*.o
	rm test/*.fort.hs
