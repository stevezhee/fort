.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

TEST_DIR=test
HS_FILES=$(shell find src -name \*.hs) $(shell find app -name \*.hs)

FORT_FILES=$(wildcard $(TEST_DIR)/*.fort)
# FORT_FILES=test/address.fort
# FORT_FILES=test/array.fort
# FORT_FILES=test/char.fort
# FORT_FILES=test/primitives.fort
# FORT_FILES=test/powi.fort
# FORT_FILES=test/struct.fort
# FORT_FILES=test/todd.fort
# FORT_FILES=test/fannkuch-redux.fort
# FORT_FILES=test/nestedif.fort
# FORT_FILES=test/enum.fort

GEN_HS_FILES=$(addsuffix .hs, $(FORT_FILES))
LL_FILES=$(addsuffix .ll, $(FORT_FILES))
O_FILES=$(addsuffix .o, $(FORT_FILES))
OUT_FILE=a.out

.PHONY: all
all: diff

.PHONY: diff
diff: a.out.actual
	diff a.out.expected $<

.PHONY: pretty
pretty: $(HS_FILES)
	floskell -s cramer $^

a.out.actual: $(OUT_FILE)
	./$< | tee ./a.out.actual

%.fort.hs: %.fort $(HS_FILES)
	stack runghc -- -Wall -isrc app/Main.hs $<

%.fort.ll: %.fort.hs
	stack runghc -- -Wall -isrc $<

%.fort.s: %.fort.ll
	llc $<

%.fort.o: %.fort.s
	clang -o $@ -c $^

$(OUT_FILE): main.c $(O_FILES)
	clang -lc $^

.PHONY: coverage
coverage: $(HS_FILES) test/Spec.hs
	stack test --coverage

.PHONY: clean
clean:
	stack clean
	rm -f a.out
	rm -f test/*.ll
	rm -f test/*.s
	rm -f test/*.o
	rm -f test/*.fort.hs
