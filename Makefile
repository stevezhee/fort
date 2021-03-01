
.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

TEST_DIR=test
HS_FILES=$(shell find src -name \*.hs) $(shell find app -name \*.hs)
LLC=llc-9
OPT=opt-9
OPTLVL=-O3

ALL_FORT_FILES=$(wildcard $(TEST_DIR)/*.fort)

# EXCLUDE_FILES += $(TEST_DIR)/empty.fort
# EXCLUDE_FILES += $(TEST_DIR)/helloworld.fort
# EXCLUDE_FILES += $(TEST_DIR)/address.fort
# EXCLUDE_FILES += $(TEST_DIR)/powi.fort
# EXCLUDE_FILES += $(TEST_DIR)/array.fort
# EXCLUDE_FILES += $(TEST_DIR)/char.fort
# EXCLUDE_FILES += $(TEST_DIR)/nestedif.fort
# EXCLUDE_FILES += $(TEST_DIR)/struct.fort
# EXCLUDE_FILES += $(TEST_DIR)/primitives.fort
# EXCLUDE_FILES += $(TEST_DIR)/enum.fort
# EXCLUDE_FILES += $(TEST_DIR)/todd.fort
# EXCLUDE_FILES += $(TEST_DIR)/fannkuch-redux.fort
# EXCLUDE_FILES += $(TEST_DIR)/floating.fort
EXCLUDE_FILES += $(TEST_DIR)/mandelbrot.fort
EXCLUDE_FILES += $(TEST_DIR)/n-body.fort

FORT_FILES=$(filter-out $(EXCLUDE_FILES), $(ALL_FORT_FILES))
# FORT_FILES=$(TEST_DIR)/powi.fort
# FORT_FILES=$(TEST_DIR)/address.fort
# FORT_FILES=$(TEST_DIR)/fannkuch-redux.fort
# FORT_FILES=$(TEST_DIR)/floating.fort

GEN_HS_FILES=$(addsuffix .hs, $(FORT_FILES))
LL_FILES=$(addsuffix .ll, $(FORT_FILES))
O_FILES=$(addsuffix .o, $(FORT_FILES))
OUT_FILE=a.out

#all: a.out.actual
	# $(OPT) -O0 --dot-cfg test/fannkuch-redux.fort.ll
	# dot .obf.dot -Tpng > t.png

.PHONY: all
all: struct.fort.exe # n-body.fort.exe mandelbrot.fort.exe a.out.actual # mandelbrot.fort.pbm mandelbrot.c.pbm # diff

mandelbrot.%.pbm: mandelbrot.%.exe
	./$< > $@

%.c.exe: %.c
	clang $(OPTLVL) -o $@ $<

$(TEST_DIR)/%.fort.exe: main.c $(TEST_DIR)/%.fort.o
	clang $(OPTLVL) -lc $^ -o $@

.PHONY: diff
diff: a.out.actual
	diff $< a.out.expected

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
	$(OPT) -S $(OPTLVL) -o $< $<
	$(LLC) $<

%.fort.o: %.fort.s
	clang $(OPTLVL) -o $@ -c $^

$(OUT_FILE): main.c $(O_FILES)
	clang $(OPTLVL) -lc $^

.PHONY: coverage
coverage: $(HS_FILES) test/Spec.hs
	stack test --coverage

.PHONY: clean
clean:
	stack clean
	rm -f a.out
	rm -f *.actual
	rm -f test/*.ll
	rm -f test/*.s
	rm -f test/*.o
	rm -f test/*.fort.hs
	rm -f *.exe
	rm -f test/*.exe
	rm -f *.pbm
	rm -f test/*.pbm
	rm -f test/*.ssa
	rm -f test/*.dot
