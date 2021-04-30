
.SUFFIXES:
.PRECIOUS: %.fort.hs %.fort.ll %.fort.s %.fort.o

TEST_DIR=test
HS_FILES=$(shell find src -name \*.hs) $(shell find app -name \*.hs)
LLC=llc-9
OPT=opt-9
OPTLVL=-O2

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
# EXCLUDE_FILES += $(TEST_DIR)/mandelbrot.fort
# EXCLUDE_FILES += $(TEST_DIR)/n-body.fort

FORT_FILES=$(filter-out $(EXCLUDE_FILES), $(ALL_FORT_FILES))
# FORT_FILES=$(TEST_DIR)/nestedif.fort
# FORT_FILES=$(TEST_DIR)/char.fort
# FORT_FILES=$(TEST_DIR)/powi.fort
# FORT_FILES=$(TEST_DIR)/address.fort
# FORT_FILES=$(TEST_DIR)/fannkuch-redux.fort
# FORT_FILES=$(TEST_DIR)/floating.fort
# FORT_FILES=$(TEST_DIR)/mandelbrot.fort
# FORT_FILES=$(TEST_DIR)/n-body.fort
# FORT_FILES=$(TEST_DIR)/spectral-norm.fort
# FORT_FILES=$(TEST_DIR)/fasta.fort

GEN_HS_FILES=$(addsuffix .hs, $(FORT_FILES))
LL_FILES=$(addsuffix .ll, $(FORT_FILES))
O_FILES=$(addsuffix .o, $(FORT_FILES))
OUT_FILE=a.out

NO_MAIN=$(TEST_DIR)/empty.fort $(TEST_DIR)/todd.fort

EXES=$(addsuffix .exe, $(filter-out $(NO_MAIN), $(FORT_FILES)))

.PHONY: all n-body spectral-norm fasta fannkuch-redux mandelbrot

# all: test/poly.fort.exe
all: mandelbrot fannkuch-redux fasta n-body spectral-norm $(O_FILES) $(EXES)

mandelbrot: mandelbrot.exe $(TEST_DIR)/mandelbrot.fort.exe
	./mandelbrot.exe > t.pbm
	./$(TEST_DIR)/mandelbrot.fort.exe > tt.pbm
	diff t.pbm tt.pbm

fannkuch-redux: $(TEST_DIR)/fannkuch-redux.fort.exe fannkuch-redux.exe
	./fannkuch-redux.exe > t.txt
	./$(TEST_DIR)/fannkuch-redux.fort.exe > tt.txt
	diff t.txt tt.txt

fasta: $(TEST_DIR)/fasta.fort.exe fasta.exe
	./fasta.exe > t.txt
	./$(TEST_DIR)/fasta.fort.exe > tt.txt
	diff t.txt tt.txt

spectral-norm: $(TEST_DIR)/spectral-norm.fort.exe spectral-norm.exe
	./spectral-norm.exe | tee t.txt
	./$(TEST_DIR)/spectral-norm.fort.exe | tee tt.txt
	diff t.txt tt.txt

n-body: $(TEST_DIR)/n-body.fort.exe n-body.exe
	./n-body.exe | tee t.txt
	./$(TEST_DIR)/n-body.fort.exe | tee tt.txt
	diff t.txt tt.txt

%.exe: %.c
	clang $(OPTLVL) -o $@ $<

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
	#$(OPT) -S $(OPTLVL) -o $< $<
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
