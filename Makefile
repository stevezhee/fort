# pow.fort ==> pow.fort.hs
# codegen pow.fort.hs ==> pow.fort.ll
# llc pow.fort.ll ==> pow.fort.s
# gcc/clang pow.fort.s main.c ==> a.out

.PHONY: clean

clean:
	rm -f *.o *.s a.out *.fort.hs *.ll
