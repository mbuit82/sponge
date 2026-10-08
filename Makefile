GHC = ghc

all: datalog-engines proof-processing

datalog-engines: ToDatalog.hs Proofs.hs Specs.hs Core.hs
	mkdir exec
	ghc ToDatalog.hs -main-is ToDatalog.compileDatalogEngines -o exec/build-engines -outputdir build
	./exec/build-engines

proof-processing: datalog-engines
	ghc ToDatalog.hs -main-is ToDatalog.userToDatalog -o exec/build-proof -outputdir build
	ghc CheckDatalogOutput.hs -o exec/check-datalog-output -outputdir build

check-proof:
	@ ./exec/build-proof $(LOGIC) $(PROOF)
	@ souffle -D datalog_proofs/$(LOGIC)/$(PROOF) datalog_proofs/$(LOGIC)/$(PROOF)/$(PROOF).dl
	@ ./exec/check-datalog-output $(LOGIC) $(PROOF)

clean:
	rm -rf build exec

.PHONY: all clean datalog-engines proof-processing check-proof