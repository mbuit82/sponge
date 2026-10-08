all: datalog-engines proof-processing

datalog-engines: ToDatalog/Engines.hs ToDatalog/Utils.hs Proofs.hs Specs.hs Core.hs
	@ mkdir -p exec
	@ ghc ToDatalog/Engines.hs -main-is ToDatalog.Engines.main -o exec/build-engines -outputdir build
	@ ./exec/build-engines

proof-processing: ToDatalog/UserProofs.hs datalog-engines
	@ ghc ToDatalog/UserProofs.hs -main-is ToDatalog.UserProofs.main -o exec/build-proof -outputdir build
	@ ghc CheckDatalogOutput.hs -main-is CheckDatalogOutput.main -o exec/check-datalog-output -outputdir build

check-proof:
	@ ./exec/build-proof $(LOGIC) $(PROOF)
	@ souffle -D datalog_proofs/$(LOGIC)/$(PROOF) datalog_proofs/$(LOGIC)/$(PROOF)/$(PROOF).dl
	@ ./exec/check-datalog-output $(LOGIC) $(PROOF)

clean:
	@ rm -rf build exec

.PHONY: all clean datalog-engines proof-processing check-proof