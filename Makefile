all: datalog-engines proof-processing

datalog-engines: ToDatalog/Engines.hs ToDatalog/Utils.hs Defs/Specs.hs Core.hs
	@ mkdir -p exec
	@ ghc ToDatalog/Engines.hs -main-is ToDatalog.Engines.main -o exec/build-engines -outputdir build
	@ ghc Commands/ShowLogic.hs -main-is Commands.ShowLogic.main -o exec/show-logic -outputdir build
	@ ghc Commands/SearchForProof.hs -main-is Commands.SearchForProof.main -o exec/search-proof -outputdir build
	@ ./exec/build-engines

proof-processing: ToDatalog/UserProofs.hs ToDatalog/Utils.hs ProofTrees.hs Core.hs
	@ ghc ToDatalog/UserProofs.hs -main-is ToDatalog.UserProofs.main -o exec/build-proof -outputdir build
	@ ghc Commands/CheckDatalogOutput.hs -main-is Commands.CheckDatalogOutput.main -o exec/check-datalog-output -outputdir build

check-proof: 
	@ ./exec/build-proof $(LOGIC) $(PROOF)
	@ souffle -D datalog/datalog_proofs/$(LOGIC)/$(PROOF) datalog/datalog_proofs/$(LOGIC)/$(PROOF)/$(PROOF).dl
	@ ./exec/check-datalog-output $(LOGIC) $(PROOF)

show-logic: 
	@ ./exec/show-logic $(LOGIC)

clean:
	@ rm -rf build exec

.PHONY: all clean datalog-engines proof-processing check-proof show-logic search-proof