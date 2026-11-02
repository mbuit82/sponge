all: basics proof-processing

exec/build-engines: ToDatalog/Engines.hs ToDatalog/Utils.hs $(wildcard Defs/*.hs) Core.hs
	@ ghc ToDatalog/Engines.hs -main-is ToDatalog.Engines.main -o exec/build-engines -outputdir build

exec/show-logic: Core.hs Defs/Specs.hs Commands/ShowLogic.hs
	@ ghc Commands/ShowLogic.hs -main-is Commands.ShowLogic.main -o exec/show-logic -outputdir build

exec/search-theorem: Core.hs Parse/Sentences.hs Defs/Specs.hs Commands/SearchForTheorem.hs
	@ ghc Commands/SearchForTheorem.hs -main-is Commands.SearchForTheorem.main -o exec/search-theorem -outputdir build

basics_: exec/build-engines exec/show-logic exec/search-theorem
	@ ./exec/build-engines

basics: 
	@ mkdir -p exec
	@ make basics_
	


exec/build-proof: ToDatalog/UserProofs.hs ToDatalog/Utils.hs $(wildcard DerivedRules/*.hs) $(wildcard Defs/*.hs) Core.hs
	@ ghc ToDatalog/UserProofs.hs -main-is ToDatalog.UserProofs.main -o exec/build-proof -outputdir build

exec/check-datalog-output: ToDatalog/Utils.hs  Commands/CheckDatalogOutput.hs
	@ ghc Commands/CheckDatalogOutput.hs -main-is Commands.CheckDatalogOutput.main -o exec/check-datalog-output -outputdir build

proof-processing: exec/build-proof exec/check-datalog-output

check-proof: exec/build-proof
	@ ./exec/build-proof $(LOGIC) $(PROOF)
	@ souffle -D datalog/datalog_proofs/$(LOGIC)/$(PROOF) datalog/datalog_proofs/$(LOGIC)/$(PROOF)/$(PROOF).dl
	@ ./exec/check-datalog-output $(LOGIC) $(PROOF)


PROOF_FILES := $(wildcard user_proofs/$(LOGIC)/*.txt)
PROOF_NAMES := $(basename $(notdir $(PROOF_FILES)))

check-logic: exec/build-proof
	@ ./exec/build-proof $(LOGIC)
	@ echo Checking all proofs in $(LOGIC)...
	@ for pnm in $(PROOF_NAMES); do \
		souffle -D datalog/datalog_proofs/$(LOGIC)/$$pnm datalog/datalog_proofs/$(LOGIC)/$$pnm/$$pnm.dl || exit 1; \
	done
	@ ./exec/check-datalog-output $(LOGIC)

LOGIC_NAMES:= $(wildcard user_proofs/$(LOGIC)/*.txt)

LOGIC_DIRS := $(wildcard user_proofs/*/)
LOGICS := $(notdir $(patsubst %/,%,$(LOGIC_DIRS)))

check-all: exec/build-proof
	@ for lnm in $(LOGICS); do \
		make check-logic LOGIC=$$lnm; \
	done

show-logic: exec/show-logic
	@ ./exec/show-logic $(LOGIC)

search-theorem: exec/search-theorem
	@ ./exec/search-theorem

clean:
	@ rm -rf build exec datalog/datalog_proofs/*

.PHONY: all clean basics_ basics proof-processing check-proof check-logic check-all show-logic search-theorem