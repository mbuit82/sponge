all: datalog-engines proof-processing

datalog-engines: ToDatalog/Engines.hs ToDatalog/Utils.hs $(wildcard Defs/*.hs) Core.hs
	@ mkdir -p exec
	@ ghc ToDatalog/Engines.hs -main-is ToDatalog.Engines.main -o exec/build-engines -outputdir build
	@ ghc Commands/ShowLogic.hs -main-is Commands.ShowLogic.main -o exec/show-logic -outputdir build
	@ ghc Commands/SearchForTheorem.hs -main-is Commands.SearchForTheorem.main -o exec/search-theorem -outputdir build
	@ ./exec/build-engines

proof-processing: ToDatalog/UserProofs.hs ToDatalog/Utils.hs $(wildcard DerivedRules/*.hs) $(wildcard Defs/*.hs) Core.hs
	@ ghc ToDatalog/UserProofs.hs -main-is ToDatalog.UserProofs.main -o exec/build-proof -outputdir build
	@ ghc Commands/CheckDatalogOutput.hs -main-is Commands.CheckDatalogOutput.main -o exec/check-datalog-output -outputdir build

check-proof: 
	@ ./exec/build-proof $(LOGIC) $(PROOF)
	@ souffle -D datalog/datalog_proofs/$(LOGIC)/$(PROOF) datalog/datalog_proofs/$(LOGIC)/$(PROOF)/$(PROOF).dl
	@ ./exec/check-datalog-output $(LOGIC) $(PROOF)


PROOF_FILES := $(wildcard user_proofs/$(LOGIC)/*.txt)
PROOF_NAMES := $(basename $(notdir $(PROOF_FILES)))

run-souffle-for-logic:
	@for pnm in $(PROOF_NAMES); do \
		souffle -D datalog/datalog_proofs/$(LOGIC)/$$pnm datalog/datalog_proofs/$(LOGIC)/$$pnm/$$pnm.dl || exit 1; \
	done

check-logic:
	@ ./exec/build-proof $(LOGIC)
	@ echo Checking all proofs in $(LOGIC)...
	@ make run-souffle-for-logic LOGIC=$(LOGIC)
	@ ./exec/check-datalog-output $(LOGIC)

LOGIC_NAMES:= $(wildcard user_proofs/$(LOGIC)/*.txt)

LOGIC_DIRS := $(wildcard user_proofs/*/)
LOGICS := $(notdir $(patsubst %/,%,$(LOGIC_DIRS)))

check-all:
	@for lnm in $(LOGICS); do \
		make check-logic LOGIC=$$lnm; \
	done

show-logic: 
	@ ./exec/show-logic $(LOGIC)

clean:
	@ rm -rf build exec datalog/datalog_proofs/*

.PHONY: all clean datalog-engines proof-processing check-proof show-logic search-theorem run-souffle-for-logic check-logic check-all