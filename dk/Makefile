# Variables
# lean2dk's output of Lean well-founded definitions (e.g. Nat.modCore) is only
# checkable by a Dedukti with lazy-delta congruence (DK_LAZY_DELTA): see the
# rish987/Dedukti `lazy-delta-congruence` fork. `DK` must point at such a kernel.
# Override with e.g. `make DK=dk` once that fork is installed on PATH.
DK           ?= $(HOME)/projects/Dedukti/_build/default/commands/main.exe
DKCHECK      ?= $(DK) check
DKDEP        ?= $(DK) dep
export DK_LAZY_DELTA := 1
SRC_FOLDER = .
TEST_FOLDER = ./tests
EDKS = $(wildcard $(SRC_FOLDER)/enc/*.dk)
ODKS = $(wildcard $(SRC_FOLDER)/out/*.dk)
DK_OUT = out.dk
EDKOS = $(EDKS:.dk=.dko)
ODKOS = $(ODKS:.dk=.dko)
DKO_OUT = out.dko


.PHONY: all check clean

all: check

# Generate the dependencies of [.dk] files
depend:
	$(DKDEP) $(SRC_FOLDER)/enc/*.dk $(SRC_FOLDER)/out/*.dk -I enc -I out > .depend

# Make sure .depend is generated then do the actual check
check: depend
	make actual_check

test:
	make -C $(TEST_FOLDER) check

# Check and compile the generated [.dk]
actual_check: $(EDKOS) $(ODKOS)

%.dko: %.dk
	$(DKCHECK) -I enc -I out --eta -e $<

clean:
	rm -f $(SRC_FOLDER)/enc/*.dko
	rm -f $(SRC_FOLDER)/out/*.dko
	rm -f .depend
	make -C $(TEST_FOLDER) clean

-include .depend
