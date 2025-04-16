# Variables
DKCHECK      ?= dk check
DKDEP        ?= dk dep
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
