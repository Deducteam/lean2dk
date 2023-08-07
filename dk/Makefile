# Variables
DKCHECK      ?= dk check
DKDEP        ?= dk dep
SRC_FOLDER = .
TEST_FOLDER = ./tests
DKS = $(filter-out $(SRC_FOLDER)/out.dk, $(wildcard $(SRC_FOLDER)/*.dk))
DK_OUT = out.dk
DKOS = $(DKS:.dk=.dko)
DKO_OUT = out.dko


.PHONY: all check clean

all: check

# Generate the dependencies of [.dk] files
depend:
	$(DKDEP) $(SRC_FOLDER)/*.dk > .depend

# Make sure .depend is generated then do the actual check
check: depend
	make actual_check

test:
	make -C $(TEST_FOLDER) check

# Check and compile the generated [.dk]
actual_check: $(DKOS) $(DKO_OUT)

%.dko: %.dk
	$(DKCHECK) --eta -e $<

clean:
	rm -f $(SRC_FOLDER)/*.dko
	rm -f .depend
	make -C $(TEST_FOLDER) clean

-include .depend
