# Variables
DKCHECK      ?= dk check
DKDEP        ?= dk dep
SRC_FOLDER = ..
TEST_FOLDER = .
DKS = $(filter-out $(SRC_FOLDER)/out.dk, $(wildcard $(SRC_FOLDER)/*.dk))
DKS_TEST = $(wildcard $(TEST_FOLDER)/*.dk)
DKOS = $(DKS:.dk=.dko)
DKOS_TEST = $(DKS_TEST:.dk=.dko)

.PHONY: all check clean

all: check

# Generate the dependencies of [.dk] files
depend:
	$(DKDEP) -I $(SRC_FOLDER) $(DKS) $(DKS_TEST) > .depend

# Make sure .depend is generated then do the actual check
check: depend
	make actual_check

# Check and compile the generated [.dk]
actual_check: $(DKOS) $(DKOS_TEST)

%.dko: %.dk
	$(DKCHECK) -I $(SRC_FOLDER) --eta -e $<

clean:
	rm -f $(TEST_FOLDER)/*.dko
	rm -f .depend

-include .depend
