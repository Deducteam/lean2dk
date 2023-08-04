# Variables
DKCHECK      ?= dk check
DKDEP        ?= dk dep
SRC_FOLDER = .
TEST_FOLDER = ./tests
DKS = $(wildcard $(SRC_FOLDER)/*.dk)
DKS_TEST = $(DKS) $(wildcard $(TEST_FOLDER)/*.dk)
DKOS = $(DKS:.dk=.dko)
DKOS_TEST = $(DKS) $(DKS_TEST:.dk=.dko)


.PHONY: all check clean

all: check

# Generate the dependencies of [.dk] files
depend:
	$(DKDEP) $(SRC_FOLDER)/*.dk > .depend

# Make sure .depend is generated then do the actual check
check: depend
	make actual_check

test: depend
	make actual_test

# Check and compile the generated [.dk]
actual_check: $(DKOS)

actual_test: $(DKOS) $(DKOS_TEST)

%.dko: %.dk
	$(DKCHECK) --eta -e $<

clean:
	rm -f $(SRC_FOLDER)/*.dko
	rm -f $(TEST_FOLDER)/*.dko
	rm -f .depend
	rm -f *.dko

-include .depend
