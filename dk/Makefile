# Variables
DKCHECK      ?= dk check
LPCHECK      ?= lambdapi check -c
LPEXP        ?= lambdapi export
DKDEP        ?= dk dep
SRC_FOLDER = .
TEST_FOLDER = ./tests
DKS = $(filter-out $(SRC_FOLDER)/out.dk, $(wildcard $(SRC_FOLDER)/*.dk))
DK_OUT = out.dk
DKOS = $(DKS:.dk=.dko)
DKO_OUT = out.dko
LP_PKG = lambdapi.pkg
LPS = $(DKS:.dk=.lp)
LPOS = $(LPS:.lp=.lpo)
LPO_OUT = out.lpo


.PHONY: all check clean

all: check

# Generate the dependencies of [.dk] files
depend:
	$(DKDEP) $(SRC_FOLDER)/*.dk > .depend

# Make sure .depend is generated then do the actual check
check: depend
	make actual_check

lp_check:
	make lp_actual_check

test:
	make -C $(TEST_FOLDER) check

# Check and compile the generated [.dk]
actual_check: $(DKOS) $(DKO_OUT)

lp_actual_check: $(LPOS) $(LPO_OUT)

%.dko: %.dk
	$(DKCHECK) --eta -e $<

%.lp: %.dk $(LP_PKG)
	$(LPEXP) $< > $@

%.lpo: %.lp
	$(LPCHECK) $<

clean:
	rm -f $(SRC_FOLDER)/*.dko
	rm -f .depend
	make -C $(TEST_FOLDER) clean

-include .depend
