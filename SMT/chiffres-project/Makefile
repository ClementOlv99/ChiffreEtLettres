# Le chemin vers Z3 est positionné vers un répertoire partagé.
# Vous pouvez modifier cette variable d'environnement si vous
# avez installé Z3 sur votre compte ou sur votre machine
# personnelle.
PATH_TO_Z3 = /mnt/n7fs/ens/tp_dupont/z3/bin

JAVAC = javac
JAVA = java
CP_OPTS = -cp $$CLASSPATH:$(PATH_TO_Z3)/com.microsoft.z3.jar
JAVAC_OPTS = $(CP_OPTS) -d classes
JAVA_OPTS = -Djava.library.path=$(PATH_TO_Z3) $(CP_OPTS):./classes
SRC_DIR = src/fr/n7/smt

_SRC_FILES = Z3Utils.java BMC.java TransitionSystem.java \
	ChiffresCache.java ChiffresTransitionSystem.java \
	MainUtils.java MainOneAction.java MainSimpleProblem.java \
	MainSimpleProblemNo.java MainSimpleProblemOverflows.java \
	MainTextProblem.java MainComplexProblems.java \
	MainComplexProblemApproximate.java

SRC_FILES = $(patsubst %,$(SRC_DIR)/%,$(_SRC_FILES))

.PHONY: compile run-one-action run-simple-problem run-simple-problem-no \
	run-simple-problem-overflows run-text run-complex run-approximate

compile: $(SRC_FILES) | classes
	$(JAVAC) $(JAVAC_OPTS) $^

run-one-action: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainOneAction

run-simple-problem: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainSimpleProblem

run-simple-problem-no: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainSimpleProblemNo

run-simple-problem-overflows: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainSimpleProblemOverflows

run-text: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainTextProblem

run-complex: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainComplexProblems

run-approximate: compile
	LD_LIBRARY_PATH=$(PATH_TO_Z3):$$LD_LIBRARY_PATH $(JAVA) -ea $(JAVA_OPTS) fr.n7.smt.MainComplexProblemApproximate

classes:
	mkdir -p $@

clean:
	- rm -rf classes *.log **/*~

run-all: run-one-action run-simple-problem run-simple-problem-no \
		run-simple-problem-overflows run-text run-complex 
