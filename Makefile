agda = agda
dev_shell = fish

ENV_VARS ?= AGDA_DIR="`pwd`"
IN_ENV = env ${ENV_VARS}


default : src

src/*.agda :
	@$(IN_ENV) $(agda) -i src $@

.PHONY: src
src : src/*.agda
	for e in $^; do \
	  $(IN_ENV) $(agda) -i src $$e ;\
	done

.PHONY: shell
shell :
	@echo "Entering development shell ($(dev_shell))"
	@$(IN_ENV) $(dev_shell)
