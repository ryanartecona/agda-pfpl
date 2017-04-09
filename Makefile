AGDA = agda

default: src

.PHONY: src/*.agda
src/*.agda:
	$(AGDA) -i src $@

.PHONY: src
src : src/*.agda
