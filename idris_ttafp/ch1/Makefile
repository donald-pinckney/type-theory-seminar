.PHONY: build
build:
	idris --build ch1.ipkg

.PHONY: run
run:	build
	./repl

.PHONY: test
test:	clean
	idris --checkpkg ch1.ipkg
	idris --testpkg ch1.ipkg

.PHONY: clean
clean:
	idris --clean ch1.ipkg
