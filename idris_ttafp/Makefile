.PHONY: build
build: build_Shared build_ch1 build_ch2
	idris --build main.ipkg

.PHONY: build_Shared
build_Shared:
	cd Shared && \
		idris --build shared.ipkg && \
		idris --install shared.ipkg

.PHONY: build_ch1
build_ch1:
	cd ch1 && \
		idris --build ch1.ipkg && \
		idris --install ch1.ipkg

.PHONY: build_ch2
build_ch2:
	cd ch2 && \
		idris --build ch2.ipkg && \
		idris --install ch2.ipkg


.PHONY: test
test: test_Shared test_ch1 test_ch2
	idris --checkpkg main.ipkg
	idris --testpkg main.ipkg

.PHONY: test_Shared
test_Shared:
	cd Shared && \
		idris --checkpkg shared.ipkg && \
		idris --testpkg shared.ipkg && \
		idris --install shared.ipkg

.PHONY: test_ch1
test_ch1:
	cd ch1 && \
		idris --checkpkg ch1.ipkg && \
		idris --testpkg ch1.ipkg && \
		idris --install ch1.ipkg

.PHONY: test_ch2
test_ch2:
	cd ch2 && \
		idris --checkpkg ch2.ipkg && \
		idris --testpkg ch2.ipkg && \
		idris --install ch2.ipkg



.PHONY: clean
clean: clean_Shared clean_ch1 clean_ch2
	idris --clean main.ipkg

.PHONY: clean_Shared
clean_Shared:
	cd Shared && \
		idris --clean shared.ipkg

.PHONY: clean_ch1
clean_ch1:
	cd ch1 && \
		idris --clean ch1.ipkg

.PHONY: clean_ch2
clean_ch2:
	cd ch2 && \
		idris --clean ch2.ipkg

.PHONY: run
run:	build
	./repl
