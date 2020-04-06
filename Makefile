all: prog

prog: inductive_vars/src/main.cpp
	$(MAKE) -C qbe
	g++ -I. --std=c++17 inductive_vars/src/main.cpp qbe/obj/*.o qbe/obj/arm64/*.o qbe/obj/amd64/*.o -o prog

test: prog
	./prog < test/test001.il
	@echo "\n\n"
	./prog < test/test002.il
	@echo "\n\n"
	./prog < test/test003.il
