all: prog

prog: main.cpp
	$(MAKE) -C qbe
	g++ -I. --std=c++17 main.cpp qbe/obj/*.o qbe/obj/arm64/*.o qbe/obj/amd64/*.o -o prog

test: prog
	./prog < test/test1.ssa
