all: prog

prog: main.c
	$(MAKE) -C qbe
	gcc -I. main.c qbe/obj/*.o qbe/obj/arm64/*.o qbe/obj/amd64/*.o -o prog

test: prog
	./prog < test/test1.ssa
