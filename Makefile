CC=g++
CC_FLAGS=--std=c++17

all: prog

prog: inductive_vars/src/main.cpp
	$(MAKE) -C qbe
	$(CC) $(CC_FLAGS) -I. inductive_vars/src/main.cpp qbe/obj/*.o qbe/obj/arm64/*.o qbe/obj/amd64/*.o -o prog

runtest:
	@$(CC) $(CC_FLAGS) test/test.cpp -o runtest

test: runtest prog
	@mkdir -p tmp
	@./prog < test/test_cases/test001.il > tmp/answer001.il
	./runtest tmp/answer001.il test/test_cases/answer001.txt
	@./prog < test/test_cases/test002.il > tmp/answer002.il
	./runtest tmp/answer002.il test/test_cases/answer002.txt
	@./prog < test/test_cases/test003.il > tmp/answer003.il
	./runtest tmp/answer003.il test/test_cases/answer003.txt

clean:
	rm -rf tmp runtest prog
	$(MAKE) clean -C qbe