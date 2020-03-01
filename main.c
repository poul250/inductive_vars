#include <qbe/all.h>

#include <stdio.h>

static void readfn (Fn *fn) {
  for (Blk *blk = fn->start; blk; blk = blk->link) {
    printf("da");
  }
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main (int argc, char ** argv) {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
