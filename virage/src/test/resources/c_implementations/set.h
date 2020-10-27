#ifndef SET_H
#define SET_H

#include <stdbool.h>

typedef struct {
  int size;
  int* contents;
} set;

set instantiate(int* contents, int size);
set emptySet();
set unify(set a, set b);
bool contains(set s, int e);
set setMinus(set a, set b);
void printSet(set s);

#endif //SET_H
