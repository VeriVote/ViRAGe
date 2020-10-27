#ifndef TYPES_H
#define TYPES_H

#include "set.h"

typedef struct {
  int size;
  int* elements;
} rel;

typedef struct {
  int voteCount;
  set alternatives;
  rel* votes;
} profile;

typedef struct {
  set elected;
  set rejected;
  set deferred;
} result;

rel limitTo(set a, rel r);
profile limitProfile(set a, profile p);
void printResult(result r);


#endif // TYPES_H
