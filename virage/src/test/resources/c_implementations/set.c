#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "set.h"

set instantiate(int contents[], int size) {
  set res;

  res.contents = contents;
  res.size = size;

  return res;
}

set emptySet() {
  set result;

  result.size = 0;

  return result;
}

set unify(set a, set b) {
  printSet(a);
  printSet(b);

  int potentialSize = a.size + b.size;
  int* elements = malloc(potentialSize);
  int distinctElements = 0;

  for(int i=0; i<a.size; i++) {
    elements[i] = a.contents[i];
    distinctElements++;
  }

  for(int j=0; j<b.size; j++) {
    int current = b.contents[j];

    bool found = false;
    for(int k=0; k<a.size; k++) {
      if(a.contents[k] == current) {
        found = true;
        break;
      }
    }

    if(!found) {
      elements[distinctElements] = current;
      distinctElements++;
    }
  }

  set result;

  result.contents = elements;
  result.size = distinctElements;

  return result;
}

bool contains(set s, int e) {
  for(int i=0; i<s.size; i++) {
    if(s.contents[i] == e) return true;
  }

  return false;
}

set setMinus(set a, set b) {
  int* resContents = malloc(a.size);
  int removedElements = 0;
  int next = 0;

  for(int i=0; i<a.size; i++) {
    if(contains(b, a.contents[i])) {
      removedElements++;
    } else {
      resContents[next] = a.contents[i];
      next++;
    }
  }

  set res;
  res.contents = resContents;
  res.size = next;

  return res;
}

void printSet(set s) {
  printf("size: %d; { ", s.size);
  for(int i=0; i<s.size; i++) {
    printf("%d ", s.contents[i]);
  }
  printf("}\n");
}
