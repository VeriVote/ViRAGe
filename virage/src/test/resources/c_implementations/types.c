#include <stdio.h>
#include <stdlib.h>

#include "set.h"
#include "types.h"

rel limitTo(set a, rel r) {
  int newSize = a.size;
  int* newRel = malloc(newSize);
  int next = 0;

  for(int i=0; i<r.size; i++) {
    if(contains(a,r.elements[i])) {
      newRel[next] = r.elements[i];
      next++;
    }
  }

  rel result;

  result.elements = newRel;
  result.size = newSize;

  return result;
}

profile limitProfile(set a, profile p) {
  for(int i=0; i<p.voteCount; i++) {
    p.votes[i] = limitTo(a, p.votes[i]);
  }
  p.alternatives = a;

  return p;
}

void printResult(result r) {
  printf("elected: "); printSet(r.elected);
  printf("rejected: "); printSet(r.rejected);
  printf("deferred: "); printSet(r.deferred);
}
