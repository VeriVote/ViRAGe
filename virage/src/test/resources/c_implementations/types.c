#include "types.h"

int find_index(profile p, int alternative) {
  for(int i=0; i<C; i++) {
    if(p.alternatives[i] == alternative) {
      return i;
    }
  }

  return -1;
}

rel get_default_ordering(profile p) {
  rel r;

  for(int i=0; i<C; i++) {
     r.elements[i] = p.votes[0][i];
  }

  return r;
}
