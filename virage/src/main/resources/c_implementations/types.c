#include "types.h"

int find_index(profile p, int alternative) {
  return alternative;
}

result rescpy(result to_be_copied) {
  result to_return;

  for(int i=0; i<C; i++) {
    to_return.values[i] = to_be_copied.values[i];
  }

  return to_return;
}

rel get_default_ordering(profile p) {
  rel r;

  for(int i=0; i<C; i++) {
     r.elements[i] = p.votes[0][i];
  }

  return r;
}
