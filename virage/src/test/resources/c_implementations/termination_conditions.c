#include <stdbool.h>

#include "types.h"

bool defer_eq_condition(int n, profile p, result r) {
  int ctr = 0;

  for(int i=0; i<C; i++) {
    if(r.values[i] == DEFERRED) ctr++;
  }

  return (ctr == n);
}
