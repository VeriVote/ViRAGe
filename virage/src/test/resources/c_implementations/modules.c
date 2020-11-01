#include <stdlib.h>

#include "types.h"

result elect_module(profile p, result r) {
  for(int i=0; i<C; i++) {
    if(r.values[i] == DEFERRED) {
      r.values[i] = ELECTED;
    }
  }

  return r;
}

result pass_module(int n, rel relation, profile p, result r) {
  for(int i=0; i<C; i++) {
    int current_alternative = relation.elements[i];
    int idx = find_index(p, current_alternative);

    if(r.values[idx] == DEFERRED) {
      if(n>0) {
        r.values[idx] = DEFERRED;
        n--;
      } else {
        r.values[idx] = REJECTED;
      }
    }
  }

  return r;
}

result drop_module(int n, rel relation, profile p, result r) {
  for(int i=0; i<C; i++) {
    int current_alternative = relation.elements[i];
    int idx = find_index(p, current_alternative);

    if(r.values[idx] == DEFERRED) {
      if(n>0) {
        r.values[idx] = REJECTED;
        n--;
      } else {
        r.values[idx] = DEFERRED;
      }
    }
  }

  return r;
}

result plurality_module(profile p, result r) {
  int wins[C];
  for(int i=0; i<C; i++) {
    wins[i] = 0;
  }

  for(int v=0; v<V; v++) {
    for(int c=0; c<C; c++) {
      int current_alternative = p.votes[c][v];
      int idx = find_index(p, current_alternative);

      if(r.values[idx] == DEFERRED) {
        wins[idx]++;
        break;
      }
    }
  }

  int max = 0;
  for(int i=0; i<C; i++) {
    if(wins[i] > max) max = wins[i];
  }

  for(int i=0; i<C; i++) {
    if(r.values[i] == DEFERRED) {
      if(wins[i] == max) {
        r.values[i] = ELECTED;
      } else {
        r.values[i] = REJECTED;
      }
    }
  }

  return r;
}
