#include "types.h"

result max_aggregator(result a, result b) {
  result new_result;

  for(int i=0; i<C; i++) {
    if(a.values[i] == ELECTED || b.values[i] == ELECTED) {
      new_result.values[i] = ELECTED;
    } else if(a.values[i] == DEFERRED || b.values[i] == DEFERRED) {
      new_result.values[i] = DEFERRED;
    } else {
      new_result.values[i] = REJECTED;
    }
  }

  return new_result;
}
