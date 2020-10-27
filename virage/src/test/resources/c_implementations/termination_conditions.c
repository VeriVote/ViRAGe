#include <stdbool.h>

#include "types.h"
#include "set.h"

bool defer_eq_condition(result r, int n) {
  return (r.deferred.size == n);
}
