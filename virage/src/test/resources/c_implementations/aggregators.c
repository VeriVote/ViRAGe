#include "types.h"
#include "set.h"

result max_aggregator(profile p, result a, result b) {
  set electedUnion = unify(a.elected, b.elected);
  set deferredUnion = unify(a.deferred, b.deferred);
  set rejectedUnion = unify(a.rejected, b.rejected);

  result res;
  res.elected = electedUnion;
  res.deferred = setMinus(deferredUnion, electedUnion);
  res.rejected = setMinus(rejectedUnion, unify(electedUnion, deferredUnion));
  return res;
}
