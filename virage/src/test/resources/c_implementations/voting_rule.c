#include "types.h"
#include "modules.h"
#include "aggregators.h"
#include "termination_conditions.h"



// downgrade
result downgrade_5(profile p, result r) {
	r = plurality_module(p,r);
	for(int i=0; i<C; i++) {
		if(r.values[i] == ELECTED) {
			r.values[i] = DEFERRED;
		} else {
			r.values[i] = REJECTED;
		}
	}

	return r;
}
// downgrade

// seq_comp
result seq_comp_4(profile p, result r) {
	r = downgrade_5(p,r);
	r = pass_module(1,get_default_ordering(p),p,r);
	return r;
}
// seq_comp
// seq_comp
result seq_comp_3(profile p, result r) {
	r = pass_module(2,get_default_ordering(p),p,r);
	r = seq_comp_4(p,r);
	return r;
}
// seq_comp

// parallel_comp
result parallel_comp_2(profile p, result r) {
	return max_aggregator(seq_comp_3(p,r),drop_module(2,get_default_ordering(p),p,r));
}
// parallel_comp
// loop_comp
result loop_comp_1(profile p, result r) {
	while(defer_eq_condition(1,p,r)) {
	  r = parallel_comp_2(p,r);
	}

	return r;
}
// loop_comp

// seq_comp
result seq_comp_0(profile p, result r) {
	r = loop_comp_1(p,r);
	r = elect_module(p,r);
	return r;
}
// seq_comp

int[C] voting_rule(int[V][C] votes) {
  profile p;
  p.alternatives = votes[0];
  p.votes = votes;

  result r;
  int values[C];
  for(int i=0; i<C; i++) {
    values[i] = DEFERRED;
  }
  r.values = values;

  r = seq_comp_0(p,r);

  int res[C];
  int nextSpot = 0;
  for(int i=ELECTED, i>=REJECTED; i--) {
    for(int j=0; j<C; j++) {
      if(r.values[j] == i) {
        res[nextSpot] = p.alternatives[j];
        nextSpot++;
      }
    }
  }

  return res;
}
