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
	while(!defer_eq_condition(1,p,r)) {
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

result borda(profile p, result r) {
	int num_deferred = 0;
	for(int i=0; i<C; i++) {
		if(r.values[i] == DEFERRED) num_deferred++;
	}

	int values[C];
	for(int i=0; i<C; i++) {
		values[i] = 0;
	}

	for(int v=0; v<V; v++) {
		int available_points = num_deferred-1;

		for(int c=0; c<C; c++) {
			int current_alternative = p.votes[v][c];

			if(r.values[current_alternative] == DEFERRED) {
				values[current_alternative] += available_points;
				available_points--;
			}

			if(available_points == 0) break;
		}
	}

	int max_value = 0;
	for(int i=0; i<C; i++) {
		if(values[i] > max_value) {
			max_value = values[i];
		}
	}

	for(int i=0; i<C; i++) {
		if(r.values[i] == DEFERRED) {
			if(values[i] == max_value) {
				r.values[i] = ELECTED;
			} else {
			}
		}
	}

	return r;
}

result voting_rule(profile p) {
  result r;

  for(int i=0; i<C; i++) {
    r.values[i] = DEFERRED;
  }

  //r = seq_comp_0(p,r);
	r = plurality_module(p,r);
	//r = borda(p,r);

  return r;
}
