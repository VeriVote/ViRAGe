#include <stdlib.h>

#include "types.h"
#include "set.h"

result elect_module(profile p) {
  result res;

  res.elected = p.alternatives;
  res.rejected = emptySet();
  res.deferred = emptySet();

  return res;
}

result pass_module(int n, rel r, profile p) {
  printf("pass_module\n");
  result res;

  res.elected = emptySet();

  int* deferred = malloc(n);
  for(int i=0; i<n; i++) {
    deferred[i] = r.elements[i];
  }
  res.deferred = instantiate(deferred, n);

  int* rejected = malloc(r.size-n);
  for(int i=n; i<r.size; i++) {
    rejected[i-n] = r.elements[i];
  }
  res.rejected = instantiate(rejected, r.size-n);

  printResult(res);
  return res;
}

result drop_module(int n, rel r, profile p) {
  result res;

  res.elected = emptySet();

  int* rejected = malloc(n);
  for(int i=0; i<n; i++) {
    rejected[i] = r.elements[i];
  }
  res.rejected = instantiate(rejected, n);

  int* deferred = malloc(r.size-n);
  for(int i=n; i<r.size; i++) {
    deferred[i-n] = r.elements[i];
  }
  res.deferred = instantiate(deferred, r.size-n);

  return res;
}

result plurality_module(profile p) {
  printSet(p.alternatives);

  int votes[p.alternatives.size];

  for(int i=0; i<p.alternatives.size; i++) {
    votes[i] = 0;
  }

  for(int i=0; i<p.voteCount; i++) {
    int currentWinner = p.votes[i].elements[0];
    for(int j=0; j<p.alternatives.size; j++) {
      if(p.alternatives.contents[j] == currentWinner) {
        votes[j]++;
      }
    }
  }

  for(int i=0; i<p.alternatives.size; i++) {
    printf("%d: %d\n", p.alternatives.contents[i], votes[i]);
  }

  // Find number of winners
  int maxVotes = 0;
  int maxCount = 0;

  for(int i=0; i<p.alternatives.size; i++) {
    if(votes[i] >= maxVotes) {
      if(votes[i] > maxVotes) {
        maxVotes = votes[i];
        maxCount = 1;
      } else {
        maxCount++;
      }
    }
  }

  int* winners = malloc(maxCount);
  int* losers = malloc(p.alternatives.size-maxCount);
  int nextWinner = 0;
  int nextLoser = 0;
  for(int i=0; i<p.alternatives.size; i++) {
    if(votes[i] == maxVotes) {
      winners[nextWinner] = p.alternatives.contents[i];
      nextWinner++;
    } else {
      losers[nextLoser] = p.alternatives.contents[i];
      nextLoser++;
    }
  }

  result res;

  res.elected = instantiate(winners, maxCount);
  res.rejected = instantiate(losers, p.alternatives.size-maxCount);
  res.deferred = emptySet();

  printf("plurality result: \n");
  printResult(res);

  return res;
}
