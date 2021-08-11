#ifndef TYPES_H
#define TYPES_H

#ifndef V
#define V 5
#endif

#ifndef C
#define C 5
#endif

#define ELECTED 2
#define DEFERRED 1
#define REJECTED 0

typedef struct {
  int alternatives[C];
  int votes[V][C];
} profile;

typedef struct {
  int elements[C];
} rel;

typedef struct {
  int values[C];
} result;

int find_index(profile p, int alternative);
rel get_default_ordering(profile p);

#endif
