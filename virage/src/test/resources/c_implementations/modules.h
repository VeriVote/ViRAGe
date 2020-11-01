#ifndef MODULES_H
#define MODULES_H

#include "types.h"

result elect_module(profile p, result r);
result pass_module(int n, rel relation, profile p, result r);
result drop_module(int n, rel relation, profile p, result r);
result plurality_module(profile p, result r);

#endif
