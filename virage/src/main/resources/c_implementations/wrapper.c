#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "types.h"
#include "voting_rule.h"

char** order = NULL;

char** split_string(char* str) {
  char* delim = ";\n";

  char** res = malloc(sizeof(char*)*C);

  char* ptr = strtok(str,delim);

  int i=0;
  while(ptr != NULL) {
    res[C-i-1] = ptr;

    ptr = strtok(NULL,delim);

    i++;
  }

  return res;
}

int find_order_index(char* candidate) {
  for(int i=0; i<C; i++) {
    if(!strcmp(candidate, order[i])) return i;
  }

  return C;
}

int main(int argc, char** argv) {
  if(argc < 1) {
    printf("Please submit an input file.\n");
  }

  FILE * fp;
  char * line = NULL;
  size_t len = 0;
  ssize_t read;


  int** ballots = malloc(sizeof(int*)*V);
  for(int i=0; i<V; i++) {
    ballots[i] = malloc(sizeof(int)*C);
  }

  fp = fopen(argv[1], "r");
  if (fp == NULL)
      exit(EXIT_FAILURE);

  int voter = 0;
  int first = 1;
  while ((read = getline(&line, &len, fp)) != -1) {
      char** ballot = split_string(line);

      if(first) {
        order = malloc(sizeof(char*)*C);
        for(int i=0; i<C; i++) {
          order[i] = malloc(sizeof(char)*strlen(ballot[i]));
        }

        for(int i=0; i<C; i++) {
          strcpy(order[i],ballot[i]);
        }
        first = 0;
      }

      for(int j=0; j<C; j++) {
        int index = find_order_index(ballot[j]);

        ballots[voter][j] = index;
      }

      voter++;
  }

  fclose(fp);

  profile p;
  for(int i=0; i<C; i++) {
          p.alternatives[i] = i;
  }

  for(int i=0; i<V; i++) {
          for(int j=0; j<C; j++) {
                  p.votes[i][j] = ballots[i][j];
          }
  }

  result r = voting_rule(p);

  printf("elected: ");
  for(int i=0; i<C; i++) {
    if(r.values[i] == ELECTED) {
      printf("%s ",order[i]);
    }
  }
  printf("\n");

  exit(EXIT_SUCCESS);
}
