#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

unsigned long r, H;
long M, o;
unsigned long n;
long d;
unsigned long corners[6];
typedef struct var Var;
unsigned long* order = NULL;

unsigned long calculate_ending(unsigned long row, unsigned long level) {
    return (row + 1) * r - (n - row) - level;
}

unsigned long calculate_begining( unsigned long row, unsigned long level) {
    return ((row - 1) * r) + (row - n) + level;
}

void calculate_all_edges(unsigned long level,unsigned long *corners_ends) {
    unsigned long idx = 0;
    for (unsigned long i = 0; i < r + 1; i++) {
        if (i >= level && i < r - level + 1) {
            if (i < (r + 1) / 2) {
                corners_ends[idx++] = i * r + level;
                corners_ends[idx++] = calculate_ending(i, level);
            } else if (i > (r + 1) / 2) {
                corners_ends[idx++] = calculate_begining(i, level);
                corners_ends[idx++] = i * r - 1 - level;
            }
        }
    }
}

void calculate_chain(unsigned long level, unsigned long *corners_ends, unsigned long *chain) {
    unsigned long idx = 0;
    for (unsigned long i = corners_ends[0]; i <= corners_ends[1]; i++) {
        chain[idx++] = i;
    }

    unsigned long idx2 = 3;
    for (unsigned long i = 0; i < r - (2 * (level + 1)); i++) {
        chain[idx++] = corners_ends[idx2];
        idx2 += 2;
    }

    idx2 = 2 * (r - 2 * level) - 1;
    for (long i = corners_ends[idx2]; i >= (long)corners_ends[idx2 - 1]; i--) {
        chain[idx++] = i;
    }

    idx2 -= 3;
    for (unsigned long i = 0; i < r - (2 * (level + 1)); i++) {
        chain[idx++] = corners_ends[idx2];
        idx2 -= 2;
    }
}

void initialize_order() {
    order = (unsigned long *)malloc((r * r + 1) * sizeof(unsigned long));
    unsigned long *corners_ends, *chain;
    unsigned long idx = 0;

    for (unsigned long level = 0; level < n - 1; level++) {
        corners_ends = (unsigned long *)malloc(2 * (r - 2 * level) * sizeof(unsigned long));
        calculate_all_edges(level, corners_ends);

        chain = (unsigned long *)malloc((2 * (r - 2 * level) + 2 * (n - 2 - level)) * sizeof(unsigned long));
        calculate_chain(level, corners_ends, chain);

        for (unsigned long j = 0; j < 2 * (r - 2 * level) + 2 * (n - 2 - level); j++) {
            order[idx++] = chain[j];
        }

        free(corners_ends);
        free(chain);
    }

    order[idx++] = r * r / 2; // Center of the hexagon
    order[idx++] = -1; // Placeholder at the end
}

/* constraint variable; if lo==hi, this is the variable's value */
typedef struct var {
  long id; /* variable id; id<0 if the variable is not part of the hexagon */
  long lo; /* lower bound */
  long hi; /* upper bound */
} Var;

/* representation of a hexagon of order n: (2n-1)^2 square array
   for a hexagon of order 2:
     A B
    C D E
     F G
   the representation is:
    A B .
    C D E
    . F G
   The . slots have lo>hi.

   The variable array is organized as a single-dimension array with accesses
   vs[y*r+x]
   This allows to access the diagonal with stride 2*order

   Variable names n, r, H, S according to German Wikipedia Article
   Instead of "i", the deviation variable is called "d" (d=0 means
   that the sum=0; to have the lowest value 1, d=2)
   
   n is the order (number of elements of a side of the hexagon).
   r = 2n-1 (length of the middle row/diagonals)
   H = 3n^2-3n+1 (number of variables)
   M = dH (sum of each row/diagonal)
   lowest  value = dr - (H-1)/2
   highest value = dr + (H-1)/2
*/

unsigned long solutions = 0; /* counter of solutions */
unsigned long leafs = 0; /* counter of leaf nodes visited in the search tree */

long min(long a, long b)
{
  return (a<b)?a:b;
}

long max(long a, long b)
{
  return (a>b)?a:b;
}


/* unless otherwise noted, the following functions return

   0 if there is no solution (i.e., the action eliminates all values
   from a variable),

   1 if there was a change 

   2 if there was no change 
*/


/* returns 0 if there is no solution, 1 if one of the variables has changed */
int lessthan(Var *v1, Var *v2) {
    //assert(v1->id >= 0);
    //assert(v2->id >= 0);

    // Inlining sethi()
    if (v2->hi - 1 < v1->hi) {
        v1->hi = v2->hi - 1;
        if (v1->lo > v1->hi) return 0;
        else return 1;
    }

    // Inlining setlo()
    if (v1->lo + 1 > v2->lo) {
        v2->lo = v1->lo + 1;
        if (v2->lo <= v2->hi) return 1;
        else return 0;
    }

    return 2;
}

int sum(Var vs[], unsigned long nv, unsigned long stride, long sum, Var *vsstart, Var *vsend) {
    unsigned long i;
    long hi = sum;
    long lo = sum;
    Var *vp;

    for (i = 0, vp = vs; i < nv; i++, vp += stride) {
        hi -= vp->lo;
        lo -= vp->hi;
    }
    /* hi is the upper bound of sum - sum(vs), lo the lower bound */
    for (i = 0, vp = vs; i < nv; i++, vp += stride) {
        // Inline sethi
        if (hi + vp->lo < vp->hi) {
            vp->hi = hi + vp->lo;
            if (vp->lo > vp->hi) return 0; // no solution
        }

        // Inline setlo
        if (lo + vp->hi > vp->lo) {
            vp->lo = lo + vp->hi;
            if (vp->lo > vp->hi) return 0; // no solution
        }
    }
    return 2;
}

    
/* reduce the ranges of the variables as much as possible (with the
   constraints we use);  returns 1 if all variables still have a
   non-empty range left, 0 if one has an empty range */
int solve(Var vs[])
{

  unsigned long occupation[H]; /* if vs[i] has value x, occupation[x-o]==i, 
                                  if no vs[*] has value x, occupation[x-o]==H*/
  unsigned long i;
  unsigned long *occPtr = occupation;
  int changes_counter;
  //printf("(re)start\n");
  /* deal with the alldifferent constraint */
  for (i=0; i<H; i++)
    occupation[i] = r*r;
 restart:
 changes_counter = 0;
  for (i=0; i<r*r; i++) {
    Var *v = &vs[i];
    if (v->lo == v->hi && *(occPtr + (v->lo - o)) != i) {
      if (*(occPtr + (v->lo - o)) < r*r)
        return 0; /* another variable has the same value */
      *(occPtr + (v->lo - o)) = i; /* occupy v->lo */
      changes_counter = 1;
    }}
  
  /* now propagate the alldifferent results to the bounds */
for (i=0; i<r*r; i++) {
    Var *v = &vs[i];
    if (v->lo < v->hi) {
      while (*(occPtr + (v->lo - o)) < r*r) {
        v->lo++;
        if(v->lo>v->hi) return 0;
        changes_counter = 1;
      }
      while (*(occPtr + (v->hi - o)) < r*r) {
        v->hi--;
        if(v->lo>v->hi) return 0;
        changes_counter = 1;
      }
    }
  }

  /* the < constraints; all other corners are smaller than the first
     one (eliminate rotational symmetry) */
  for (i=1; i<sizeof(corners)/sizeof(corners[0]); i++) {
    int f = lessthan(&vs[corners[0]],&vs[corners[i]]);
    if (f==0) return 0;
    if (f==1) changes_counter = 1;
  }
  /* eliminate the mirror symmetry between the corners to the right
     and left of the first corner */
  {
    int f = lessthan(&vs[corners[2]],&vs[corners[1]]); 
    if (f==0) return 0;
    if (f==1) changes_counter = 1;
  }
  /* sum constraints: each line and diagonal sums up to M */
  /* line sum constraints */
  for (i=0; i<r; i++) {
    int f;
    /* line */
    f = sum(vs+r*i+max(0,i+1-n), min(i+n,r+n-i-1), 1, M, vs, vs+r*r);
    if (f==0) return 0;
    if (f==1) changes_counter = 1;
    /* column (diagonal down-left in the hexagon) */
    f = sum(vs+i+max(0,i+1-n)*r, min(i+n,r+n-i-1), r, M, vs, vs+r*r);
    if (f==0) return 0;
    if (f==1) changes_counter = 1;
    /* diagonal (down-right) */
    f = sum(vs-n+1+i+max(0,n-i-1)*(r+1), min(i+n,r+n-i-1), r+1, M, vs, vs+r*r);
    if (f==0) return 0;
    if (f==1) changes_counter = 1;
  }
  if (changes_counter > 0) goto restart;
  return 1;
}

void printhexagon(Var vs[])
{
  unsigned long i,j;

  for (i=0; i<r; i++) {
    unsigned long l=0;
    unsigned long h=r;
    if (i+1>n)
      l = i+1-n;
    if (i+1<n)
      h = n+i;
    for (j=h-l; j<r; j++)
      printf("    ");
    for (j=l; j<h; j++) {
      //assert(i<r);
      //assert(j<r);
      Var *v=&vs[i*r+j];
      //assert(v->lo <= v->hi);
#if 0
      printf("%6ld  ",v->id);
#else
      if (v->lo < v->hi)
        printf("%4ld-%-3ld",v->lo,v->hi);
      else
        printf("%6ld  ",v->lo);
#endif
    }
    printf("\n");
  }
}

/* assign values to vs[index] and all later variables in vs such that
   the constraints hold */
void labeling(Var vs[], unsigned long index)
{
  long i;
  unsigned long current_index = order[index];
  Var *vp = vs+current_index;
  if (current_index == -1) {
    printhexagon(vs);
    solutions++;
    leafs++;
    printf("leafs visited: %lu\n\n",leafs);
    return;
  }
  if (vp->id < 0)
    return labeling(vs,index+1);
  for (i = vp->lo; i <= vp->hi; i++) {
    Var newvs[r*r];
    Var* newvp=newvs+current_index;
    memmove(newvs,vs,r*r*sizeof(Var));
    newvp->lo = i;
    newvp->hi = i;
#if 0
    for (Var *v = newvs; v<=newvp; v++) {
      if (v->id >= 0) {
        assert(v->lo == v->hi);
        printf(" %ld",v->lo); fflush(stdout);
      }
    }
    printf("\n");
#endif
    if (solve(newvs))
      labeling(newvs,index+1);
    else
      leafs++;
  }
}

Var *makehexagon()
{
  unsigned long i,j;

  Var *vs = calloc(r*r,sizeof(Var));
  unsigned long id = 0;
  for (i=0; i<r*r; i++) {
    Var *v = &vs[i];
    v->id = -1;
    v->lo = 1;
    v->hi = 0;
  }
  for (i=0; i<r; i++) {
    unsigned long l=0;
    unsigned long h=r;
    if (i+1>n)
      l = i+1-n;
    if (i+1<n)
      h = n+i;
    for (j=l; j<h; j++) {
      //assert(i<r);
      //assert(j<r);
      Var *v=&vs[i*r+j];
      //assert(v->lo>v->hi);
      v->id = id++;
      v->lo = d*r - (H-1)/2;
      v->hi = d*r + (H-1)/2;
    }
  }
  return vs;
}

int main(int argc, char *argv[])
{
  unsigned long i;
  unsigned long j=0;
  if (argc < 3) {
    fprintf(stderr, "Usage: %s <order> <deviation> <value> ... <value>\n", argv[0]);
    exit(1);
  }
  n = strtoul(argv[1],NULL,10);
  if (n<1) {
    fprintf(stderr, "order must be >=1\n");
    exit(1);
  }

  r = 2*n-1;
  H = 3*n*n-3*n+1;
  d = strtol(argv[2],NULL,10);
  M = d*H;
  o = d*r - (H-1)/2;
  Var *vs = makehexagon();
  for (i=3; i<argc; i++) {
    while (vs[j].id < 0)
      j++;
    vs[j].lo = vs[j].hi = strtol(argv[i],NULL,10);
    j++;
  }
  corners[0] = 0;
  corners[1] = n-1;
  corners[2] = (n-1)*r+0;
  corners[3] = (n-1)*r+r-1;
  corners[4] = (r-1)*r+n-1;
  corners[5] = (r-1)*r+r-1;
  // Allocate memory for the order array
  order = (unsigned long*)malloc((r*r + 2) * sizeof(unsigned long));
  if (order == NULL) {
      // Handle memory allocation error
      exit(1);
  }

  
  // Initialize the custom order for search
  initialize_order();
  labeling(vs,0);
  printf("%lu solution(s), %lu leafs visited\n",solutions, leafs);
  //(void)solve(n, d, vs);
  //printhexagon(n, vs);
  return 0;
}
