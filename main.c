#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

FILE* g_stdin;
FILE* g_stdout;
FILE* g_stderr;

extern int _main(int argc, char**argv);

void h_put_uint64(uint64_t x, FILE *h)
{
  fprintf(h, "%llu", x);
}

void h_put_sint64(int64_t x, FILE *h)
{
  fprintf(h, "%lld", x);
}

void h_put_f64(double x, FILE *h)
{
  fprintf(h, "%f", x);
}


int main(int argc, char**argv)
{
  g_stdin = stdin;
  g_stdout = stdout;
  g_stderr = stderr;

  return _main(argc, argv);

  /* int n = argc > 1 ? atoi(argv[1]) : 7; */


  /* printf("sizeof int %lu\n", sizeof(int)); */
  /* printf("sizeof FILE* %lu\n", sizeof(FILE*)); */

  /* int i,j; */
  /* for(i=0;i<2;++i) */
  /*   { */
  /*     for(j=0;j<3;++j) */
  /*       { */
  /*         printf("arr2[%d][%d] = %d\n",i,j,arr2[i][j]); */
  /*       } */
  /*   } */

  /* struct_foo(); */

  /* int rev[] = {4,2,1,5,3}; */
  /* fannkuch_redux_swap(&rev[0], &rev[1]); */
  /* printf("rev[0] = %d\n", rev[0]); */
  /* fannkuch_redux_reverse_n(5, rev); */
  /* printf("rev[0] = %d\n", rev[0]); */

  /* int perm[] = {4,2,1,5,3}; */
  /* printf("flips: %d\n", fannkuch_redux_num_flips(perm)); */
  /* printf("perm[0] = %d\n", perm[0]); */

  /* printf("Pfannkuchen(%d) = %d\n", n, fannkuch_redux_permutations(n)); */

  /* floating_test(3.2f, 2.3); */
  /* float fx = 3.2f; */
  /* double dx = 2.3; */
  /* floating_test(2.3, dx); */
  /* floating_test(fx, 42.0); */

  return 0;
}
