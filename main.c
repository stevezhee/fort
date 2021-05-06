#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

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
  fprintf(h, "%.9f", x);
}

int main(int argc, char**argv)
{
  g_stdin = stdin;
  g_stdout = stdout;
  g_stderr = stderr;

  assert(sizeof(int) == 4);
  assert(sizeof(FILE*) == 8);
  assert(sizeof(long) == 8);
  assert(sizeof(float) == 4);
  assert(sizeof(double) == 8);

  /* printf("sizeof int %lu\n", sizeof(int)); */
  /* printf("sizeof FILE* %lu\n", sizeof(FILE*)); */
  /* printf("sizeof long %lu\n", sizeof(long)); */
  /* printf("sizeof float %lu\n", sizeof(float)); */
  /* printf("sizeof double %lu\n", sizeof(double)); */

  int r = _main(argc, argv);

  printf("\n");

  return r;
}
