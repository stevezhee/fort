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
  fprintf(h, "%.9f", x);
}


int main(int argc, char**argv)
{
  g_stdin = stdin;
  g_stdout = stdout;
  g_stderr = stderr;

  /* printf("sizeof int %lu\n", sizeof(int)); */
  /* printf("sizeof FILE* %lu\n", sizeof(FILE*)); */

  return _main(argc, argv);

  return 0;
}
