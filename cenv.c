#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

FILE* g_stdin;
FILE* g_stdout;
FILE* g_stderr;

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

void init_cenv()
{
  g_stdin = stdin;
  g_stdout = stdout;
  g_stderr = stderr;
}
