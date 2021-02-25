#include <stdio.h>
#include <stdlib.h>

void mandelbrot_write_pbm(int);
FILE* g_stdout;

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


int main(int argc, char **argv)
{
  g_stdout = stdout;

  int w = argc > 1 ? atoi(argv[1]) : 200;

  printf("P4\n%d %d\n",w,w);
  mandelbrot_write_pbm(w);

  return 0;
}
