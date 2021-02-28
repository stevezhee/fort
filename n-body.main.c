#include <stdio.h>
#include <stdlib.h>

FILE* g_stdout;
void n_body_advance_n(struct planet bodies[], double adv, int n);
void n_body_offset_momentum(struct planet * bodies);
double n_body_energy(struct planet * bodies);
void n_body_advance(struct planet * bodies, double dt);

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

  int n = argc > 1 ? atoi(argv[1]) : 1000;

  n_body_offset_momentum(bodies);
  printf ("%.9f\n", n_body_energy(bodies));
  n_body_advance_n(bodies, 0.01, n);
  printf ("%.9f\n", n_body_energy(bodies));
  return 0;
}
