#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

extern void fannkuch_redux_init_linear(int []);
extern void fannkuch_redux_swap(int*,int*);
extern void fannkuch_redux_reverse_n(int,int []);
extern int fannkuch_redux_num_flips(int []);
extern int fannkuch_redux_permutations(int);
extern void char_hello_world();
extern int powi_powi(int, int);
extern int powi_squared(int);
extern int powi_cubed(int);
extern int powi_pow2(int);
extern void address_inc(int*);
extern void address_inc_op(int*);
extern void address_inc2(int*);
extern void array_foo_array(int[2]);
extern void array_foo_2dim_array(int[2][3]);
extern void char_io_test();
extern void primitives_add315AtLoc(int*);
extern void struct_foo();
extern void enum_foo();
extern void enum_enum_foo(int);
extern void floating_test(float, double);

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

FILE* g_stdin;
FILE* g_stdout;
FILE* g_stderr;

int main(int argc, char**argv)
{
  int n = argc > 1 ? atoi(argv[1]) : 7;

  g_stdin = stdin;
  g_stdout = stdout;
  g_stderr = stderr;

  printf("sizeof int %lu\n", sizeof(int));
  printf("sizeof FILE* %lu\n", sizeof(FILE*));

  /* printf("128^0 = %d\n",powi_powi(128,0)); */
  /* printf("3^2 = %d\n",powi_powi(3,2)); */
  /* printf("2^3 = %d\n",powi_powi(2,3)); */
  /* printf("128^1 = %d\n",powi_powi(128,1)); */
  /* printf("3^2 = %d\n",powi_squared(3)); */
  /* printf("2^3 = %d\n",powi_cubed(2)); */
  /* printf("2^8 = %d\n",powi_pow2(8)); */

  /* int x = 0; */
  /* printf("%d\n",x); */
  /* address_inc(&x); */
  /* printf("%d\n",x); */
  /* address_inc_op(&x); */
  /* printf("%d\n",x); */
  /* address_inc2(&x); */
  /* printf("%d\n",x); */

  /* int arr[2]; */
  /* array_foo_array(arr); */
  /* printf("arr[0] %d\n",arr[0]); */
  /* printf("arr[1] %d\n",arr[1]); */

  /* int arr2[2][3]; */
  /* array_foo_2dim_array(arr2); */

  /* int i,j; */
  /* for(i=0;i<2;++i) */
  /*   { */
  /*     for(j=0;j<3;++j) */
  /*       { */
  /*         printf("arr2[%d][%d] = %d\n",i,j,arr2[i][j]); */
  /*       } */
  /*   } */

  /* int myInt = 4; */
  /* primitives_add315AtLoc(&myInt); */
  /* printf("myInt = %d\n", myInt); */

  /* if(n == 0) */
  /*   { */
  /*     char_io_test(); */
  /*   } */
  /* char_hello_world(); */

  /* enum_enum_foo(0); */
  /* enum_foo(); */

  /* struct_foo(); */

  /* int linear[100] = {42, 42}; */

  /* fannkuch_redux_init_linear(linear); */
  /* printf("linear[0] = %d\n", linear[0]); */
  /* printf("linear[1] = %d\n", linear[1]); */

  /* int rev[] = {4,2,1,5,3}; */
  /* fannkuch_redux_swap(&rev[0], &rev[1]); */
  /* printf("rev[0] = %d\n", rev[0]); */
  /* fannkuch_redux_reverse_n(5, rev); */
  /* printf("rev[0] = %d\n", rev[0]); */

  /* int perm[] = {4,2,1,5,3}; */
  /* printf("flips: %d\n", fannkuch_redux_num_flips(perm)); */
  /* printf("perm[0] = %d\n", perm[0]); */

  /* printf("Pfannkuchen(%d) = %d\n", n, fannkuch_redux_permutations(n)); */

  floating_test(3.2f, 2.3);
  float fx = 3.2f;
  double dx = 2.3;
  floating_test(2.3, dx);
  floating_test(fx, 42.0);

  return 0;
}
