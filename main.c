#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

extern void reverse_n(int,int []);
extern int fannkuch_redux_fannkuch(int []);
extern void char_hello_world();
extern int powi_powi(int, int);
extern int powi_squared(int);
extern void address_inc(int*);
extern void address_inc2(int*);
extern void array_foo_array(int[2]);
extern void char_char_io_test();
extern void array_foo_2dim_array(int[2][3]);
extern void primitives_add315AtLoc(int*);
extern void struct_foo();
extern void enum_foo();
extern void enum_enum_foo(int);

void h_put_uint64(uint64_t x, FILE *h)
{
  fprintf(h, "%llu", x);
}

void h_put_sint64(int64_t x, FILE *h)
{
  fprintf(h, "%lld", x);
}

FILE* g_stdin;
FILE* g_stdout;
FILE* g_stderr;

int main(int argc, char**argv)
{
  g_stdin = stdin;
  g_stdout = stdout;
  g_stderr = stderr;

  printf("3^2 = %d\n",powi_powi(3,2));
  printf("128^0 = %d\n",powi_powi(128,0));
  printf("128^1 = %d\n",powi_powi(128,1));
  printf("3^2 = %d\n",powi_squared(3));

  int x = 0;
  printf("%d\n",x);
  address_inc(&x);
  printf("%d\n",x);
  address_inc2(&x);
  printf("%d\n",x);

  int arr[2];
  array_foo_array(arr);
  printf("arr[0] %d\n",arr[0]);
  printf("arr[1] %d\n",arr[1]);

  printf("sizeof int %lu\n", sizeof(int));
  printf("sizeof FILE* %lu\n", sizeof(FILE*));

  printf("stdin %p\n",stdin);

  if(argc > 1)
    {
      char_char_io_test();
    }

  int arr2[2][3];
  array_foo_2dim_array(arr2);

  int i,j;
  for(i=0;i<2;++i)
    {
      for(j=0;j<3;++j)
        {
          printf("arr2[%d][%d] = %d\n",i,j,arr2[i][j]);
        }
    }

  int myInt = 4;
  primitives_add315AtLoc(&myInt);
  printf("myInt = %d\n", myInt);

  char_hello_world();

  int perm[] = {4,2,1,5,3};
  printf("flips: %d\n", fannkuch_redux_fannkuch(perm));

  enum_enum_foo(0);

  for(i=0; i < 5; ++i)
    {
      printf("%d,",perm[i]);
    }
  printf("\n");

  struct_foo();
  enum_foo();

  /* 228 */
  /* Pfannkuchen(7) = 16 */
  return 0;
}
