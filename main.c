#include <stdio.h>
#include <stdlib.h>

typedef struct {
  int x;
  char y;
  long int z;
} MyStruct;

typedef struct {
  long int x;
  int y;
} MyStruct2;

extern int powi(int, int);
extern int squared(int);
extern void inc(int*);
extern void inc2(int*);
extern void foo_array(int[]);
extern void foo_struct(MyStruct*, MyStruct2*);

int getChar()
{
  int c = fgetc(stdin);
  if (c == EOF){
    exit(ferror(stdin));
  }
  return c;
}
void putChar(int c)
{
  int r = fputc(c, stdout);
  if (r == EOF){
    exit(ferror(stdout));
  }
}
int main()
{
  printf("%d\n",powi(3,2));
  printf("%d\n",powi(128,0));
  printf("%d\n",powi(128,1));
  printf("%d\n",powi(3,3));
  printf("%d\n",powi(2,3));
  printf("%d\n",powi(4,6));
  printf("%d\n",squared(3));

  int x = 0;
  printf("%d\n",x);
  inc(&x);
  printf("%d\n",x);
  inc2(&x);
  printf("%d\n",x);

  int arr[2];
  foo_array(arr);
  printf("arr[0] %d\n",arr[0]);
  printf("arr[1] %d\n",arr[1]);

  MyStruct mystruct;
  MyStruct2 mystruct2;
  printf("sizeof MyStruct.x %lu\n", sizeof(mystruct.x));
  printf("sizeof MyStruct.y %lu\n", sizeof(mystruct.y));
  printf("sizeof MyStruct.z %lu\n", sizeof(mystruct.z));
  printf("sizeof MyStruct %lu\n", sizeof(mystruct));
  foo_struct(&mystruct, &mystruct2);
  printf("mystruct.x %d\n",mystruct.x);
  printf("mystruct.y %c\n",mystruct.y);
  printf("mystruct.z %lu\n",mystruct.z);
  printf("mystruct2.x %lu\n",mystruct2.x);
  printf("mystruct2.y %d\n",mystruct2.y);
  return 0;
}
