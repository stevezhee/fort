#include <stdio.h>
#include <stdlib.h>

extern int powi(int, int);
extern int squared(int);
extern void inc(int*);
extern void inc2(int*);

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
  int x = 0;
  printf("%d\n",powi(3,2));
  printf("%d\n",powi(128,0));
  printf("%d\n",powi(128,1));
  printf("%d\n",powi(3,3));
  printf("%d\n",powi(2,3));
  printf("%d\n",powi(4,6));
  printf("%d\n",squared(3));
  printf("%d\n",x);
  inc(&x);
  printf("%d\n",x);
  inc2(&x);
  printf("%d\n",x);
  return 0;
}
