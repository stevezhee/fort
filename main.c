#include <stdio.h>

extern int pow(int, int);

int main()
{
  printf("%d\n",pow(3,2));
  printf("%d\n",pow(128,0));
  printf("%d\n",pow(128,1));
  printf("%d\n",pow(3,3));
  printf("%d\n",pow(2,3));
  printf("%d\n",pow(4,6));
  return 0;
}
