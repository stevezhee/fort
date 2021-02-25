/* mandelbrot gcc #2 (modified) */
/* The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/

   contributed by Greg Buchholz

   for the debian (AMD) machine...
   compile flags:  -O3 -ffast-math -march=athlon-xp -funroll-loops

   for the gp4 (Intel) machine...
   compile flags:  -O3 -ffast-math -march=pentium4 -funroll-loops
*/

#include<stdio.h>
#include<stdlib.h>
#include<assert.h>

int main (int argc, char **argv)
{
    int w, h, bit_num = 0;
    char byte_acc = 0;
    int i, iter = 50;
    double x, y, limit = 2.0;
    double limit2 = 4.0;
    double Zr, Zi, Cr, Ci, Tr, Ti;

    w = h = argc > 1 ? atoi(argv[1]) : 200;

    printf("P4\n%d %d\n",w,h);

    for(y=0;y<h;++y)
    {
      assert(bit_num == 0);
      assert(byte_acc == 0);
      Ci = ((2.0*y)/h) - 1.0;
        for(x=0;x<w;++x)
        {
          assert(x < w);
            Cr = ((2.0*x)/w) - 1.5;
            Zi = 0.0;
            Zr = 0.0;
            Ti = 0.0;
            Tr = 0.0;
            for (i=0;i<iter && (Tr + Ti <= limit2);++i)
            {
              Zi = ((2.0*Zr)*Zi) + Ci;
              Zr = (Tr - Ti) + Cr;
              Ti = Zi * Zi;
              Tr = Zr * Zr;
            }

            byte_acc = (byte_acc << 1) | (Tr+Ti <= limit2);

            if(bit_num == 7)
              {
                putc(byte_acc,stdout);
                goto output;
              }
            if(x == (w-1))
            {
              putc(byte_acc << (8-(w%8)),stdout);
              goto output;
            }
            ++bit_num;
            continue;
        output:
            byte_acc = 0;
            bit_num = 0;
        }
    }
}


/* notes, command-line, and program output */
/* NOTES: */
/* 64-bit Ubuntu quad core */
/* gcc (Ubuntu 10.2.0-13ubuntu1) 10.2.0 */


/* Mon, 02 Nov 2020 18:50:30 GMT */

/* MAKE: */
/* /usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -march=ivybridge  mandelbrot.gcc-2.c -o mandelbrot.gcc-2.gcc_run  */
/* mandelbrot.gcc-2.c: In function ‘main’: */
/* mandelbrot.gcc-2.c:23:13: warning: implicit declaration of function ‘atoi’ [-Wimplicit-function-declaration] */
/*    23 |     w = h = atoi(argv[1]); */
/*       |             ^~~~ */
/* rm mandelbrot.gcc-2.c */

/* 1.60s to complete and log all make actions */

/* COMMAND LINE: */
/* ./mandelbrot.gcc-2.gcc_run 16000 */

/* (BINARY) PROGRAM OUTPUT NOT SHOWN */
