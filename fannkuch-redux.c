/* The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * converted to C by Joseph Piché
 * from Java version by Oleg Mazurov and Isaac Gouy
 *
 */

#include <stdio.h>
#include <stdlib.h>

inline static int max(int a, int b)
{
    return a > b ? a : b;
}

int fannkuchredux(int n)
{
    int perm[n];
    int perm1[n];
    int count[n];
    int maxFlipsCount = 0;
    int permCount = 0;
    int checksum = 0;

    int i;

    for (i=0; i<n; i+=1)
        perm1[i] = i;
    int r = n;

    while (1) {
        while (r != 1) {
            count[r-1] = r;
            r--;
        }

        for (i=0; i<n; i++)
            perm[i] = perm1[i];
        int flipsCount = 0;
        int k;

        while ( !((k = perm[0]) == 0) ) {
            int k2 = (k+1) >> 1;
            for (i=0; i<k2; i++) {
                int temp = perm[i]; perm[i] = perm[k-i]; perm[k-i] = temp;
            }
            flipsCount += 1;
        }

        maxFlipsCount = max(maxFlipsCount, flipsCount);
        checksum += permCount % 2 == 0 ? flipsCount : -flipsCount;

        for (i=0; i<n; i+=1)
          printf("%d ", 1 + perm1[i]); // BAL:
        printf("\n"); // BAL:
        /* printf("\n %d flips\n", flipsCount); // BAL: */
        /* printf(" %d perms\n", permCount); // BAL: */
        /* printf("%d checksum\n", checksum); // BAL: */

        /* Use incremental change to generate another permutation */
        while (1) {
            if (r == n) {
                printf("%d\n", checksum);
                return maxFlipsCount;
            }

            int perm0 = perm1[0];
            i = 0;
            while (i < r) {
                int j = i + 1;
                perm1[i] = perm1[j];
                i = j;
            }
            perm1[r] = perm0;
            count[r] = count[r] - 1;
            if (count[r] > 0) break;
            r++;
        }
        permCount++;
    }
}

int main(int argc, char *argv[])
{
    int n = argc > 1 ? atoi(argv[1]) : 7;
    printf("Pfannkuchen(%d) = %d\n", n, fannkuchredux(n));
    return 0;
}

/* notes, command-line, and program output */
/* NOTES: */
/* 64-bit Ubuntu quad core */
/* gcc (Ubuntu 8.2.0-7ubuntu1) 8.2.0 */


/* Sun, 25 Nov 2018 21:58:45 GMT */

/* MAKE: */
/* /usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -march=native  fannkuchredux.c -o fannkuchredux.gcc_run  */
/* rm fannkuchredux.c */

/* 2.85s to complete and log all make actions */

/* COMMAND LINE: */
/* ./fannkuchredux.gcc_run 12 */

/* PROGRAM OUTPUT: */
/* 3968050 */
/* Pfannkuchen(12) = 65 */
