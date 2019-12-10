#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

int deck[52];

int pick(int n)
{
  int r = (double)n * (double)random() / 2147483648.0;
  assert(r >= 0);
  assert(r < n);
  return r;
}

void initDeck()
{
  for(int i = 0; i < 52; ++i)
    {
      deck[i] = i;
    }
}

void shuffle(int n)
{
  initDeck();
  for(int i = 0; i < n; ++i)
    {
      int c = deck[i];
      int j = i + pick(52 - i);
      deck[i] = deck[j];
      deck[j] = c;
    }
}
void shuffleHoldem(int n)
{
  shuffle(5 + 2*n);
}

int hist[13];

#define rank(x) ((x) % 13)
#define suit(x) ((x) / 13)
#define popCount(x) __builtin_popcountll(x)

#define histo(x) (((0b1UL << hist[x]*13) >> 13) << x)

uint64_t evalHand(int a, int b, int c, int d, int e)
{
  uint64_t h;

  memset(hist, 0, sizeof(hist));
  hist[rank(a)]++;
  hist[rank(b)]++;
  hist[rank(c)]++;
  hist[rank(d)]++;
  hist[rank(e)]++;
  h  = histo(0);
  h |= histo(1);
  h |= histo(2);
  h |= histo(3);
  h |= histo(4);
  h |= histo(5);
  h |= histo(6);
  h |= histo(7);
  h |= histo(8);
  h |= histo(9);
  h |= histo(10);
  h |= histo(11);
  h |= histo(12);

  uint64_t isTwoPairOrTrips = popCount(h) == 3;
  h |= isTwoPairOrTrips << 52;

  uint64_t isWheel = h == 0b1000000001111UL;
  h |= isWheel << 53;

  uint64_t isStraight =
    h == 0b1111100000000UL |
    h == 0b0111110000000UL |
    h == 0b0011111000000UL |
    h == 0b0001111100000UL |
    h == 0b0000111110000UL |
    h == 0b0000011111000UL |
    h == 0b0000001111100UL |
    h == 0b0000000111110UL |
    h == 0b0000000011111UL;

  h |= isStraight << 54;

  uint64_t isFlush = suit(a) == suit(b) & suit(a) == suit(c) & suit(a) == suit(d) & suit(a) == suit(e);
  h |= isFlush << 55;

  uint64_t isFullHouseOrQuads = popCount(h) == 2;
  h |= isFullHouseOrQuads << 56;

  uint64_t isWheelFlush = isWheel & isFlush;
  h |= isWheelFlush << 57;

  uint64_t isStraightFlush = isStraight & isFlush;

  h |= isStraightFlush << 58;

  return h;
}

void printHandEval(uint64_t h)
{
  if ((h & (0x1UL << 57)) | (h & (0x1UL << 58)))
    {
      printf("straightflush");
      return;
    }
  if (h & (0x1UL << 52))
    {
      if (h & 0b111111111111100000000000000000000000000UL)
        {
          printf("trips");
          return;
        }
      printf("two pair");
      return;
    }
  if ((h & (0x1UL << 53)) | (h & (0x1UL << 54)))
    {
      printf("straight");
      return;
    }
  if (h & (0x1UL << 55))
    {
      printf("flush");
      return;
    }
  if (h & (0x1UL << 56))
    {
      if (h & 0b1111111111111UL)
        {
          printf("quads");
          return;
        }
      printf("boat");
      return;
    }
  if (h & 0b11111111111110000000000000UL)
    {
      printf("one pair");
      return;
    }
  printf("high card");
  return;
}

void debug(uint64_t h)
{
  for(int i = 58; i >= 0; --i)
    {
      if ((0x1UL << i) & h)
        {
          printf("1");
        }
      else
        {
          printf("0");
        }
      if (i % 13 == 0)
        {
          printf(" ");
        }
    }

  printf(" ");

  printHandEval(h);

  printf("\n");

}

int main()
{
  /* int tst[2] = { 0, 0 }; */

  /* for(int i = 0; i < 100000000; ++i) */
  /*   { */
  /*     tst[pick(2)]++; */
  /*   } */
  /* printf("%d %d\n", tst[0], tst[1]); */

  assert(popCount(0xffffffffffffffffUL) == 64);
  /* debug(evalHand(0,1,2,3+13,4)); */
  /* debug(evalHand(12,1,2+13,3,0)); */
  /* debug(evalHand(12,0,0+13,5,5)); */
  /* debug(evalHand(12,12+13,12,12,11)); */
  /* debug(evalHand(12,0,0,0+13,0)); */
  /* debug(evalHand(0,1,2,3,4)); */
  /* debug(evalHand(0,1,2,3,12)); */
  /* debug(evalHand(6,7,8,12,9)); */
  /* debug(evalHand(0,0,0,12,12+13)); */
  /* debug(evalHand(0,2,5,12,12+13)); */
  /* debug(evalHand(0,2,5,12,8+13)); */
  /* debug(evalHand(5,5,5,12,8+13)); */
  srandom(42);

  for(int i = 0; i < 100000; ++i)
    {
      shuffleHoldem(0);
      debug(evalHand(deck[0], deck[1], deck[2], deck[3], deck[4]));
    }
  return 0;
}
