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
  shuffle(5 + 2 * n);
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

  uint64_t isWheel = h == 0b1000000001111UL;

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

  uint64_t isFlush = suit(a) == suit(b) & suit(a) == suit(c) & suit(a) == suit(d) & suit(a) == suit(e);

  uint64_t isFullHouseOrQuads = popCount(h) == 2;

  uint64_t isWheelFlush = isWheel & isFlush;

  uint64_t isStraightFlush = isStraight & isFlush;

  h |= isTwoPairOrTrips << 52;
  h |= isWheel << 53;
  h |= isStraight << 54;
  h |= isFlush << 55;
  h |= isFullHouseOrQuads << 56;
  h |= isWheelFlush << 57;
  h |= isStraightFlush << 58;

  return h;
}

#define max(x, y) ((x) > (y) ? (x) : (y))
#define min(x, y) ((x) < (y) ? (x) : (y))

uint64_t evalHoldem(int x)
{
  int i = 5 + x * 2;
  int j = i + 1;
  uint64_t h = evalHand(deck[0], deck[1], deck[2], deck[3], deck[4]);

  h = max(h, evalHand(deck[0], deck[1], deck[2], deck[3], deck[i]));
  h = max(h, evalHand(deck[0], deck[1], deck[2], deck[i], deck[4]));
  h = max(h, evalHand(deck[0], deck[1], deck[i], deck[3], deck[4]));
  h = max(h, evalHand(deck[0], deck[i], deck[2], deck[3], deck[4]));
  h = max(h, evalHand(deck[i], deck[1], deck[2], deck[3], deck[4]));

  h = max(h, evalHand(deck[0], deck[1], deck[2], deck[3], deck[j]));
  h = max(h, evalHand(deck[0], deck[1], deck[2], deck[j], deck[4]));
  h = max(h, evalHand(deck[0], deck[1], deck[j], deck[3], deck[4]));
  h = max(h, evalHand(deck[0], deck[j], deck[2], deck[3], deck[4]));
  h = max(h, evalHand(deck[j], deck[1], deck[2], deck[3], deck[4]));

  h = max(h, evalHand(deck[0], deck[1], deck[2], deck[i], deck[j]));
  h = max(h, evalHand(deck[0], deck[1], deck[i], deck[3], deck[j]));
  h = max(h, evalHand(deck[0], deck[1], deck[i], deck[j], deck[4]));
  h = max(h, evalHand(deck[0], deck[i], deck[2], deck[3], deck[j]));
  h = max(h, evalHand(deck[0], deck[i], deck[2], deck[j], deck[4]));
  h = max(h, evalHand(deck[0], deck[i], deck[j], deck[3], deck[4]));
  h = max(h, evalHand(deck[i], deck[1], deck[2], deck[3], deck[j]));
  h = max(h, evalHand(deck[i], deck[1], deck[2], deck[j], deck[4]));
  h = max(h, evalHand(deck[i], deck[1], deck[j], deck[3], deck[4]));
  h = max(h, evalHand(deck[i], deck[j], deck[2], deck[3], deck[4]));

  return h;
}
char ranks[] = "23456789TJQKA";
char *suits = "shcd";

void printCard(int c)
{
  printf("%c%c", ranks[rank(c)], suits[suit(c)]);
}

void printBoard()
{
  printCard(deck[0]);
  printCard(deck[1]);
  printCard(deck[2]);
  printCard(deck[3]);
  printCard(deck[4]);
}

void printPocket(int x)
{
  printCard(deck[5 + x * 2]);
  printCard(deck[5 + x * 2 + 1]);
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
  /* for(int i = 58; i >= 0; --i) */
  /*   { */
  /*     if ((0x1UL << i) & h) */
  /*       { */
  /*         printf("1"); */
  /*       } */
  /*     else */
  /*       { */
  /*         printf("0"); */
  /*       } */
  /*     if (i % 13 == 0) */
  /*       { */
  /*         printf(" "); */
  /*       } */
  /*   } */

  /* printf(" "); */

  printHandEval(h);

  printf("\n");

}

int nHoldem[256];
int valueHoldem[256];

void initStats()
{
  memset(nHoldem, 0, sizeof(nHoldem));
  memset(valueHoldem, 0, sizeof(valueHoldem));
}

int canonicalHand(int x)
{
  int i = deck[5 + x * 2];
  int j = deck[5 + x * 2 + 1];

  int ri = rank(i);
  int rj = rank(j);

  int mx = max(ri, rj);
  int mn = min(ri, rj);

  if (suit(i) == suit(j))
    {
      return (mx << 4 | mn);
    }
  return (mn << 4 | mx);
}

void fullEval(int n)
{
  shuffleHoldem(n);
  /* printBoard(); printf("\n"); */
  uint64_t win = 0;
  int winners[10];
  int nWinners;
  nWinners = 0;
  for(int i = 0; i < n; ++i)
    {
      uint64_t h = evalHoldem(i);
      int ch = canonicalHand(i);
      nHoldem[ch]++;
      if (h > win)
        {
          win = h;
          nWinners = 1;
          winners[0] = ch;
        } else if (h == win)
        {
          winners[nWinners] = ch;
          nWinners++;
        }
      /* printPocket(i); printf(" "); */
      /* debug(h); */
    }

  double value = 1.0 / (double)nWinners;

  for(int i = 0; i < nWinners; ++i)
    {
      valueHoldem[winners[i]] += value;
    }
  /* if (nWinners == 1) */
  /*   { */
  /*     printf("player #%d won\n", winners[0]); */
  /*     printPocket(winners[0]); printf(" "); */
  /*     debug(win); */
  /*   } */
  /* else */
  /*   { */
  /*     printf("%d way chop\n", nWinners); */
  /*     for(int i = 0; i < nWinners; ++i) */
  /*       { */
  /*         printPocket(winners[i]); printf(" "); */
  /*       } */
  /*     debug(win); */
  /*   } */
}
void printCanonical(ch)
{
  int a = (0xf0 & ch) >> 4;
  int b = 0xf & ch;
  if (a > b)
    {
      printf("%c%cs", ranks[a], ranks[b]);
      return;
    }
  printf("%c%c ", ranks[b], ranks[a]);
  return;
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
  srandom(42);
  initStats();

  int n = 1000000;
  for(int i = 0; i < n; ++i)
    {
      fullEval(10);
    }

  double all = 0.0;

  for(int ch = 255; ch >= 0; --ch)
    {
      if (nHoldem[ch] == 0) continue;
      printf("%f ", valueHoldem[ch]/(double)nHoldem[ch]);
      printCanonical(ch);
      double pct = (double)nHoldem[ch]/(double)n;
      printf(" %f\n", pct);
      // all += pct;
    }

  printf("100 = %f\n", all);

  return 0;
}
