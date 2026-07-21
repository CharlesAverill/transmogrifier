unsigned long long delta(unsigned long long, unsigned long long, unsigned long long *);
void run(unsigned long long *, unsigned long long, unsigned long long *);
int $13(void);
unsigned long long const table[24] = { 5LL, 5LL, 5LL, 5LL, 0LL, 5LL, 5LL,
  5LL, 1LL, 0LL, 5LL, 5LL, 2LL, 1LL, 5LL, 5LL, 3LL, 2LL, 5LL, 5LL, 4LL, 3LL,
  0LL, 5LL, };

unsigned long long const otable[24] = { 1LL, 2LL, 5LL, 10LL, 0LL, 1LL, 4LL,
  9LL, 0LL, 0LL, 3LL, 8LL, 0LL, 0LL, 2LL, 7LL, 0LL, 0LL, 1LL, 6LL, 0LL, 0LL,
  0LL, 0LL, };

unsigned long long delta(unsigned long long $5, unsigned long long $6, unsigned long long *$7)
{
  if ($5 < 6LLU & $6 < 4LLU) {
    *$7 = *(otable + ($5 * 4LLU + $6));
    return *(table + ($5 * 4LLU + $6));
  } else {
    *$7 = 11LLU;
    return 6LLU;
  }
}

unsigned long long const q0 = 5LL;

void run(unsigned long long *$8, unsigned long long $9, unsigned long long *$7)
{
  unsigned long long $11;
  register unsigned long long $10;
  register unsigned long long $5;
  $10 = 0LLU;
  $5 = 5LLU;
  while (1) {
    if (! ($10 < $9)) {
      break;
    }
    $5 = delta($5, *($8 + $10), &$11);
    *($7 + $10) = $11;
    $10 = $10 + 1LLU;
  }
}

int $13(void)
{
  return 0;
}


