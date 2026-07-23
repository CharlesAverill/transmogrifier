unsigned long long delta(unsigned long long, unsigned long long, unsigned long long *);
void run(unsigned long long *, unsigned long long, unsigned long long *);
int $13(void);
unsigned long long const table[20] = { 0LL, 0LL, 0LL, 0LL, 1LL, 1LL, 1LL,
  1LL, 1LL, 1LL, 2LL, 0LL, 2LL, 2LL, 1LL, 2LL, 3LL, 3LL, 3LL, 1LL, };

unsigned long long const otable[20] = { 0LL, 0LL, 3LL, 2LL, 4LL, 4LL, 4LL,
  4LL, 4LL, 4LL, 0LL, 2LL, 0LL, 2LL, 4LL, 1LL, 0LL, 0LL, 0LL, 4LL, };

unsigned long long delta(unsigned long long $5, unsigned long long $6, unsigned long long *$7)
{
  if ($5 < 4LLU & $6 < 5LLU) {
    *$7 = *(otable + ($5 * 5LLU + $6));
    return *(table + ($5 * 5LLU + $6));
  } else {
    *$7 = 5LLU;
    return 4LLU;
  }
}

unsigned long long const q0 = 3LL;

void run(unsigned long long *$8, unsigned long long $9, unsigned long long *$7)
{
  unsigned long long $11;
  register unsigned long long $10;
  register unsigned long long $5;
  $10 = 0LLU;
  $5 = 3LLU;
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


