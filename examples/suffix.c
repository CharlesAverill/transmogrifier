unsigned long long delta(unsigned long long, unsigned long long);
unsigned long long accept(unsigned long long);
unsigned long long run(unsigned long long *, unsigned long long);
int $12(void);
unsigned long long const init[32] = { 0LL, 0LL, 3LL, 1LL, 7LL, 5LL, 7LL, 5LL,
  11LL, 9LL, 11LL, 9LL, 15LL, 13LL, 15LL, 13LL, 3LL, 1LL, 3LL, 1LL, 7LL, 5LL,
  7LL, 5LL, 11LL, 9LL, 11LL, 9LL, 15LL, 13LL, 15LL, 13LL, };

unsigned long long const final[16] = { 1LL, 1LL, 1LL, 1LL, 1LL, 1LL, 1LL,
  1LL, 0LL, 0LL, 0LL, 0LL, 0LL, 0LL, 0LL, 0LL, };

unsigned long long delta(unsigned long long $6, unsigned long long $7)
{
  if ($6 < 16LLU & $7 < 2LLU) {
    return *(init + ($6 * 2LLU + $7));
  } else {
    return 16LLU;
  }
}

unsigned long long accept(unsigned long long $6)
{
  if ($6 < 16LLU) {
    return *(final + $6);
  } else {
    return (_Bool) 2LLU;
  }
}

unsigned long long const table = 1LL;

unsigned long long run(unsigned long long *$8, unsigned long long $9)
{
  register unsigned long long $10;
  register unsigned long long $6;
  $10 = 0LLU;
  $6 = 1LLU;
  while (1) {
    if (! ($10 < $9)) {
      break;
    }
    $6 = delta($6, *($8 + $10));
    $10 = $10 + 1LLU;
  }
  return $6;
}

int $12(void)
{
  return 0;
}


