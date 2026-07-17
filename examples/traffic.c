unsigned long long delta(unsigned long long, unsigned long long);
unsigned long long output(unsigned long long);
unsigned long long run(unsigned long long *, unsigned long long);
int $12(void);
unsigned long long const table[8] = { 3LL, 3LL, 0LL, 3LL, 1LL, 3LL, 2LL, 3LL,
  };

unsigned long long const atable[4] = { 2LL, 1LL, 3LL, 0LL, };

unsigned long long delta(unsigned long long $6, unsigned long long $7)
{
  if ($6 < 4LLU & $7 < 2LLU) {
    return *(table + ($6 * 2LLU + $7));
  } else {
    return 4LLU;
  }
}

unsigned long long output(unsigned long long $6)
{
  if ($6 < 4LLU) {
    return *(atable + $6);
  } else {
    return (_Bool) 4LLU;
  }
}

unsigned long long const q0 = 3LL;

unsigned long long run(unsigned long long *$8, unsigned long long $9)
{
  register unsigned long long $10;
  register unsigned long long $6;
  $10 = 0LLU;
  $6 = 3LLU;
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


