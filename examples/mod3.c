unsigned long long delta(unsigned long long, unsigned long long);
unsigned long long accept(unsigned long long);
unsigned long long run(unsigned long long *, unsigned long long);
int $12(void);
unsigned long long const table[6] = { 0LL, 2LL, 1LL, 0LL, 2LL, 1LL, };

unsigned long long const atable[3] = { 1LL, 1LL, 0LL, };

unsigned long long delta(unsigned long long $6, unsigned long long $7)
{
  if ($6 < 3LLU & $7 < 2LLU) {
    return *(table + ($6 * 2LLU + $7));
  } else {
    return 3LLU;
  }
}

unsigned long long accept(unsigned long long $6)
{
  if ($6 < 3LLU) {
    return *(atable + $6);
  } else {
    return (_Bool) 0U;
  }
}

unsigned long long const q0 = 2LL;

unsigned long long run(unsigned long long *$8, unsigned long long $9)
{
  register unsigned long long $10;
  register unsigned long long $6;
  $10 = 0LLU;
  $6 = 2LLU;
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


