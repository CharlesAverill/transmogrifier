unsigned long long delta(unsigned long long, unsigned long long);
_Bool accept(unsigned long long);
unsigned long long run(unsigned long long *, unsigned long long);
int $11(void);
unsigned long long const table[8] = { 2LL, 1LL, 1LL, 1LL, 1LL, 0LL, 2LL, 0LL,
  };

unsigned long long delta(unsigned long long $5, unsigned long long $6)
{
  if ($5 < 4LLU & $6 < 2LLU) {
    return *(table + ($5 * 2LLU + $6));
  } else {
    return 4LLU;
  }
}

_Bool accept(unsigned long long $5)
{
  if ($5 == 3LLU) {
    return 1;
  } else {
    if ($5 == 2LLU) {
      return 1;
    } else {
      if ($5 == 0LLU) {
        return 1;
      } else {
        return 0;
      }
    }
  }
}

unsigned long long const q0 = 3LL;

unsigned long long run(unsigned long long *$7, unsigned long long $8)
{
  register unsigned long long $9;
  register unsigned long long $5;
  $9 = 0LLU;
  $5 = 3LLU;
  while (1) {
    if (! ($9 < $8)) {
      break;
    }
    $5 = delta($5, *($7 + $9));
    $9 = $9 + 1LLU;
  }
  return $5;
}

int $11(void)
{
  return 0;
}


