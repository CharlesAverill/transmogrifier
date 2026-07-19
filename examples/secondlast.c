void delta(unsigned long long *, unsigned long long, unsigned long long *);
_Bool accept(unsigned long long *);
void run(unsigned long long *, unsigned long long, unsigned long long *);
int $19(void);
unsigned long long const table[6] = { 3LL, 1LL, 4LL, 4LL, 0LL, 0LL, };

unsigned long long const q0[1] = { 1LL, };

unsigned long long const atable[1] = { 4LL, };

void delta(unsigned long long *$6, unsigned long long $8, unsigned long long *$7)
{
  register unsigned long long $10;
  register unsigned long long $11;
  register unsigned long long $9;
  register unsigned long long $12;
  $11 = 0LLU;
  for (; 1; $11 = $11 + 1LLU) {
    if (! ($11 < 1LLU)) {
      break;
    }
    *($7 + $11) = 0LLU;
  }
  if (! ($8 < 2LLU)) {
    return;
  }
  $10 = 0LLU;
  for (; 1; $10 = $10 + 1LLU) {
    if (! ($10 < 1LLU)) {
      break;
    }
    $12 = *($6 + $10);
    if ($12 == 0LLU) {
      continue;
    } else {
      $9 = 0LLU;
      for (; 1; $9 = $9 + 1LLU, $12 = $12 >> 1LLU) {
        if (! ($9 < 64LLU)) {
          break;
        }
        if ($12 == 0LLU) {
          break;
        }
        if (($12 & 1LLU) != 0LLU) {
          if ($10 * 64LLU + $9 < 3LLU) {
            $11 = 0LLU;
            for (; 1; $11 = $11 + 1LLU) {
              if (! ($11 < 1LLU)) {
                break;
              }
              *($7 + $11) =
                *($7 + $11)
                  | *(table
                       + ((($10 * 64LLU + $9) * 2LLU + $8) * 1LLU + $11));
            }
          }
        }
      }
    }
  }
}

_Bool accept(unsigned long long *$6)
{
  register unsigned long long $11;
  register unsigned long long $16;
  $16 = 0LLU;
  $11 = 0LLU;
  for (; 1; $11 = $11 + 1LLU) {
    if (! ($11 < 1LLU)) {
      break;
    }
    $16 = $16 | *($6 + $11) & *(atable + $11);
  }
  return $16 != 0LLU;
}

void run(unsigned long long *$13, unsigned long long $14, unsigned long long *$17)
{
  unsigned long long $6[1];
  unsigned long long $7[1];
  register unsigned long long $15;
  register unsigned long long $11;
  $11 = 0LLU;
  for (; 1; $11 = $11 + 1LLU) {
    if (! ($11 < 1LLU)) {
      break;
    }
    *($6 + $11) = *(q0 + $11);
  }
  $15 = 0LLU;
  while (1) {
    if (! ($15 < $14)) {
      break;
    }
    delta($6, *($13 + $15), $7);
    $11 = 0LLU;
    for (; 1; $11 = $11 + 1LLU) {
      if (! ($11 < 1LLU)) {
        break;
      }
      *($6 + $11) = *($7 + $11);
    }
    $15 = $15 + 1LLU;
  }
  $11 = 0LLU;
  for (; 1; $11 = $11 + 1LLU) {
    if (! ($11 < 1LLU)) {
      break;
    }
    *($17 + $11) = *($6 + $11);
  }
}

int $19(void)
{
  return 0;
}


