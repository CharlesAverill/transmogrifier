unsigned int delta(unsigned int, unsigned int);
unsigned int accept(unsigned int);
unsigned int delta(unsigned int $4, unsigned int $5)
{
  if ($4 == 3U) {
    if ($5 == 1U) {
      return 0U;
    } else {
      if ($5 == 0U) {
        return 2U;
      } else {
        return 4U;
      }
    }
  } else {
    if ($4 == 2U) {
      if ($5 == 1U) {
        return 0U;
      } else {
        if ($5 == 0U) {
          return 1U;
        } else {
          return 4U;
        }
      }
    } else {
      if ($4 == 1U) {
        if ($5 == 1U) {
          return 1U;
        } else {
          if ($5 == 0U) {
            return 1U;
          } else {
            return 4U;
          }
        }
      } else {
        if ($4 == 0U) {
          if ($5 == 1U) {
            return 1U;
          } else {
            if ($5 == 0U) {
              return 2U;
            } else {
              return 4U;
            }
          }
        } else {
          return 4U;
        }
      }
    }
  }
}

unsigned int accept(unsigned int $4)
{
  if ($4 == 3U) {
    return 1U;
  } else {
    if ($4 == 2U) {
      return 1U;
    } else {
      if ($4 == 0U) {
        return 1U;
      } else {
        return 0U;
      }
    }
  }
}

unsigned int const q0 = 3;


