/// \file
/// \brief arithmetic overflow helpers
///
/// Replace this with stdckdint.h when moving to C23.

#pragma once

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>

/** add two integers, checking for overflow
 *
 * \param a Operand 1
 * \param b Operand 2
 * \param res [out] Result on success
 * \return True if overflow would occur
 */
static inline bool sadd_overflow(int a, int b, int *res) {
  assert(res != NULL);

  // delegate to hardware optimized implementations where possible
#if defined(__clang__) &&                                                      \
    (__clang_major__ > 3 ||                                                    \
     (__clang_major__ == 3 && __clang_minor__ > 7)) // Clang ≥ 3.8
  return __builtin_sadd_overflow(a, b, res);
#elif defined(__GNUC__) && __GNUC__ > 4 // GCC ≥ 5
  return __builtin_sadd_overflow(a, b, res);
#endif

  if (a > 0 && INT_MAX - a < b) {
    return true;
  }
  if (a < 0 && INT_MIN - a > b) {
    return true;
  }

  *res = a + b;
  return false;
}
