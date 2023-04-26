#include "matrix_reduce.h"

/* The tensor is assumed to be in a sort of col_major order or, in other words,
   we sum and eliminate the outermost dimension, not the innermost. */

/* Inspired by https://hackage.haskell.org/package/hmatrix-morpheus
The result array y is allocated and zeroed before being passed here.
 */
void row_sum_double(int nrows, int ncols, const double *x, double *y) {
  for (int j = 0; j < ncols; j++) {
    const double *column = x + j * nrows;
    for (int i = 0; i < nrows; i++) {
      y[i] += column[i];
    }
  }
}
void column_sum_double(int nrows, int ncols, const double *x, double *y) {
  for (int j = 0; j < ncols; j++) {
    const double *column = &x[j * nrows];
    y[j] = 0;
    for (int i = 0; i < nrows; i++) {
      y[j] += column[i];
    }
  }
}

void row_sum_float(int nrows, int ncols, const float *x, float *y) {
  for (int j = 0; j < ncols; j++) {
    const float *column = x + j * nrows;
    for (int i = 0; i < nrows; i++) {
      y[i] += column[i];
    }
  }
}
void column_sum_float(int nrows, int ncols, const float *x, float *y) {
  for (int j = 0; j < ncols; j++) {
    const float *column = &x[j * nrows];
    y[j] = 0;
    for (int i = 0; i < nrows; i++) {
      y[j] += column[i];
    }
  }
}
