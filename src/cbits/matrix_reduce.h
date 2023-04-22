#ifndef MATRIX_REDUCE_H
#define MATRIX_REDUCE_H

/* The tensor is assumed to be in a sort of col_major order or, in other words,
   we sum and eliminate the outermost dimension, not the innermost. */

void row_sum_double(int nrows, int ncols, const double *x, double *y);

void row_sum_float(int nrows, int ncols, const float *x, float *y);

#endif /* MATRIX_REDUCE_H */
