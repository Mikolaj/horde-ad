#ifndef MATRIX_REDUCE_H
#define MATRIX_REDUCE_H

/* The tensor is assumed to be in a sort of col_major order or, in other words,
   we sum and eliminate the outermost dimension, not the innermost. */

void row_sum_double(int nrows, int ncols, const double *x, double *y);
void column_sum_double(int nrows, int ncols, const double *x, double *y);

void row_sum_float(int nrows, int ncols, const float *x, float *y);
void column_sum_float(int nrows, int ncols, const float *x, float *y);

void row_sum_int64(int nrows, int ncols, const long long *x, long long *y);
void column_sum_int64(int nrows, int ncols, const long long *x, long long *y);

#endif /* MATRIX_REDUCE_H */
