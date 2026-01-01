#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <string.h>
#include <math.h>
#include <threads.h>
#include <sys/time.h>

// These are the wrapper macros used in arith_lists.h. Preset them to empty to
// avoid having to touch macros unrelated to the particular operation set below.
#define LIST_BINOP(name, id, hsop)
#define LIST_IBINOP(name, id, hsop)
#define LIST_FBINOP(name, id, hsop)
#define LIST_UNOP(name, id, _)
#define LIST_FUNOP(name, id, _)
#define LIST_REDOP(name, id, _)


// Shorter names, due to CPP used both in function names and in C types.
typedef int8_t i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;


// PRECONDITIONS
//
// All strided array operations in this file assume that none of the shape
// components are zero -- that is, the input arrays are non-empty. This must
// be arranged on the Haskell side.
//
// Furthermore, note that while the Haskell side has an offset into the backing
// vector, the C side assumes that the offset is zero. Shift the pointer if
// necessary.


/*****************************************************************************
 *                          Performance statistics                           *
 *****************************************************************************/

// Each block holds a buffer with variable-length messages. Each message starts
// with a tag byte; the respective sublists below give the fields after that tag
// byte.
// - 1: unary operation performance measurement
//   - u8: some identifier
//   - i32: input rank
//   - i64[rank]: input shape
//   - i64[rank]: input strides
//   - f64: seconds taken
// - 2: binary operation performance measurement
//   - u8: a stats_binary_id
//   - i32: input rank
//   - i64[rank]: input shape
//   - i64[rank]: input 1 strides
//   - i64[rank]: input 2 strides
//   - f64: seconds taken
// The 'prev' and 'cap' fields are set only once on creation of a block, and can
// thus be read without restrictions. The 'len' field is potentially mutated
// from different threads and must be handled with care.
struct stats_block {
  struct stats_block *prev;  // backwards linked list; NULL if first block
  size_t cap;  // bytes capacity of buffer in this block
  atomic_size_t len;  // bytes filled in this buffer
  uint8_t buf[];  // trailing VLA
};

enum stats_binary_id {
  sbi_dotprod = 1,
};

// Atomic because blocks may be allocated from different threads.
static _Atomic(struct stats_block*) stats_current = NULL;
static atomic_bool stats_enabled = false;

void oxarrays_stats_enable(i32 yes) { atomic_store(&stats_enabled, yes == 1); }

static uint8_t* stats_alloc(size_t nbytes) {
try_again: ;
  struct stats_block *block = atomic_load(&stats_current);
  size_t curlen = block != NULL ? atomic_load(&block->len) : 0;
  size_t curcap = block != NULL ? block->cap : 0;

  if (block == NULL || curlen + nbytes > curcap) {
    const size_t newcap = stats_current == NULL ? 4096 : 2 * stats_current->cap;
    struct stats_block *new = malloc(sizeof(struct stats_block) + newcap);
    new->prev = stats_current;
    curcap = new->cap = newcap;
    curlen = new->len = 0;
    if (!atomic_compare_exchange_strong(&stats_current, &block, new)) {
      // Race condition, simply free this memory block and try again
      free(new);
      goto try_again;
    }
    block = new;
  }

  // Try to update the 'len' field of the block we captured at the start of the
  // function. Note that it doesn't matter if someone else already allocated a
  // new block in the meantime; we're still accessing the same block here, which
  // may succeed or fail independently.
  while (!atomic_compare_exchange_strong(&block->len, &curlen, curlen + nbytes)) {
    // curlen was updated to the actual value.
    // If the block got full in the meantime, try again from the start
    if (curlen + nbytes > curcap) goto try_again;
  }

  return block->buf + curlen;
}

__attribute__((unused))
static void stats_record_unary(enum stats_binary_id id, i32 rank, const i64 *shape, const i64 *strides, double secs) {
  if (!atomic_load(&stats_enabled)) return;
  uint8_t *buf = stats_alloc(1 + 1 + 4 + 2*rank*8 + 8);
  *buf = 1; buf += 1;
  *buf = id; buf += 1;
  *(i32*)buf = rank; buf += 4;
  memcpy((i64*)buf, shape, rank * 8); buf += rank * 8;
  memcpy((i64*)buf, strides, rank * 8); buf += rank * 8;
  *(double*)buf = secs;
}

__attribute__((unused))
static void stats_record_binary(enum stats_binary_id id, i32 rank, const i64 *shape, const i64 *strides1, const i64 *strides2, double secs) {
  if (!atomic_load(&stats_enabled)) return;
  uint8_t *buf = stats_alloc(1 + 1 + 4 + 3*rank*8 + 8);
  *buf = 2; buf += 1;
  *buf = id; buf += 1;
  *(i32*)buf = rank; buf += 4;
  memcpy((i64*)buf, shape, rank * 8); buf += rank * 8;
  memcpy((i64*)buf, strides1, rank * 8); buf += rank * 8;
  memcpy((i64*)buf, strides2, rank * 8); buf += rank * 8;
  *(double*)buf = secs;
}

#define TIME_START(varname_) \
  struct timeval varname_ ## _start, varname_ ## _end; \
  gettimeofday(&varname_ ## _start, NULL);
#define TIME_END(varname_) \
  (gettimeofday(&varname_ ## _end, NULL), \
   ((varname_ ## _end).tv_sec - (varname_ ## _start).tv_sec) + \
      ((varname_ ## _end).tv_usec - (varname_ ## _start).tv_usec) / (double)1e6)

static size_t stats_print_unary(uint8_t *buf) {
  uint8_t *orig_buf = buf;

  enum stats_binary_id id = *buf; buf += 1;
  i32 rank = *(i32*)buf; buf += 4;
  i64 *shape = (i64*)buf; buf += rank * 8;
  i64 *strides = (i64*)buf; buf += rank * 8;
  double secs = *(double*)buf; buf += 8;

  i64 shsize = 1; for (i32 i = 0; i < rank; i++) shsize *= shape[i];

  printf("unary %d sz %" PRIi64 " ms %.3lf sh=[", (int)id, shsize, secs * 1000);
  for (i32 i = 0; i < rank; i++) { if (i > 0) putchar(','); printf("%" PRIi64, shape[i]); }
  printf("] str=[");
  for (i32 i = 0; i < rank; i++) { if (i > 0) putchar(','); printf("%" PRIi64, strides[i]); }
  printf("]\n");

  return buf - orig_buf;
}

static size_t stats_print_binary(uint8_t *buf) {
  uint8_t *orig_buf = buf;

  enum stats_binary_id id = *buf; buf += 1;
  i32 rank = *(i32*)buf; buf += 4;
  i64 *shape = (i64*)buf; buf += rank * 8;
  i64 *strides1 = (i64*)buf; buf += rank * 8;
  i64 *strides2 = (i64*)buf; buf += rank * 8;
  double secs = *(double*)buf; buf += 8;

  i64 shsize = 1; for (i32 i = 0; i < rank; i++) shsize *= shape[i];

  printf("binary %d sz %" PRIi64 " ms %.3lf sh=[", (int)id, shsize, secs * 1000);
  for (i32 i = 0; i < rank; i++) { if (i > 0) putchar(','); printf("%" PRIi64, shape[i]); }
  printf("] str1=[");
  for (i32 i = 0; i < rank; i++) { if (i > 0) putchar(','); printf("%" PRIi64, strides1[i]); }
  printf("] str2=[");
  for (i32 i = 0; i < rank; i++) { if (i > 0) putchar(','); printf("%" PRIi64, strides2[i]); }
  printf("]\n");

  return buf - orig_buf;
}

// Also frees the printed log.
void oxarrays_stats_print_all(void) {
  printf("=== ox-arrays-arith-stats start ===\n");

  // Claim the entire chain and prevent new blocks from being added to it.
  // (This is technically slightly wrong because a value may still be in the
  // process of being recorded to some blocks in the chain while we're doing
  // this printing, but yolo)
  struct stats_block *last = atomic_exchange(&stats_current, NULL);

  // Reverse the linked list; after this loop, the 'prev' pointers point to the
  // _next_ block, not the previous one.
  struct stats_block *block = last;
  if (last != NULL) {
    struct stats_block *next = NULL;
    //                     block    next
    //   #####  <-#####  <-#####    NULL
    while (block->prev != NULL) {
      struct stats_block *prev = block->prev;
      //          prev     block    next
      // #####  <-#####  <-#####    ##...
      block->prev = next;
      //          prev     block    next
      // #####  <-#####    #####->  ##...
      next = block;
      //          prev     bl=nx
      // #####  <-#####    #####->  ##...
      block = prev;
      //          block    next
      // #####  <-#####    #####->  ##...
    }
    //            block    next
    //    NULL  <-#####    #####->  ##...
    block->prev = next;
    //            block    next
    //    NULL    #####->  #####->  ##...
  }

  while (block != NULL) {
    for (size_t i = 0; i < block->len; ) {
      switch (block->buf[i]) {
        case 1: i += 1 + stats_print_unary(block->buf + i+1); break;
        case 2: i += 1 + stats_print_binary(block->buf + i+1); break;
        default:
          printf("# UNKNOWN ENTRY WITH ID %d, SKIPPING BLOCK\n", (int)block->buf[i]);
          i = block->len;
          break;
      }
    }
    struct stats_block *next = block->prev;  // remember, reversed!
    free(block);
    block = next;
  }

  printf("=== ox-arrays-arith-stats end ===\n");
}


/*****************************************************************************
 *                         Additional math functions                         *
 *****************************************************************************/

#define GEN_ABS(x) \
  _Generic((x), \
      i8: abs, \
      i16: abs, \
      int: abs, \
      long: labs, \
      long long: llabs, \
      float: fabsf, \
      double: fabs)(x)

// This does not result in multiple loads with GCC 13.
#define GEN_SIGNUM(x) ((x) < 0 ? -1 : (x) > 0 ? 1 : 0)

#define GEN_POW(x, y) _Generic((x), float: powf, double: pow)(x, y)
#define GEN_LOGBASE(x, y) _Generic((x), float: logf(y) / logf(x), double: log(y) / log(x))
#define GEN_ATAN2(y, x) _Generic((x), float: atan2f(y, x), double: atan2(y, x))
#define GEN_EXP(x) _Generic((x), float: expf, double: exp)(x)
#define GEN_LOG(x) _Generic((x), float: logf, double: log)(x)
#define GEN_SQRT(x) _Generic((x), float: sqrtf, double: sqrt)(x)
#define GEN_SIN(x) _Generic((x), float: sinf, double: sin)(x)
#define GEN_COS(x) _Generic((x), float: cosf, double: cos)(x)
#define GEN_TAN(x) _Generic((x), float: tanf, double: tan)(x)
#define GEN_ASIN(x) _Generic((x), float: asinf, double: asin)(x)
#define GEN_ACOS(x) _Generic((x), float: acosf, double: acos)(x)
#define GEN_ATAN(x) _Generic((x), float: atanf, double: atan)(x)
#define GEN_SINH(x) _Generic((x), float: sinhf, double: sinh)(x)
#define GEN_COSH(x) _Generic((x), float: coshf, double: cosh)(x)
#define GEN_TANH(x) _Generic((x), float: tanhf, double: tanh)(x)
#define GEN_ASINH(x) _Generic((x), float: asinhf, double: asinh)(x)
#define GEN_ACOSH(x) _Generic((x), float: acoshf, double: acosh)(x)
#define GEN_ATANH(x) _Generic((x), float: atanhf, double: atanh)(x)
#define GEN_LOG1P(x) _Generic((x), float: log1pf, double: log1p)(x)
#define GEN_EXPM1(x) _Generic((x), float: expm1f, double: expm1)(x)

// Taken from Haskell's implementation:
//   https://hackage.haskell.org/package/ghc-internal-9.1001.0/docs/src//GHC.Internal.Float.html#log1mexpOrd
#define LOG1MEXP_IMPL(x) do { \
    if (x > _Generic((x), float: logf, double: log)(2)) return GEN_LOG(-GEN_EXPM1(x)); \
    else return GEN_LOG1P(-GEN_EXP(x)); \
  } while (0)

static float log1mexp_float(float x) { LOG1MEXP_IMPL(x); }
static double log1mexp_double(double x) { LOG1MEXP_IMPL(x); }

#define GEN_LOG1MEXP(x) _Generic((x), float: log1mexp_float, double: log1mexp_double)(x)

// Taken from Haskell's implementation:
//   https://hackage.haskell.org/package/ghc-internal-9.1001.0/docs/src//GHC.Internal.Float.html#line-595
#define LOG1PEXP_IMPL(x) do { \
      if (x <= 18) return GEN_LOG1P(GEN_EXP(x)); \
      if (x <= 100) return x + GEN_EXP(-x); \
      return x; \
  } while (0)

static float log1pexp_float(float x) { LOG1PEXP_IMPL(x); }
static double log1pexp_double(double x) { LOG1PEXP_IMPL(x); }

#define GEN_LOG1PEXP(x) _Generic((x), float: log1pexp_float, double: log1pexp_double)(x)


/*****************************************************************************
 *                             Helper functions                              *
 *****************************************************************************/

__attribute__((used))
static void print_shape(FILE *stream, i64 rank, const i64 *shape) {
  fputc('[', stream);
  for (i64 i = 0; i < rank; i++) {
    if (i != 0) fputc(',', stream);
    fprintf(stream, "%" PRIi64, shape[i]);
  }
  fputc(']', stream);
}


/*****************************************************************************
 *                                Skeletons                                  *
 *****************************************************************************/

// Walk a orthotope-style strided array, except for the inner dimension. The
// body is run for every "inner vector".
// Provides idx, outlinidx, arrlinidx.
#define TARRAY_WALK_NOINNER(again_label_name, rank, shape, strides, ...) \
  do { \
    i64 idx[(rank) /* - 1 */]; /* Note: [zero-length VLA] */ \
    memset(idx, 0, ((rank) - 1) * sizeof(idx[0])); \
    i64 arrlinidx = 0; \
    i64 outlinidx = 0; \
  again_label_name: \
    { \
      __VA_ARGS__ \
    } \
    for (i64 dim = (rank) - 2; dim >= 0; dim--) { \
      if (++idx[dim] < (shape)[dim]) { \
        arrlinidx += (strides)[dim]; \
        outlinidx++; \
        goto again_label_name; \
      } \
      arrlinidx -= (idx[dim] - 1) * (strides)[dim]; \
      idx[dim] = 0; \
    } \
  } while (false)

// Walk TWO orthotope-style strided arrays simultaneously, except for their
// inner dimension. The arrays must have the same shape, but may have different
// strides. The body is run for every pair of "inner vectors".
// Provides idx, outlinidx, arrlinidx1, arrlinidx2.
#define TARRAY_WALK2_NOINNER(again_label_name, rank, shape, strides1, strides2, ...) \
  do { \
    i64 idx[(rank) /* - 1 */]; /* Note: [zero-length VLA] */ \
    memset(idx, 0, ((rank) - 1) * sizeof(idx[0])); \
    i64 arrlinidx1 = 0, arrlinidx2 = 0; \
    i64 outlinidx = 0; \
  again_label_name: \
    { \
      __VA_ARGS__ \
    } \
    for (i64 dim = (rank) - 2; dim >= 0; dim--) { \
      if (++idx[dim] < (shape)[dim]) { \
        arrlinidx1 += (strides1)[dim]; \
        arrlinidx2 += (strides2)[dim]; \
        outlinidx++; \
        goto again_label_name; \
      } \
      arrlinidx1 -= (idx[dim] - 1) * (strides1)[dim]; \
      arrlinidx2 -= (idx[dim] - 1) * (strides2)[dim]; \
      idx[dim] = 0; \
    } \
  } while (false)


/*****************************************************************************
 *                             Kernel functions                              *
 *****************************************************************************/

#define COMM_OP_STRIDED(name, op, typ) \
  static void oxarop_op_ ## name ## _ ## typ ## _sv_strided(i64 rank, const i64 *shape, typ *restrict out, typ x, const i64 *strides, const typ *y) { \
    if (rank == 0) { out[0] = x op y[0]; return; } \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = x op y[arrlinidx + strides[rank - 1] * i]; \
      } \
    }); \
  } \
  static void oxarop_op_ ## name ## _ ## typ ## _vv_strided(i64 rank, const i64 *shape, typ *restrict out, const i64 *strides1, const typ *x, const i64 *strides2, const typ *y) { \
    if (rank == 0) { out[0] = x[0] op y[0]; return; } \
    TARRAY_WALK2_NOINNER(again, rank, shape, strides1, strides2, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = x[arrlinidx1 + strides1[rank - 1] * i] op y[arrlinidx2 + strides2[rank - 1] * i]; \
      } \
    }); \
  }

#define NONCOMM_OP_STRIDED(name, op, typ) \
  COMM_OP_STRIDED(name, op, typ) \
  static void oxarop_op_ ## name ## _ ## typ ## _vs_strided(i64 rank, const i64 *shape, typ *restrict out, const i64 *strides, const typ *x, typ y) { \
    if (rank == 0) { out[0] = x[0] op y; return; } \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = x[arrlinidx + strides[rank - 1] * i] op y; \
      } \
    }); \
  }

#define PREFIX_BINOP_STRIDED(name, op, typ) \
  static void oxarop_op_ ## name ## _ ## typ ## _sv_strided(i64 rank, const i64 *shape, typ *restrict out, typ x, const i64 *strides, const typ *y) { \
    if (rank == 0) { out[0] = op(x, y[0]); return; } \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = op(x, y[arrlinidx + strides[rank - 1] * i]); \
      } \
    }); \
  } \
  static void oxarop_op_ ## name ## _ ## typ ## _vv_strided(i64 rank, const i64 *shape, typ *restrict out, const i64 *strides1, const typ *x, const i64 *strides2, const typ *y) { \
    if (rank == 0) { out[0] = op(x[0], y[0]); return; } \
    TARRAY_WALK2_NOINNER(again, rank, shape, strides1, strides2, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = op(x[arrlinidx1 + strides1[rank - 1] * i], y[arrlinidx2 + strides2[rank - 1] * i]); \
      } \
    }); \
  } \
  static void oxarop_op_ ## name ## _ ## typ ## _vs_strided(i64 rank, const i64 *shape, typ *restrict out, const i64 *strides, const typ *x, typ y) { \
    if (rank == 0) { out[0] = op(x[0], y); return; } \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = op(x[arrlinidx + strides[rank - 1] * i], y); \
      } \
    }); \
  }

#define UNARY_OP_STRIDED(name, op, typ) \
  static void oxarop_op_ ## name ## _ ## typ ## _strided(i64 rank, typ *restrict out, const i64 *shape, const i64 *strides, const typ *arr) { \
    /* fprintf(stderr, "oxarop_op_" #name "_" #typ "_strided: rank=%ld shape=", rank); \
    print_shape(stderr, rank, shape); \
    fprintf(stderr, " strides="); \
    print_shape(stderr, rank, strides); \
    fprintf(stderr, "\n"); */ \
    if (rank == 0) { out[0] = op(arr[0]); return; } \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        out[outlinidx * shape[rank - 1] + i] = op(arr[arrlinidx + strides[rank - 1] * i]); \
      } \
    }); \
  }

// Used for reduction and dot product kernels below
#define MANUAL_VECT_WID 8

// Used in REDUCE1_OP and REDUCEFULL_OP below
#define REDUCE_BODY_CODE(op, typ, innerLen, innerStride, arr, arrlinidx, destination) \
  do { \
    const i64 n = innerLen; const i64 s = innerStride; \
    if (n < MANUAL_VECT_WID) { \
      typ accum = arr[arrlinidx]; \
      for (i64 i = 1; i < n; i++) accum = accum op arr[arrlinidx + s * i]; \
      destination = accum; \
    } else { \
      typ accum[MANUAL_VECT_WID]; \
      for (i64 j = 0; j < MANUAL_VECT_WID; j++) accum[j] = arr[arrlinidx + s * j]; \
      for (i64 i = 1; i < n / MANUAL_VECT_WID; i++) { \
        for (i64 j = 0; j < MANUAL_VECT_WID; j++) { \
          accum[j] = accum[j] op arr[arrlinidx + s * (MANUAL_VECT_WID * i + j)]; \
        } \
      } \
      typ res = accum[0]; \
      for (i64 j = 1; j < MANUAL_VECT_WID; j++) res = res op accum[j]; \
      for (i64 i = n / MANUAL_VECT_WID * MANUAL_VECT_WID; i < n; i++) \
        res = res op arr[arrlinidx + s * i]; \
      destination = res; \
    } \
  } while (0)

// Reduces along the innermost dimension.
// 'out' will be filled densely in linearisation order.
#define REDUCE1_OP(name, op, typ) \
  static void oxarop_op_ ## name ## _ ## typ(i64 rank, typ *restrict out, const i64 *shape, const i64 *strides, const typ *arr) { \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      REDUCE_BODY_CODE(op, typ, shape[rank - 1], strides[rank - 1], arr, arrlinidx, out[outlinidx]); \
    }); \
  }

#define REDUCEFULL_OP(name, op, typ) \
  typ oxarop_op_ ## name ## _ ## typ(i64 rank, const i64 *shape, const i64 *strides, const typ *arr) { \
    if (rank == 0) return arr[0]; \
    typ result = 0; \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      REDUCE_BODY_CODE(op, typ, shape[rank - 1], strides[rank - 1], arr, arrlinidx, result); \
    }); \
    return result; \
  }

// Writes extreme index to outidx. If 'cmp' is '<', computes minindex ("argmin"); if '>', maxindex.
#define EXTREMUM_OP(name, cmp, typ) \
  void oxarop_extremum_ ## name ## _ ## typ(i64 *restrict outidx, i64 rank, const i64 *shape, const i64 *strides, const typ *arr) { \
    if (rank == 0) return; /* output index vector has length 0 anyways */ \
    typ best = arr[0]; \
    memset(outidx, 0, rank * sizeof(i64)); \
    TARRAY_WALK_NOINNER(again, rank, shape, strides, { \
      bool found = false; \
      for (i64 i = 0; i < shape[rank - 1]; i++) { \
        if (arr[arrlinidx + i] cmp best) { \
          best = arr[arrlinidx + strides[rank - 1] * i]; \
          found = true; \
          outidx[rank - 1] = i; \
        } \
      } \
      if (found) memcpy(outidx, idx, (rank - 1) * sizeof(i64)); \
    }); \
  }

// Reduces along the innermost dimension.
// 'out' will be filled densely in linearisation order.
#define DOTPROD_INNER_OP(typ) \
  void oxarop_dotprodinner_ ## typ(i64 rank, const i64 *shape, typ *restrict out, const i64 *strides1, const typ *arr1, const i64 *strides2, const typ *arr2) { \
    TIME_START(tm); \
    TARRAY_WALK2_NOINNER(again3, rank, shape, strides1, strides2, { \
      const i64 length = shape[rank - 1], stride1 = strides1[rank - 1], stride2 = strides2[rank - 1]; \
      if (length < MANUAL_VECT_WID) { \
        typ res = 0; \
        for (i64 i = 0; i < length; i++) res += arr1[arrlinidx1 + stride1 * i] * arr2[arrlinidx2 + stride2 * i]; \
        out[outlinidx] = res; \
      } else { \
        typ accum[MANUAL_VECT_WID]; \
        for (i64 j = 0; j < MANUAL_VECT_WID; j++) accum[j] = arr1[arrlinidx1 + stride1 * j] * arr2[arrlinidx2 + stride2 * j]; \
        for (i64 i = 1; i < length / MANUAL_VECT_WID; i++) \
          for (i64 j = 0; j < MANUAL_VECT_WID; j++) \
            accum[j] += arr1[arrlinidx1 + stride1 * (MANUAL_VECT_WID * i + j)] * arr2[arrlinidx2 + stride2 * (MANUAL_VECT_WID * i + j)]; \
        typ res = accum[0]; \
        for (i64 j = 1; j < MANUAL_VECT_WID; j++) res += accum[j]; \
        for (i64 i = length / MANUAL_VECT_WID * MANUAL_VECT_WID; i < length; i++) \
          res += arr1[arrlinidx1 + stride1 * i] * arr2[arrlinidx2 + stride2 * i]; \
        out[outlinidx] = res; \
      } \
    }); \
    stats_record_binary(sbi_dotprod, rank, shape, strides1, strides2, TIME_END(tm)); \
  }


/*****************************************************************************
 *                           Entry point functions                           *
 *****************************************************************************/

__attribute__((noreturn, cold))
static void wrong_op(const char *name, int tag) {
  fprintf(stderr, "ox-arrays: Invalid operation tag passed to %s C code: %d\n", name, tag);
  abort();
}

enum binop_tag_t {
#undef LIST_BINOP
#define LIST_BINOP(name, id, hsop) name = id,
#include "arith_lists.h"
#undef LIST_BINOP
#define LIST_BINOP(name, id, hsop)
};

#define ENTRY_BINARY_STRIDED_OPS(typ) \
  void oxarop_binary_ ## typ ## _sv_strided(enum binop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, typ x, const i64 *strides, const typ *y) { \
    switch (tag) { \
      case BO_ADD: oxarop_op_add_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      case BO_SUB: oxarop_op_sub_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      case BO_MUL: oxarop_op_mul_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      default: wrong_op("binary_sv_strided", tag); \
    } \
  } \
  void oxarop_binary_ ## typ ## _vs_strided(enum binop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, const i64 *strides, const typ *x, typ y) { \
    switch (tag) { \
      case BO_ADD: oxarop_op_add_ ## typ ## _sv_strided(rank, shape, out, y, strides, x); break; \
      case BO_SUB: oxarop_op_sub_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      case BO_MUL: oxarop_op_mul_ ## typ ## _sv_strided(rank, shape, out, y, strides, x); break; \
      default: wrong_op("binary_vs_strided", tag); \
    } \
  } \
  void oxarop_binary_ ## typ ## _vv_strided(enum binop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, const i64 *strides1, const typ *x, const i64 *strides2, const typ *y) { \
    switch (tag) { \
      case BO_ADD: oxarop_op_add_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      case BO_SUB: oxarop_op_sub_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      case BO_MUL: oxarop_op_mul_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      default: wrong_op("binary_vv_strided", tag); \
    } \
  }

enum ibinop_tag_t {
#undef LIST_IBINOP
#define LIST_IBINOP(name, id, hsop) name = id,
#include "arith_lists.h"
#undef LIST_IBINOP
#define LIST_IBINOP(name, id, hsop)
};

#define ENTRY_IBINARY_STRIDED_OPS(typ) \
  void oxarop_ibinary_ ## typ ## _sv_strided(enum ibinop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, typ x, const i64 *strides, const typ *y) { \
    switch (tag) { \
      case IB_QUOT: oxarop_op_quot_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      case IB_REM:  oxarop_op_rem_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      default: wrong_op("ibinary_sv_strided", tag); \
    } \
  } \
  void oxarop_ibinary_ ## typ ## _vs_strided(enum ibinop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, const i64 *strides, const typ *x, typ y) { \
    switch (tag) { \
      case IB_QUOT: oxarop_op_quot_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      case IB_REM:  oxarop_op_rem_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      default: wrong_op("ibinary_vs_strided", tag); \
    } \
  } \
  void oxarop_ibinary_ ## typ ## _vv_strided(enum ibinop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, const i64 *strides1, const typ *x, const i64 *strides2, const typ *y) { \
    switch (tag) { \
      case IB_QUOT: oxarop_op_quot_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      case IB_REM:  oxarop_op_rem_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      default: wrong_op("ibinary_vv_strided", tag); \
    } \
  }

enum fbinop_tag_t {
#undef LIST_FBINOP
#define LIST_FBINOP(name, id, hsop) name = id,
#include "arith_lists.h"
#undef LIST_FBINOP
#define LIST_FBINOP(name, id, hsop)
};

#define ENTRY_FBINARY_STRIDED_OPS(typ) \
  void oxarop_fbinary_ ## typ ## _sv_strided(enum fbinop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, typ x, const i64 *strides, const typ *y) { \
    switch (tag) { \
      case FB_DIV: oxarop_op_fdiv_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      case FB_POW: oxarop_op_pow_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      case FB_LOGBASE: oxarop_op_logbase_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      case FB_ATAN2: oxarop_op_atan2_ ## typ ## _sv_strided(rank, shape, out, x, strides, y); break; \
      default: wrong_op("fbinary_sv_strided", tag); \
    } \
  } \
  void oxarop_fbinary_ ## typ ## _vs_strided(enum fbinop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, const i64 *strides, const typ *x, typ y) { \
    switch (tag) { \
      case FB_DIV: oxarop_op_fdiv_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      case FB_POW: oxarop_op_pow_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      case FB_LOGBASE: oxarop_op_logbase_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      case FB_ATAN2: oxarop_op_atan2_ ## typ ## _vs_strided(rank, shape, out, strides, x, y); break; \
      default: wrong_op("fbinary_vs_strided", tag); \
    } \
  } \
  void oxarop_fbinary_ ## typ ## _vv_strided(enum fbinop_tag_t tag, i64 rank, const i64 *shape, typ *restrict out, const i64 *strides1, const typ *x, const i64 *strides2, const typ *y) { \
    switch (tag) { \
      case FB_DIV: oxarop_op_fdiv_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      case FB_POW: oxarop_op_pow_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      case FB_LOGBASE: oxarop_op_logbase_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      case FB_ATAN2: oxarop_op_atan2_ ## typ ## _vv_strided(rank, shape, out, strides1, x, strides2, y); break; \
      default: wrong_op("fbinary_vv_strided", tag); \
    } \
  }

enum unop_tag_t {
#undef LIST_UNOP
#define LIST_UNOP(name, id, _) name = id,
#include "arith_lists.h"
#undef LIST_UNOP
#define LIST_UNOP(name, id, _)
};

#define ENTRY_UNARY_STRIDED_OPS(typ) \
  void oxarop_unary_ ## typ ## _strided(enum unop_tag_t tag, i64 rank, typ *restrict out, const i64 *shape, const i64 *strides, const typ *x) { \
    switch (tag) { \
      case UO_NEG: oxarop_op_neg_ ## typ ## _strided(rank, out, shape, strides, x); break; \
      case UO_ABS: oxarop_op_abs_ ## typ ## _strided(rank, out, shape, strides, x); break; \
      case UO_SIGNUM: oxarop_op_signum_ ## typ ## _strided(rank, out, shape, strides, x); break; \
      default: wrong_op("unary_strided", tag); \
    } \
  }

enum funop_tag_t {
#undef LIST_FUNOP
#define LIST_FUNOP(name, id, _) name = id,
#include "arith_lists.h"
#undef LIST_FUNOP
#define LIST_FUNOP(name, id, _)
};

#define ENTRY_FUNARY_STRIDED_OPS(typ) \
  void oxarop_funary_ ## typ ## _strided(enum funop_tag_t tag, i64 rank, typ *restrict out, const i64 *shape, const i64 *strides, const typ *x) { \
    switch (tag) { \
      case FU_RECIP:    oxarop_op_recip_    ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_EXP:      oxarop_op_exp_      ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_LOG:      oxarop_op_log_      ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_SQRT:     oxarop_op_sqrt_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_SIN:      oxarop_op_sin_      ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_COS:      oxarop_op_cos_      ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_TAN:      oxarop_op_tan_      ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_ASIN:     oxarop_op_asin_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_ACOS:     oxarop_op_acos_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_ATAN:     oxarop_op_atan_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_SINH:     oxarop_op_sinh_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_COSH:     oxarop_op_cosh_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_TANH:     oxarop_op_tanh_     ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_ASINH:    oxarop_op_asinh_    ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_ACOSH:    oxarop_op_acosh_    ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_ATANH:    oxarop_op_atanh_    ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_LOG1P:    oxarop_op_log1p_    ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_EXPM1:    oxarop_op_expm1_    ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_LOG1PEXP: oxarop_op_log1pexp_ ## typ ## _strided(rank, out, shape, strides, x); break; \
      case FU_LOG1MEXP: oxarop_op_log1mexp_ ## typ ## _strided(rank, out, shape, strides, x); break; \
      default: wrong_op("funary_strided", tag); \
    } \
  }

enum redop_tag_t {
#undef LIST_REDOP
#define LIST_REDOP(name, id, _) name = id,
#include "arith_lists.h"
#undef LIST_REDOP
#define LIST_REDOP(name, id, _)
};

#define ENTRY_REDUCE1_OPS(typ) \
  void oxarop_reduce1_ ## typ(enum redop_tag_t tag, i64 rank, typ *restrict out, const i64 *shape, const i64 *strides, const typ *arr) { \
    switch (tag) { \
      case RO_SUM: oxarop_op_sum1_ ## typ(rank, out, shape, strides, arr); break; \
      case RO_PRODUCT: oxarop_op_product1_ ## typ(rank, out, shape, strides, arr); break; \
      default: wrong_op("reduce", tag); \
    } \
  }

#define ENTRY_REDUCEFULL_OPS(typ) \
  typ oxarop_reducefull_ ## typ(enum redop_tag_t tag, i64 rank, const i64 *shape, const i64 *strides, const typ *arr) { \
    switch (tag) { \
      case RO_SUM: return oxarop_op_sumfull_ ## typ(rank, shape, strides, arr); \
      case RO_PRODUCT: return oxarop_op_productfull_ ## typ(rank, shape, strides, arr); \
      default: wrong_op("reduce", tag); \
    } \
  }


/*****************************************************************************
 *                        Generate all the functions                         *
 *****************************************************************************/

#define INT_TYPES_XLIST X(i8) X(i16) X(i32) X(i64)
#define FLOAT_TYPES_XLIST X(double) X(float)
#define NUM_TYPES_XLIST INT_TYPES_XLIST FLOAT_TYPES_XLIST

#define X(typ) \
  COMM_OP_STRIDED(add, +, typ) \
  NONCOMM_OP_STRIDED(sub, -, typ) \
  COMM_OP_STRIDED(mul, *, typ) \
  UNARY_OP_STRIDED(neg, -, typ) \
  UNARY_OP_STRIDED(abs, GEN_ABS, typ) \
  UNARY_OP_STRIDED(signum, GEN_SIGNUM, typ) \
  REDUCE1_OP(sum1, +, typ) \
  REDUCE1_OP(product1, *, typ) \
  REDUCEFULL_OP(sumfull, +, typ) \
  REDUCEFULL_OP(productfull, *, typ) \
  ENTRY_BINARY_STRIDED_OPS(typ) \
  ENTRY_UNARY_STRIDED_OPS(typ) \
  ENTRY_REDUCE1_OPS(typ) \
  ENTRY_REDUCEFULL_OPS(typ) \
  EXTREMUM_OP(min, <, typ) \
  EXTREMUM_OP(max, >, typ) \
  DOTPROD_INNER_OP(typ)
NUM_TYPES_XLIST
#undef X

#define X(typ) \
  NONCOMM_OP_STRIDED(quot, /, typ) \
  NONCOMM_OP_STRIDED(rem, %, typ) \
  ENTRY_IBINARY_STRIDED_OPS(typ)
INT_TYPES_XLIST
#undef X

#define X(typ) \
  NONCOMM_OP_STRIDED(fdiv, /, typ) \
  PREFIX_BINOP_STRIDED(pow, GEN_POW, typ) \
  PREFIX_BINOP_STRIDED(logbase, GEN_LOGBASE, typ) \
  PREFIX_BINOP_STRIDED(atan2, GEN_ATAN2, typ) \
  UNARY_OP_STRIDED(recip, 1.0/, typ) \
  UNARY_OP_STRIDED(exp, GEN_EXP, typ) \
  UNARY_OP_STRIDED(log, GEN_LOG, typ) \
  UNARY_OP_STRIDED(sqrt, GEN_SQRT, typ) \
  UNARY_OP_STRIDED(sin, GEN_SIN, typ) \
  UNARY_OP_STRIDED(cos, GEN_COS, typ) \
  UNARY_OP_STRIDED(tan, GEN_TAN, typ) \
  UNARY_OP_STRIDED(asin, GEN_ASIN, typ) \
  UNARY_OP_STRIDED(acos, GEN_ACOS, typ) \
  UNARY_OP_STRIDED(atan, GEN_ATAN, typ) \
  UNARY_OP_STRIDED(sinh, GEN_SINH, typ) \
  UNARY_OP_STRIDED(cosh, GEN_COSH, typ) \
  UNARY_OP_STRIDED(tanh, GEN_TANH, typ) \
  UNARY_OP_STRIDED(asinh, GEN_ASINH, typ) \
  UNARY_OP_STRIDED(acosh, GEN_ACOSH, typ) \
  UNARY_OP_STRIDED(atanh, GEN_ATANH, typ) \
  UNARY_OP_STRIDED(log1p, GEN_LOG1P, typ) \
  UNARY_OP_STRIDED(expm1, GEN_EXPM1, typ) \
  UNARY_OP_STRIDED(log1pexp, GEN_LOG1PEXP, typ) \
  UNARY_OP_STRIDED(log1mexp, GEN_LOG1MEXP, typ) \
  ENTRY_FBINARY_STRIDED_OPS(typ) \
  ENTRY_FUNARY_STRIDED_OPS(typ)
FLOAT_TYPES_XLIST
#undef X

// Note: [zero-length VLA]
//
// Zero-length variable-length arrays are not allowed in C(99). Thus whenever we
// have a VLA that could sometimes suffice to be empty (e.g. `idx` in the
// TARRAY_WALK_NOINNER macros), we tweak the length formula (typically by just
// adding 1) so that it never ends up empty.
