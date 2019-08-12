
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <gmp.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

/* To only search a subset of the search space, we start at
 * BEGINOFF+1 and end at ENDOFF */
#define BEGINOFF 0
#define ENDOFF 9999
//int initc[256] = {1,2,3,4,5,6,7,8,9,10};
int initc[256] = {0};

/* moduli that work well seem to be 17, 19, 23
 * 13 seems to be too small, large primes mean large
 * lookup table which means cache misses, the modulus
 * should not divide the degree or we're almost always
 * fail through to the full integer rref */
#define MODP1 23

#define FALSE 0
#define TRUE (!FALSE)

#define MIN(A,B) ((A<B)?A:B)

/* to use 64 bits also change %ld to %Ld */
#define ntype long long

//#include "rref-d9.h"
//#include "rref-d11.h"
//#include "rref-d13.h"
#include "rref-d15.h"
//#include "rref-d17.h"
//#include "rref-d19.h"
//#include "rref-d21.h"

int purex[DEGREE-1];
int purey[DEGREE-1];
#define UNREACHABLES ((DEGREE-3)/2)
int unreachable[UNREACHABLES];

/* this is without the last column */
#define LOGCOLS (COLS-2*(DEGREE-1)-UNREACHABLES-1)

int tr[LOGCOLS+1];

int degx[LOGCOLS+1];
int degy[LOGCOLS+1];

//int upleft[LOGCOLS+1];
//int upright[LOGCOLS+1];

/* +1 if right side, -1 if left side 0 if middle */
int rsvec[LOGCOLS+1];


#define TARGETN (((DEGREE+3)/2)+((DEGREE+3)%2))

#define ROWS1 (ROWS-2)
#define COLS1 (TARGETN-2+1)
unsigned int mm3[ROWS1][COLS1];
unsigned int mm31[ROWS][COLS];
__mpz_struct mm4[ROWS1][COLS1];
unsigned int mbit[COLS+1]; /* 1 indexed! */
unsigned int mmod2[COLS+1]; /* 1 indexed! */
unsigned int mmod2m[COLS1];

#if ROWS1 == 8 /* deg 9 */
#define FULLROWS 0xff
#elif ROWS1 == 10 /* deg 11 */
#define FULLROWS 0x3ff
#elif ROWS1 == 12 /* deg 13 */
#define FULLROWS 0xfff
#elif ROWS1 == 14 /* deg 15 */
#define FULLROWS 0x3fff
#elif ROWS1 == 16 /* deg 17 */
#define FULLROWS 0xffff
#elif ROWS1 == 18 /* deg 19 */
#define FULLROWS 0x3ffff
#elif ROWS1 == 20 /* deg 21 */
#define FULLROWS 0xfffff
#else
#error "no FULLROWS!"
#endif

/* The current place */
int c[TARGETN-2] = {0};
int trc[TARGETN-2] = {0};

/* tables for x,y,a,b -> xb-ya mod MODP1? */
static int tblP1[MODP1][MODP1][MODP1][MODP1];

static void
precompute_mod_tblP1 (void)
{
	int i, j, k, l;

	for (i=0; i < MODP1; i++)
		for (j=0; j < MODP1; j++)
			for (k=0; k < MODP1; k++)
				for (l=0; l < MODP1; l++)
					tblP1[i][j][k][l] = (i*l+(MODP1-1)*j*k)%MODP1;
}

static void
precompute_mod_matrixP1(unsigned int m2[ROWS][COLS], ntype m[ROWS][COLS])
{
	int i, j;

	for (i=0; i < ROWS; i++) {
		for (j=0; j < COLS; j++) {
			ntype e = m[i][j];
			if (e != 0) {
				while (e < 0) {
					e += MODP1;
				}
			}
			m2[i][j] = e % MODP1;
		}
	}
}

/* note that mmod2 is 1 indexed */
static void
precompute_mod_matrix_mod2(unsigned int mmod2[COLS], ntype m[ROWS][COLS])
{
	int i, j;

	/* hmmm */
	mmod2[0] = 0;

	for (j = 1; j <= COLS; j++) {
		mmod2[j] = 0;
		/* ONLY nonpure rows */
		for (i=1; i < ROWS-1; i++) {
			ntype e = m[i][j-1];
			if ((e % 2) == 1 ||
			    (e % 2) == -1) {
				mmod2[j] |= (1<<(i-1));
			}
		}
	}
}

static void
swap_rows_mod (unsigned int m[ROWS1][COLS1], int r1, int r2)
{
	unsigned int tmp[COLS1];

	memcpy(tmp, m[r1], sizeof(unsigned int)*COLS1);
	memcpy(m[r1], m[r2], sizeof(unsigned int)*COLS1);
	memcpy(m[r2], tmp, sizeof(unsigned int)*COLS1);
}

static int
mod2_ref_is_full_rank (void)
{
	int i, j, d;

	/* note that mmod2 is 1 indexed */
	for (j = 0; j < TARGETN-2; j++) {
		mmod2m[j] = mmod2[trc[j]];
	}
	/* tack on the last column */
	mmod2m[TARGETN-2] = mmod2[COLS];

	d = 0;
	for (j = 0; j < ROWS1; j++) {
		for (i = d; i < COLS1; i++) {
			if (((mmod2m[i]) & (1<<j)) != 0) break;
		}

		if (i == COLS1) {
			continue;

		} else if ((d+1) == MIN(ROWS1,COLS1)) {
			return TRUE;

		} else if (i > d) {
			unsigned int tmp;

			tmp = mmod2m[i];
			mmod2m[i] = mmod2m[d];
			mmod2m[d] = tmp;
		}


		for (i = d+1; i < COLS1; i++) {
			if (((mmod2m[i]) & (1<<j)) != 0) {
				mmod2m[i] ^= mmod2m[d];
			}
		}

		d++;
	}

	return FALSE;
}

static int
modP1_ref_is_full_rank (unsigned int m[ROWS1][COLS1])
{
	int i, j, k, d;
	unsigned int x, y;

	d = 0;
	for (j = 0; j < COLS1; j++) {
		for (i = d; i < ROWS1; i++) {
			if (m[i][j] != 0) break;
		}

		if (i == ROWS1) {
			return FALSE;
		} else if ((d+1) == MIN(ROWS1,COLS1)) {
			/* no need to do the last steps, we are done! */
			return TRUE;
		} else if (i > d) {
			swap_rows_mod (m, i, d);
		}

		x = m[d][j];

		for (i = d+1; i < ROWS1; i++) {
			y = m[i][j];

			if (y != 0) {
				m[i][j] = 0;
				for (k = j+1; k < COLS1; k++) {
					m[i][k] =
						tblP1[x][y][m[d][k]][m[i][k]];
						/* (x*m[i][k] + (MODP1-1)* y*m[d][k]) % MODP1; */
				}
			}
		}

		d++;
	}

	/* found pivots on all columns, full rank */
	return TRUE;
}

typedef struct {
	int pivr[COLS1];
	int pivc[COLS1];
	int pivots;
} PivotsType;

static void
swap_rows_gmp (__mpz_struct m[ROWS1][COLS1], int r1, int r2)
{
	__mpz_struct tmp[COLS1];

	memcpy(tmp, m[r1], sizeof(__mpz_struct)*COLS1);
	memcpy(m[r1], m[r2], sizeof(__mpz_struct)*COLS1);
	memcpy(m[r2], tmp, sizeof(__mpz_struct)*COLS1);
}

static int
gmp_int_rref (__mpz_struct m[ROWS1][COLS1], PivotsType *p,
	      int dim_one_only)
{
	int i, j, k, l, d;
	int mg_set;
	int mg_one;
	mpz_t mg;
	mpz_t tmp;
	mpz_t x;
	mpz_t y;

	p->pivots = 0;

	mpz_init (mg);
	mpz_init (tmp);
	mpz_init (x);
	mpz_init (y);

	d = 0;
	for (j = 0; j < COLS1; j++) {
		for (i = d; i < ROWS1; i++) {
			if (mpz_sgn (&(m[i][j])) != 0) break;
		}

		if (i == ROWS1) {
			continue;
		} else if (i > d) {
			swap_rows_gmp (m, i, d);
		}

		p->pivr[p->pivots] = d;
		p->pivc[p->pivots] = j;
		p->pivots++;

		/* x is the pivot */
		mpz_set (x, &(m[d][j]));

		for (i = d+1; i < ROWS1; i++) {
			if (mpz_sgn (&(m[i][j])) == 0) continue;

			mpz_set (y, &(m[i][j]));

			mg_set = FALSE;
			mg_one = FALSE;

			mpz_set_ui (&(m[i][j]), 0);
			for (k = j+1; k < COLS1; k++) {
				mpz_mul (&(m[i][k]), x, &(m[i][k]));
				mpz_mul (tmp, y, &(m[d][k]));
				mpz_sub (&(m[i][k]), &(m[i][k]), tmp);

				if (mpz_sgn (&(m[i][k])) != 0 &&
				    ! mg_one) {
					if ( ! mg_set) {
						mpz_abs (mg, &(m[i][k]));
						mg_set = TRUE;
					} else {
						mpz_abs (tmp, &(m[i][k]));
						mpz_gcd (mg, mg, tmp);
					}
					if (mpz_cmp_ui (mg, 1) == 0)
						mg_one = TRUE;
				}
			}

			if (mg_set && ! mg_one) {
				for (k = j+1; k < COLS1; k++) {
					mpz_divexact (&(m[i][k]),
						      &(m[i][k]),
						      mg);
				}
			}
		}

		d++;
	}

	if (dim_one_only && (COLS1 - p->pivots) != 1) {
		mpz_clear (mg);
		mpz_clear (tmp);
		mpz_clear (x);
		mpz_clear (y);
		return FALSE;
	}

	for (l = 0; l < p->pivots; l++) {
		d = p->pivr[l];
		j = p->pivc[l];

		mpz_set (x, &(m[d][j]));
		for (i = d-1; i >= 0; i--) {
			if (mpz_sgn (&(m[i][j])) == 0) continue;

			mpz_set (y, &(m[i][j]));

			for (k = 0; k < j; k++) {
				mpz_mul (&(m[i][k]), x, &(m[i][k]));
			}
			mpz_set_ui (&(m[i][j]), 0);
			for (k = j+1; k < COLS1; k++) {
				mpz_mul (&(m[i][k]), x, &(m[i][k]));
				mpz_mul (tmp, y, &(m[d][k]));
				mpz_sub (&(m[i][k]), &(m[i][k]), tmp);
			}
		}
	}

	mpz_clear (mg);
	mpz_clear (tmp);
	mpz_clear (x);
	mpz_clear (y);
	return TRUE;
}

static int
gmp_null_vector (__mpz_struct m[ROWS1][COLS1], __mpz_struct *v, PivotsType *p)
{
	int k, i, jj;
	__mpz_struct ty[COLS1];
	mpz_t my;
	mpz_t a;
	mpz_t b;
	mpz_t g;

	for (i = 0; i < COLS1; i++)
		mpz_init (&(ty[i]));
	mpz_init (my);
	mpz_init (a);
	mpz_init (b);
	mpz_init (g);

	/* loop over nonpivots */
	jj = 0;
	for (k = 0; k < COLS1; k++) {
		/* skip pivots */
		if (jj < p->pivots &&
		    k == p->pivc[jj]) {
			jj++;
			continue;
		}

		for (i = 0; i < COLS1; i++) {
			mpz_set_ui (&(v[i]), 0);
			mpz_set_ui (&(ty[i]), 0);
		}
		
		mpz_set_ui (my, 1);

		for (i = 0; i < p->pivots; i++) {
			int pc = p->pivc[i];
			int pr = p->pivr[i];

			mpz_abs (a, &(m[pr][pc]));
			mpz_abs (b, &(m[pr][k]));
			mpz_gcd (g, a, b);
			mpz_divexact (a, &(m[pr][k]), g);
			mpz_divexact (b, &(m[pr][pc]), g);

			if (mpz_sgn (b) < 0) {
				mpz_neg (b, b);
				mpz_neg (a, a);
			}

			mpz_lcm (my, my, b);
			mpz_neg (&(v[pc]), a);
			mpz_set (&(ty[pc]), b);
		}

		mpz_set (&(v[k]), my);

		for (i = 0; i < p->pivots; i++) {
			int pc = p->pivc[i];
			mpz_mul (&(v[pc]), &(v[pc]), my);
			mpz_div (&(v[pc]), &(v[pc]), &(ty[pc]));
		}

		for (i = 0; i < COLS1; i++)
			mpz_clear (&(ty[i]));
		mpz_clear (my);
		mpz_clear (a);
		mpz_clear (b);
		mpz_clear (g);

		return TRUE;
	}

	for (i = 0; i < COLS1; i++)
		mpz_clear (&(ty[i]));
	mpz_clear (my);
	mpz_clear (a);
	mpz_clear (b);
	mpz_clear (g);

	return FALSE;
}

static int
comb_get_next_combination (int *vec, int len, int n)
{
	int i = len;
	int j;

	while (i > 0 && vec[i-1] == n-(len-i)) {
		i--;
	}
	if (__builtin_expect (i == 0, 0)) {
	//if (i == 0) {
		return FALSE;
	} else {
		vec[i-1] ++;
		for (j = i+1; j <= len; j++)
			vec[j-1] = vec[j-2]+1;
	}
	return TRUE;
}

static void
comb_get_random_combination (int *vec, int len, int n)
{
	int i;
	int sorted;

	for (i = 0; i < len; i++) {
		int j, k;
find_new_one:
		k = ((rand () >> 2) % n) + 1;

		for (j = 0; j < i; j++) {
			if (k == vec[j])
				goto find_new_one;
		}

		vec[i] = k;
	}

	/* this is very very unoptimal, but how many times do
	 * we do it ... and only for testing */
	sorted = 0;
	while ( ! sorted) {
		sorted = 1;
		for (i = 0; i < len-1; i++) {
			if (vec[i] > vec[i+1]) {
				int tmp;
				sorted = 0;
				tmp = vec[i];
				vec[i] = vec[i+1];
				vec[i+1] = tmp;
			}
		}
	}
}

/* note that mbit is 1 indexed */
static int
get_the_bitmap_matrix (unsigned int mbit[COLS+1], ntype m[ROWS][COLS])
{
	int i, j;

	/* hmmm */
	mbit[0] = 0;

	for (j = 1; j <= COLS; j++) {
		mbit[j] = 0;
		/* only do the nonpure rows */
		for (i = 1; i < ROWS-1; i++) {
			if (m[i][j-1] != 0) {
				mbit[j] |= (1<<(i-1));
			}
		}
	}
	return TRUE;
}

static void
get_the_modP1_submatrix (unsigned int m2[ROWS1][COLS1], unsigned int pm[ROWS][COLS])
{
	int i, j;
	
	/* use columns from the column list */
	for (i = 0; i < ROWS-2; i++) {
		for (j = 0; j < TARGETN-2; j++) {
			m2[i][j] = pm[i+1][trc[j]-1];
		}
		/* tack on the last column, that is always positive */
		m2[i][TARGETN-2] = pm[i+1][COLS-1];
	}
}

static int
gmp_get_the_submatrix (__mpz_struct m2[ROWS1][COLS1], ntype m[ROWS][COLS])
{
	int i, j;
	
	/* use columns from the column list */
	for (i = 0; i < ROWS-2; i++) {
		//int isnull = TRUE;
		for (j = 0; j < TARGETN-2; j++) {
			int cc = trc[j]-1;
			mpz_set_si (&(m2[i][j]), m[i+1][cc]);
			//if (m2[i][j] != 0) isnull = FALSE;
		}
		//if (isnull)
			//return FALSE;
		/* tack on the last column */
		mpz_set_si (&(m2[i][TARGETN-2]), m[i+1][COLS-1]);
	}
	return TRUE;
}

static int
gmp_vector_nonnegative (__mpz_struct v[], int len)
{
	int i;
	for (i = 0; i < len; i++) {
		if (mpz_sgn (&(v[i])) < 0)
			return FALSE;
	}
	return TRUE;
}

static int
gmp_vector_nonpositive (__mpz_struct v[], int len)
{
	int i;
	for (i = 0; i < len; i++) {
		if (mpz_sgn (&(v[i])) > 0)
			return FALSE;
	}
	return TRUE;
}

static int
check_pure_unreachable (int cc)
{
	int j;

	for (j=0; j < DEGREE-1; j++) {
		if (purex[j] == cc ||
		    purey[j] == cc)
			return TRUE;
	}
	for (j=0; j < UNREACHABLES; j++) {
		if (unreachable[j] == cc)
			return TRUE;
	}

	return FALSE;
}

#if 0
static int
checkadjacent (void)
{
	/* Note that since pures have been removed, adjacents are
	 * really adjacent and undoable, so we need not check them */
	int i;

	int cclast = c[0];

	/* This ought to be smarter, these are all sorted! */
	for (i=1; i < TARGETN-2; i++) {
		int cc = c[i];
		if (tr[cclast]+1 == tr[cc])
			return TRUE;
		cclast = cc;
	}
	return FALSE;
}
#endif

static int
checkupadjacent_and_adjust_full (void)
{
	int i;
	for (i=0; i < TARGETN-2-1; i++) {
		int j;
		int a = degx[c[i]];
		int b = degy[c[i]];
		for (j = i+1; j < TARGETN-2; j++) {
			int aa = degx[c[j]];
			int bb = degy[c[j]];
			if (aa + bb > a+b+1) {
				/*if (c[j] == upleft[c[i]] || c[j] == upright[c[i]]) {
					printf ("found upleft that's skipped by degree code\n");
				}*/
				break;
			} else if ((aa == a && bb == b+1) ||
				   (aa == a+1 && bb == b)) {
				int k = c[j];

				/*if (k != upleft[c[i]] && k!= upright[c[i]]) {
					printf ("found up left that's not in upleft %d %d %d x%d y%d (%d %d)\n", c[i], c[j], upleft[c[i]], a, b, aa, bb);
					exit(1);
				}*/

				if (k + TARGETN-2-j > LOGCOLS) {
					comb_get_next_combination (c, TARGETN-2, LOGCOLS);
					return TRUE;
				}
				/*printf ("PREFIXUP: ");
				for (i=0; i < TARGETN-2; i++) {
					printf ("%d ", c[i]);
				}*/
				for (; j < TARGETN-2; j++) {
					k++;
					c[j] = k;
				}
				/*
				printf ("\nPOST FIXUP : ");
				for (i=0; i < TARGETN-2; i++) {
					printf ("%d ", c[i]);
				}
				printf ("\n");
				*/
				return TRUE;
			}
			/*
			if (c[j] == upleft[c[i]] || c[j] == upright[c[i]]) {
				printf ("found upleft that's not found by the code\n");
				printf ("---- %d %d %d x%d y%d (%d %d)\n", c[i], c[j], upleft[c[i]], a, b, aa, bb);
			}
			*/
		}
	}
	return FALSE;
}

#if 0
static int
checkupadjacent_and_adjust_full_newslow (void)
{
	int i;
	for (i=0; i < TARGETN-2-1; i++) {
		int j;
		int ul = upleft[c[i]];
		int ur = upright[c[i]];
		if (ul < 0 && ur < 0) 
			return FALSE;
		for (j = i+1; j < TARGETN-2; j++) {
			int k = c[j];
			if (ul == k || ur == k) {
				if (k + TARGETN-2-j > LOGCOLS) {
					comb_get_next_combination (c, TARGETN-2, LOGCOLS);
					return TRUE;
				}
				for (; j < TARGETN-2; j++) {
					k++;
					c[j] = k;
				}
				return TRUE;
			} else if (ul < k && ur < k) {
				break;
			}
		}
	}
	return FALSE;
}
#endif

static int
checkupadjacent_and_adjust (void)
{
	int i;
	for (i=0; i < TARGETN-2-1; i++) {
		int a = degx[c[i]];
		int b = degy[c[i]];
		int aa = degx[c[i+1]];
		int bb = degy[c[i+1]];
		if ((aa == a && bb == b+1) ||
		    (aa == a+1 && bb == b)) {
			i++;
			int k = c[i];
			if (k + TARGETN-2-i > LOGCOLS) {
				comb_get_next_combination (c, TARGETN-2, LOGCOLS);
				return TRUE;
			}
			for (; i < TARGETN-2; i++) {
				k++;
				c[i] = k;
			}
			return TRUE;
		}
	}
	return FALSE;
}

static int
checkupadjacent_andrightsideheavy_and_adjust (void)
{
	int i;
	int right = 0;
	int left = 0;
	int a;
	int b;
	for (i=0; i < TARGETN-2-1; i++) {
		a = degx[c[i]];
		b = degy[c[i]];
		int aa = degx[c[i+1]];
		int bb = degy[c[i+1]];
		if ((aa == a && bb == b+1) ||
		    (aa == a+1 && bb == b)) {
			i++;
			int k = c[i];
			if (k + TARGETN-2-i > LOGCOLS) {
				comb_get_next_combination (c, TARGETN-2, LOGCOLS);
				return TRUE;
			}
			for (; i < TARGETN-2; i++) {
				k++;
				c[i] = k;
			}
			return 1;
		}
		if (a > b)
			left++;
		else if (b > a)
			right++;
	}

	a = degx[c[i]];
	b = degy[c[i]];
	if (a > b)
		left++;
	else if (b > a)
		right++;
	if (right > left) {
		return 2;
	} else {
		return 0;
	}
}

static void
precompute_right_side_vector (void)
{
	int i;
	for (i=1; i <= LOGCOLS; i++) {
		int a = degx[i];
		int b = degy[i];
		if (a > b)
			/* left side */
			rsvec[i] = -1;
		else if (b > a)
			/* right side */
			rsvec[i] = 1;
		else
			rsvec[i] = 0;
	}
}

#if 0
static void
precompute_upleftright_vector (void)
{
	int i;
	int j;
	for (i=1; i <= LOGCOLS; i++) {
		int a = degx[i];
		int b = degy[i];
		upleft[i] = -1;
		upright[i] = -1;
		for (j=i+1; j <= LOGCOLS; j++) {
			int aa = degx[j];
			int bb = degy[j];
			if (aa == a+1 && bb == b) {
				//printf ("ul: %d %d\n", i, j);
				upleft[i] = j;
			}
			if (aa == a && bb == b+1) {
				//printf ("ur: %d %d\n", i, j);
				upright[i] = j;
			}
		}
		/*if (upleft[i] == -1) {
			printf ("ul: %d %d\n", i, -1);
		}
		if (upright[i] == -1) {
			printf ("ur: %d %d\n", i, -1);
		}*/
	}
}
#endif

static int
is_right_side_heavy_old (void)
{
	int i;
	int right = 0;
	int left = 0;
	for (i=0; i < TARGETN-2; i++) {
		int a = degx[c[i]];
		int b = degy[c[i]];
		if (a > b)
			left++;
		else if (b > a)
			right++;
	}
	if (right > left) {
		/* by this time the last guy in c is in degree d-1.  If we move this anymore
		   to the right it will just be more and more right side heavy, so just
		   move it all the way to the end so that next_combination will move the
		   c[TARGETN-2-2] guy */
		c[TARGETN-2-1] = LOGCOLS;
		return TRUE;
	} else {
		return FALSE;
	}
	//return right > left;
}

static int
is_right_side_heavy (void)
{
	int sum = 0;
	int i;
	for (i=0; i < TARGETN-2; i++) {
		sum += rsvec[c[i]];
	}
	if (sum > 0) {
		/* by this time the last guy in c is in degree d-1.  If we move this anymore
		   to the right it will just be more and more right side heavy, so just
		   move it all the way to the end so that next_combination will move the
		   c[TARGETN-2-2] guy */
		c[TARGETN-2-1] = LOGCOLS;
		return TRUE;
	} else {
		return FALSE;
	}
	//return right > left;
}

static int
is_simplesym (void)
{
	int sum = 0;
	int i;
	for (i=0; i < TARGETN-2; i++) {
		sum += rsvec[c[i]];
	}
	if (sum > 0) {
		/* by this time the last guy in c is in degree d-1.  If we move this anymore
		   to the right it will just be more and more right side heavy, so just
		   move it all the way to the end so that next_combination will move the
		   c[TARGETN-2-2] guy */
		c[TARGETN-2-1] = LOGCOLS;
		return FALSE;
	} else if(sum < 0) {
		return FALSE;
	} else {
		return TRUE;
	}
	//return right > left;
}

static int
fixup_combination (void)
{
	/* Note that since pures have been removed, adjacents are
	 * really adjacent and undoable, so we need not check them */
	int i;

	int cclast = c[0];

	/* This ought to be smarter, these are all sorted! */
	for (i=1; i < TARGETN-2; i++) {
		int cc = c[i];
		if (tr[cclast]+1 == tr[cc]) {
			int j;
			cc++;
			/* We find where we are adjacent and now make up the next reasonable combination */
			for (j = i; j < TARGETN-2; j++) {
				if (cc > LOGCOLS) {
					printf ("Detected end in fixup\n");
					return FALSE; /* no more combinations */
				}
				c[j] = cc;
				cclast = cc;
				cc++;
				if (cc <= LOGCOLS && tr[cclast]+1 == tr[cc])
					cc++;
			}

			return TRUE;
		}
		cclast = cc;
	}

	/* should never happen */
	return TRUE;
}

static int
is_symmetric(void)
{
	int i, j, found, xd, yd, tdeg;
	for (i = 0; i < TARGETN-2-1; i++) {
		if (degx[c[i]] == degy[c[i]])
			continue;
		else if (degx[c[i]] < degy[c[i]])
			continue;
		else {
			xd = degx[c[i]];
			yd = degy[c[i]];
			found = 0;
			for (j = i+1; j < TARGETN-2 && (degx[c[j]]+degy[c[j]]) == (xd+yd); j++) {
				if (xd == degy[c[j]] && yd == degx[c[j]]) {
					found = 1;
					break;
				}
			}
			if ( ! found)
				return FALSE;
		}

	}
	return TRUE;
}

int
main (void)
{
	int i, j;
	PivotsType p;
	__mpz_struct v[TARGETN-2+1];
	int cnt = 0;
	int startof_dminusone;
	int startof_dminusone_c;
	long long allcnt = 0;
	long long notopcnt = 0;
	long long adjcnt = 0;
	long long adjupcnt = 0;
	long long nonsymcnt = 0;
	long long nrowcnt = 0;
	long long modP1fullrankcnt = 0;
	long long mod2fullrankcnt = 0;
	long long rightsideheavycnt = 0;
	long long simplesymcnt = 0;
	long long finalcnt = 0;
	struct timeval t0;
	struct timeval t00;
	struct timeval t1;

	j=0;
	for (i=0; i < COLS-1; i++) {
		if (mm[0][i] != 0) {
			purex[j++] = i+1;
			printf ("%d ", i+1);
		}
	}

	startof_dminusone = purex[DEGREE-2];

	printf ("\nun: ");
	j = startof_dminusone+2;
	for (i=0; i < UNREACHABLES; i++) {
		unreachable[i] = j;
		printf ("%d ", j);
		j += 2;
	}
	printf ("\n");

	j=0;
	for (i=0; i < COLS-1; i++) {
		if (mm[ROWS-1][i] != 0) {
			purey[j++] = i+1;
			printf ("%d ", i+1);
		}
	}

	printf ("\n");

	printf ("tr(%d vs %d): ", LOGCOLS, COLS-1);
	j=1;
	for (i=0; i < LOGCOLS; i++) {
		while (check_pure_unreachable (j))
			j++;
		tr[i+1] = j;
		printf ("%d ", j);
		j++;
	}
	printf ("\n");

	startof_dminusone_c = 1;
	while (tr[startof_dminusone_c] < startof_dminusone)
		startof_dminusone_c ++;

	printf ("STARTOF D-1 %d (%d)\n", startof_dminusone, startof_dminusone_c);

	/* This is suboptimal but we only do it once */
	for (i=0; i < LOGCOLS; i++) {
		int thecol = tr[i+1];
		int ii = 1;
		for (j=1; j < DEGREE; j++) {
			int k;
			for (k=0; k <= j; k++) {
				if (ii == thecol) {
					degx[i+1] = j-k;
					degy[i+1] = k;
					j = DEGREE;
					k = DEGREE;
				}
				ii++;
			}
		}
	}
	printf ("The monomials:");
	for (i=0; i < LOGCOLS; i++) {
		printf (" (%d:%d)x^%dy^%d", tr[i+1], i+1, degx[i+1], degy[i+1]);
	}
	printf("\n");

	for (i=0; i < TARGETN-2; i++)
		c[i] = i+1+BEGINOFF;

	if (initc[0] > 0) {
		for (i=0; i < TARGETN-2; i++)
			c[i] = initc[i];
	}

	for (i=0; i < TARGETN-2+1; i++)
		mpz_init (&(v[i]));
	for (i = 0; i < ROWS1; i++) {
		for (j = 0; j < COLS1; j++) {
			mpz_init (&(mm4[i][j]));
		}
	}

	precompute_mod_tblP1 ();
	precompute_mod_matrixP1 (mm31, mm);
	precompute_mod_matrix_mod2 (mmod2, mm);
	precompute_right_side_vector ();
	//precompute_upleftright_vector ();

	get_the_bitmap_matrix (mbit, mm);

	/* sanity check */
	{
		unsigned int e = 0;
		for (i = 0; i < ROWS1; i++) {
			e |= (1<<i);
		}
		if (e != FULLROWS) {
			printf ("FULLROWS IS WRONG!\n");
			exit (1);
		}
	}

	/* for testing */
	if (getenv ("DORANDOM") != NULL) {
		srand (time (NULL) ^ getpid ());
		comb_get_random_combination (c, TARGETN-2, LOGCOLS);
#ifdef ENDOFF
		if (c[0] > ENDOFF)
			c[0] = ENDOFF;
#endif
	}

	printf("   starting at: ");
	for (i = 0; i < TARGETN-2; i++) {
		printf ("%d", tr[c[i]]);
		if (i < TARGETN-2-1)
			printf (",");
	}
	printf("   (");
	for (i = 0; i < TARGETN-2; i++) {
		printf ("%d", c[i]);
		if (i < TARGETN-2-1)
			printf (",");
	}
	printf("\n");

	fflush(stdout);

	j = 0;

	gettimeofday(&t0, 0);
	t00 = t0;

	/* Assuming x^d+y^d */
	do {
do_loop_again_with_new_combination:
#ifdef ENDOFF
		if (__builtin_expect(c[0] > ENDOFF, 0))
			break;
#endif
		allcnt ++;

		/* must include one term of degree d-1 */
		if (c[TARGETN-2-1] < startof_dminusone_c) {
			notopcnt++;
			c[TARGETN-2-1] = startof_dminusone_c;
		}

		if ( ! is_simplesym ()) {
			simplesymcnt++;
			continue;
		}


		/* Must not include any adjacent terms
		 * such polynomials are not optional */
#if (TARGETN-2) == 4
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]))
#elif (TARGETN-2) == 5
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]) ||
		    trc[3]+1 == (trc[4] = tr[c[4]]))
#elif (TARGETN-2) == 6
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]) ||
		    trc[3]+1 == (trc[4] = tr[c[4]]) ||
		    trc[4]+1 == (trc[5] = tr[c[5]]))
#elif (TARGETN-2) == 7
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]) ||
		    trc[3]+1 == (trc[4] = tr[c[4]]) ||
		    trc[4]+1 == (trc[5] = tr[c[5]]) ||
		    trc[5]+1 == (trc[6] = tr[c[6]]))
#elif (TARGETN-2) == 8
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]) ||
		    trc[3]+1 == (trc[4] = tr[c[4]]) ||
		    trc[4]+1 == (trc[5] = tr[c[5]]) ||
		    trc[5]+1 == (trc[6] = tr[c[6]]) ||
		    trc[6]+1 == (trc[7] = tr[c[7]]))
#elif (TARGETN-2) == 9
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]) ||
		    trc[3]+1 == (trc[4] = tr[c[4]]) ||
		    trc[4]+1 == (trc[5] = tr[c[5]]) ||
		    trc[5]+1 == (trc[6] = tr[c[6]]) ||
		    trc[6]+1 == (trc[7] = tr[c[7]]) ||
		    trc[7]+1 == (trc[8] = tr[c[8]]))
#elif (TARGETN-2) == 10
		/* At the same time set trc */
		trc[0] = tr[c[0]];
		if (trc[0]+1 == (trc[1] = tr[c[1]]) ||
		    trc[1]+1 == (trc[2] = tr[c[2]]) ||
		    trc[2]+1 == (trc[3] = tr[c[3]]) ||
		    trc[3]+1 == (trc[4] = tr[c[4]]) ||
		    trc[4]+1 == (trc[5] = tr[c[5]]) ||
		    trc[5]+1 == (trc[6] = tr[c[6]]) ||
		    trc[6]+1 == (trc[7] = tr[c[7]]) ||
		    trc[7]+1 == (trc[8] = tr[c[8]]) ||
		    trc[8]+1 == (trc[9] = tr[c[9]]))
#else
#		error "adjacent check not defined.  Could use loop and checkadjacent function!"
		{
			int ii;
			for (ii = 0; ii < TARGETN-2; ii++) {
				trc[ii] = tr[c[ii]];
			}
		}
		if (checkadjacent ())
#endif
		{
			adjcnt++;
			if ( ! fixup_combination ())
				break;

			goto do_loop_again_with_new_combination;
		}

		/* all entries must affect the top degree terms */
		if ((mbit[trc[0]] |
#if (TARGETN-2) == 4
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
#elif (TARGETN-2) == 5
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
		     mbit[trc[4]] |
#elif (TARGETN-2) == 6
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
		     mbit[trc[4]] |
		     mbit[trc[5]] |
#elif (TARGETN-2) == 7
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
		     mbit[trc[4]] |
		     mbit[trc[5]] |
		     mbit[trc[6]] |
#elif (TARGETN-2) == 8
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
		     mbit[trc[4]] |
		     mbit[trc[5]] |
		     mbit[trc[6]] |
		     mbit[trc[7]] |
#elif (TARGETN-2) == 9
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
		     mbit[trc[4]] |
		     mbit[trc[5]] |
		     mbit[trc[6]] |
		     mbit[trc[7]] |
		     mbit[trc[8]] |
#elif (TARGETN-2) == 10
		     mbit[trc[1]] |
		     mbit[trc[2]] |
		     mbit[trc[3]] |
		     mbit[trc[4]] |
		     mbit[trc[5]] |
		     mbit[trc[6]] |
		     mbit[trc[7]] |
		     mbit[trc[8]] |
		     mbit[trc[9]] |
#else
#error "fullrows check not done, could work without it though"
#endif
		     0x0) != FULLROWS) {
			nrowcnt ++;
			continue;
		}

		/*
		switch (checkupadjacent_andrightsideheavy_and_adjust ()) {
		case 1:
			adjupcnt++;
			goto do_loop_again_with_new_combination;
		case 2:
			rightsideheavycnt++;
			continue;
		default:
			;
		}
		*/

		/* more weight on the y terms, can ignore by symmetry */
		/* No need for this check, we are only checking symmetric */
		/*if (is_right_side_heavy ()) {
			rightsideheavycnt++;
			continue;
		}*/

		if ( ! is_symmetric ()) {
			nonsymcnt++;
			continue;
		}



		if (checkupadjacent_and_adjust_full ()) {
			adjupcnt++;
			goto do_loop_again_with_new_combination;
		}
		

		if (mod2_ref_is_full_rank ()) {
			mod2fullrankcnt ++;
			goto status_update;
		}

		get_the_modP1_submatrix (mm3, mm31);

		if (__builtin_expect(
		     modP1_ref_is_full_rank (mm3),
		     TRUE)) {
			modP1fullrankcnt++;
			goto status_update;
		}

		gmp_get_the_submatrix (mm4, mm);

		finalcnt++;

		if (gmp_int_rref (mm4, &p, TRUE /* dim_one_only */)) {
			gmp_null_vector (mm4, v, &p);
			if (__builtin_expect(
			     (gmp_vector_nonnegative (v, TARGETN-2+1) ||
			      gmp_vector_nonpositive (v, TARGETN-2+1)),
			     0)) {
				printf ("******** EXAMPLE: ");
				for (i = 0; i < TARGETN-2+1; i++) {
					if (mpz_fits_slong_p (&(v[i]))) {
						long vi = mpz_get_si (&(v[i]));
						printf ("%ld", vi);
					} else {
						printf ("(too large)");
					}
					if (i < TARGETN-2) {
						printf ("x^%dy^%d + ", degx[c[i]], degy[c[i]]);
					} else {
						printf ("(x^%d + y^%d)", DEGREE, DEGREE);
					}
				}
				printf("   at: ");
				for (i = 0; i < TARGETN-2; i++) {
					printf ("%d", trc[i]);
					if (i < TARGETN-2-1)
						printf (",");
				}
				printf("   (");
				for (i = 0; i < TARGETN-2; i++) {
					printf ("%d", c[i]);
					if (i < TARGETN-2-1)
						printf (",");
				}
				printf("\n");
				fflush(stdout);
				cnt ++;
			}
		}

status_update:
		if (__builtin_expect(j == 200000000, 0)) {
			long long elapsed, overall_elapsed_ms;

			gettimeofday(&t1, 0);
			elapsed = (t1.tv_sec-t0.tv_sec)*1000000LL + t1.tv_usec-t0.tv_usec;
			overall_elapsed_ms = (t1.tv_sec-t00.tv_sec)*1000LL + (t1.tv_usec-t00.tv_usec)/1000LL;

			t0 = t1;

			printf("at: ");
			for (i = 0; i < TARGETN-2; i++) {
				printf ("%d,", tr[c[i]]);
			}
			printf(" (");
			for (i = 0; i < TARGETN-2; i++) {
				printf ("%d,", c[i]);
			}
			printf(" allcnt: %'Ld elapsed ms: %g overall ms: %'Ld\n", allcnt, ((double)elapsed)/1000.0, overall_elapsed_ms);
			fflush(stdout);
			j=0;
			if (getenv ("JUSTQUIT") != NULL)
				break;

			/* for testing */
			if (getenv ("DORANDOM") != NULL) {
				comb_get_random_combination (c, TARGETN-2, LOGCOLS);
#ifdef ENDOFF
				if (c[0] > ENDOFF)
					c[0] = ENDOFF;
#endif
				printf("new random one: ");
				for (i = 0; i < TARGETN-2; i++) {
					printf ("%d,", c[i]);
				}
				printf("\n");
			}
		}
		j++;
	} while (__builtin_expect (comb_get_next_combination (c, TARGETN-2, LOGCOLS),
				   TRUE));

	printf ("EXAMPLES: %d\n", cnt);
	fflush(stdout);

	{
		long long overall_elapsed_ms;

		gettimeofday(&t1, 0);
		overall_elapsed_ms = (t1.tv_sec-t00.tv_sec)*1000LL + (t1.tv_usec-t00.tv_usec)/1000LL;
		printf ("elapsed ms: %'Ld\n", overall_elapsed_ms);
	}

	printf ("allcnt: %'Ld notopcnt: %'Ld adjcnt: %'Ld "
		"nonsymcnt: %'Ld "
		"nrowcnt: %'Ld "
		"rightsideheavycnt: %'Ld "
		"simplesymcnt: %'Ld "
		"adjupcnt: %'Ld "
		"mod2fullrankcnt: %'Ld "
		"modP1fullrankcnt: %'Ld "
		"finalcnt: %'Ld\n",
		allcnt, notopcnt, adjcnt,
		nonsymcnt,
		nrowcnt, 
		rightsideheavycnt,
		simplesymcnt,
		adjupcnt,
		mod2fullrankcnt,
		modP1fullrankcnt,
		finalcnt);

	return 0;
}
