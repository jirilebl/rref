#define ROWS 10
#define COLS 45
#define DEGREE 9
/* d = 9 */
ntype mm[ROWS][COLS] = {{
-1,   0,  -1,   0,   0,  -1,   0,   0,   0,  -1,   0,   0,   0,   0, -1,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,   1},
{-8,  -1,  -7,  -1,   0,  -6,  -1,   0,   0,  -5,  -1,   0,   0,   0, -4, -1,  0,  0,  0,  0, -3, -1,  0,  0,  0,  0,  0, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,   9},
{-28,  -8, -21,  -7,  -1, -15,  -6,  -1,   0, -10,  -5,  -1,   0,   0, -6, -4, -1,  0,  0,  0, -3, -3, -1,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  36},
{-56, -28, -35, -21,  -7, -20, -15,  -6,  -1, -10, -10,  -5,  -1,   0, -4, -6, -4, -1,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  84},
{-70, -56, -35, -35, -21, -15, -20, -15,  -6,  -5, -10, -10,  -5,  -1, -1, -4, -6, -4, -1,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0, 126},
{-56, -70, -21, -35, -35,  -6, -15, -20, -15,  -1,  -5, -10, -10,  -5,  0, -1, -4, -6, -4, -1,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0, 126},
{-28, -56,  -7, -21, -35,  -1,  -6, -15, -20,   0,  -1,  -5, -10, -10,  0,  0, -1, -4, -6, -4,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  84},
{-8, -28,  -1,  -7, -21,   0,  -1,  -6, -15,   0,   0,  -1,  -5, -10,  0,  0,  0, -1, -4, -6,  0,  0,  0,  0, -1, -3, -3,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0, -1, -1,  0,  36},
{-1,  -8,   0,  -1,  -7,   0,   0,  -1,  -6,   0,   0,   0,  -1,  -5,  0,  0,  0,  0, -1, -4,  0,  0,  0,  0,  0, -1, -3,  0,  0,  0,  0,  0,  0, -1, -2,  0,  0,  0,  0,  0,  0,  0, -1, -1,   9},
{0,  -1,   0,   0,  -1,   0,   0,   0,  -1,   0,   0,   0,   0,  -1,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1,   1}};
