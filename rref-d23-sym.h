#define ROWS 24
#define COLS 144
#define DEGREE 23
/* d = 23 symmetric */
ntype mm[ROWS][COLS] = {
{      -1,      -1,       0,      -1,       0,      -1,       0,      0,     -1,      0,      0,     -1,      0,      0,      0,     -1,      0,      0,      0,    -1,     0,     0,      0,     0,    -1,     0,     0,     0,     0,    -1,     0,     0,     0,     0,     0,   -1,    0,    0,    0,     0,     0,   -1,    0,    0,    0,    0,    0,    0,   -1,    0,    0,    0,    0,    0,    0,   -1,    0,    0,    0,    0,    0,    0,    0,  -1,   0,   0,   0,   0,   0,   0,    0,  -1,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   0,   0,   0,   0,   0,   0,   0,   0,   0, -1,  0,  0,  0,  0,  0,  0,  0,  0,   0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,       1},
{     -23,     -21,      -1,     -20,      -1,     -19,      -1,      0,    -18,     -1,      0,    -17,     -1,      0,      0,    -16,     -1,      0,      0,   -15,    -1,     0,      0,     0,   -14,    -1,     0,     0,     0,   -13,    -1,     0,     0,     0,     0,  -12,   -1,    0,    0,     0,     0,  -11,   -1,    0,    0,    0,    0,    0,  -10,   -1,    0,    0,    0,    0,    0,   -9,   -1,    0,    0,    0,    0,    0,    0,  -8,  -1,   0,   0,   0,   0,   0,    0,  -7,  -1,   0,   0,   0,   0,   0,   0,   0,  -6,  -1,   0,   0,   0,   0,   0,   0,   0,  -5,  -1,   0,   0,   0,   0,   0,   0,   0,   0, -4, -1,  0,  0,  0,  0,  0,  0,  0,   0, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,      23},
{    -253,    -211,     -21,    -190,     -21,    -171,     -19,     -1,   -153,    -18,     -1,   -136,    -17,     -1,      0,   -120,    -16,     -1,      0,  -105,   -15,    -1,      0,     0,   -91,   -14,    -1,     0,     0,   -78,   -13,    -1,     0,     0,     0,  -66,  -12,   -1,    0,     0,     0,  -55,  -11,   -1,    0,    0,    0,    0,  -45,  -10,   -1,    0,    0,    0,    0,  -36,   -9,   -1,    0,    0,    0,    0,    0, -28,  -8,  -1,   0,   0,   0,   0,    0, -21,  -7,  -1,   0,   0,   0,   0,   0,   0, -15,  -6,  -1,   0,   0,   0,   0,   0,   0, -10,  -5,  -1,   0,   0,   0,   0,   0,   0,   0, -6, -4, -1,  0,  0,  0,  0,  0,  0,   0, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,     253},
{   -1771,   -1351,    -210,   -1141,    -210,    -969,    -172,    -19,   -816,   -153,    -19,   -680,   -136,    -17,     -1,   -560,   -120,    -16,     -1,  -455,  -105,   -15,     -1,     0,  -364,   -91,   -14,    -1,     0,  -286,   -78,   -13,    -1,     0,     0, -220,  -66,  -12,   -1,     0,     0, -165,  -55,  -11,   -1,    0,    0,    0, -120,  -45,  -10,   -1,    0,    0,    0,  -84,  -36,   -9,   -1,    0,    0,    0,    0, -56, -28,  -8,  -1,   0,   0,   0,    0, -35, -21,  -7,  -1,   0,   0,   0,   0,   0, -20, -15,  -6,  -1,   0,   0,   0,   0,   0, -10, -10,  -5,  -1,   0,   0,   0,   0,   0,   0, -4, -6, -4, -1,  0,  0,  0,  0,  0,   0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,    1771},
{   -8855,   -6195,   -1330,   -4865,   -1330,   -3877,    -988,   -171,  -3060,   -817,   -171,  -2380,   -680,   -137,    -17,  -1820,   -560,   -120,    -17, -1365,  -455,  -105,    -15,    -1, -1001,  -364,   -91,   -14,    -1,  -715,  -286,   -78,   -13,    -1,     0, -495, -220,  -66,  -12,    -1,     0, -330, -165,  -55,  -11,   -1,    0,    0, -210, -120,  -45,  -10,   -1,    0,    0, -126,  -84,  -36,   -9,   -1,    0,    0,    0, -70, -56, -28,  -8,  -1,   0,   0,    0, -35, -35, -21,  -7,  -1,   0,   0,   0,   0, -15, -20, -15,  -6,  -1,   0,   0,   0,   0,  -5, -10, -10,  -5,  -1,   0,   0,   0,   0,   0, -1, -4, -6, -4, -1,  0,  0,  0,  0,   0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,    8855},
{  -33649,  -21679,   -5985,  -15694,   -5985,  -11647,   -4047,   -969,  -8569,  -3078,   -969,  -6188,  -2381,   -697,   -136,  -4368,  -1820,   -561,   -136, -3003, -1365,  -455,   -106,   -15, -2002, -1001,  -364,   -91,   -15, -1287,  -715,  -286,   -78,   -13,    -1, -792, -495, -220,  -66,   -12,    -1, -462, -330, -165,  -55,  -11,   -1,    0, -252, -210, -120,  -45,  -10,   -1,    0, -126, -126,  -84,  -36,   -9,   -1,    0,    0, -56, -70, -56, -28,  -8,  -1,   0,    0, -21, -35, -35, -21,  -7,  -1,   0,   0,   0,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,   0,   0,   0,  0, -1, -4, -6, -4, -1,  0,  0,  0,   0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,   33649},
{ -100947,  -60249,  -20349,  -39900,  -20349,  -27303,  -12597,  -3876, -18582,  -8721,  -3876, -12377,  -6205,  -2516,   -680,  -8008,  -4369,  -1836,   -680, -5005, -3003, -1366,   -470,  -105, -3003, -2002, -1001,  -365,  -105, -1716, -1287,  -715,  -286,   -79,   -13, -924, -792, -495, -220,   -66,   -13, -462, -462, -330, -165,  -55,  -11,   -1, -210, -252, -210, -120,  -45,  -10,   -1,  -84, -126, -126,  -84,  -36,   -9,   -1,    0, -28, -56, -70, -56, -28,  -8,  -1,    0,  -7, -21, -35, -35, -21,  -7,  -1,   0,   0,  -1,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,   0,   0,  0,  0, -1, -4, -6, -4, -1,  0,  0,   0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  100947},
{ -245157, -136629,  -54264,  -82365,  -54264,  -51357,  -31008, -11628, -31977, -19380, -11628, -19465, -12512,  -6868,  -2380, -11441,  -8024,  -4488,  -2380, -6435, -5006, -3018,  -1470,  -455, -3432, -3003, -2003, -1015,  -455, -1716, -1716, -1287,  -716,  -299,   -78, -792, -924, -792, -495,  -221,   -78, -330, -462, -462, -330, -165,  -56,  -11, -120, -210, -252, -210, -120,  -45,  -11,  -36,  -84, -126, -126,  -84,  -36,   -9,   -1,  -8, -28, -56, -70, -56, -28,  -8,   -1,  -1,  -7, -21, -35, -35, -21,  -7,  -1,   0,   0,  -1,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,   0,  0,  0,  0, -1, -4, -6, -4, -1,  0,   0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  245157},
{ -490314, -257754, -116280, -141474, -116280,  -79458,  -62016, -27132, -44574, -34884, -27132, -24446, -20128, -14756,  -6188, -12886, -11560,  -8568,  -6188, -6436, -6450, -5110,  -3458, -1365, -3003, -3433, -3017, -2093, -1365, -1287, -1716, -1717, -1300,  -793,  -286, -495, -792, -924, -793,  -507,  -286, -165, -330, -462, -462, -331, -176,  -55,  -45, -120, -210, -252, -210, -121,  -55,   -9,  -36,  -84, -126, -126,  -84,  -37,   -9,  -1,  -8, -28, -56, -70, -56, -28,   -9,   0,  -1,  -7, -21, -35, -35, -21,  -7,  -1,   0,   0,  -1,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,  0,  0,  0,  0, -1, -4, -6, -4, -1,   0,  0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  490314},
{ -817190, -410210, -203490, -206720, -203490, -104006, -102714, -50388, -51680, -52326, -50388, -24990, -26690, -25636, -12376, -11560, -13430, -13260, -12376, -5020, -6540, -6890,  -6370, -3003, -2003, -3017, -3523, -3367, -3003,  -715, -1288, -1729, -1794, -1573,  -715, -220, -495, -793, -936,  -858,  -715,  -55, -165, -330, -463, -473, -385, -165,  -10,  -45, -120, -210, -253, -220, -165,   -1,   -9,  -36,  -84, -126, -127,  -93,  -36,   0,  -1,  -8, -28, -56, -70, -57,  -36,   0,   0,  -1,  -7, -21, -35, -35, -22,  -7,   0,   0,   0,  -1,  -6, -15, -20, -15,  -7,   0,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,  0,  0,  0,  0,  0, -1, -4, -6, -4,  -1,  0,  0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  817190},
{-1144066, -556206, -293930, -262276, -293930, -119510, -142766, -75582, -52326, -67184, -75582, -21828, -30498, -36686, -19448,  -8568, -13260, -17238, -19448, -3108, -5460, -7800,  -9438, -5005, -1015, -2093, -3367, -4433, -5005,  -287,  -728, -1365, -2002, -2431, -1287,  -66, -221, -507, -858, -1144, -1287,  -11,  -55, -166, -341, -517, -627, -330,   -1,  -10,  -45, -121, -220, -297, -330,    0,   -1,   -9,  -36,  -85, -135, -162,  -84,   0,   0,  -1,  -8, -28, -57, -78,  -84,   0,   0,   0,  -1,  -7, -21, -36, -42, -21,   0,   0,   0,   0,  -1,  -6, -15, -21, -21,   0,   0,   0,   0,   0,  -1,  -5, -10, -11,  -5,  0,  0,  0,  0,  0,  0, -1, -4, -6,  -5,  0,  0,  0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0, 1144066},
{-1352078, -646646, -352716, -293930, -352716, -125970, -167960, -92378, -50388, -75582, -92378, -18564, -31824, -43758, -24310,  -6188, -12376, -19448, -24310, -1820, -4368, -8008, -11440, -6435,  -455, -1365, -3003, -5005, -6435,   -91,  -364, -1001, -2002, -3003, -1716,  -13,  -78, -286, -715, -1287, -1716,   -1,  -12,  -66, -220, -495, -792, -462,    0,   -1,  -11,  -55, -165, -330, -462,    0,    0,   -1,  -10,  -45, -120, -210, -126,   0,   0,   0,  -1,  -9, -36, -84, -126,   0,   0,   0,   0,  -1,  -8, -28, -56, -35,   0,   0,   0,   0,   0,  -1,  -7, -21, -35,   0,   0,   0,   0,   0,   0,  -1,  -6, -15, -10,  0,  0,  0,  0,  0,  0,  0, -1, -5, -10,  0,  0,  0,  0,  0,  0,  0,  0, -1, -4, -3,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -3,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1, 1352078},
{-1352078, -646646, -352716, -293930, -352716, -125970, -167960, -92378, -50388, -75582, -92378, -18564, -31824, -43758, -24310,  -6188, -12376, -19448, -24310, -1820, -4368, -8008, -11440, -6435,  -455, -1365, -3003, -5005, -6435,   -91,  -364, -1001, -2002, -3003, -1716,  -13,  -78, -286, -715, -1287, -1716,   -1,  -12,  -66, -220, -495, -792, -462,    0,   -1,  -11,  -55, -165, -330, -462,    0,    0,   -1,  -10,  -45, -120, -210, -126,   0,   0,   0,  -1,  -9, -36, -84, -126,   0,   0,   0,   0,  -1,  -8, -28, -56, -35,   0,   0,   0,   0,   0,  -1,  -7, -21, -35,   0,   0,   0,   0,   0,   0,  -1,  -6, -15, -10,  0,  0,  0,  0,  0,  0,  0, -1, -5, -10,  0,  0,  0,  0,  0,  0,  0,  0, -1, -4, -3,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -3,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1, 1352078},
{-1144066, -556206, -293930, -262276, -293930, -119510, -142766, -75582, -52326, -67184, -75582, -21828, -30498, -36686, -19448,  -8568, -13260, -17238, -19448, -3108, -5460, -7800,  -9438, -5005, -1015, -2093, -3367, -4433, -5005,  -287,  -728, -1365, -2002, -2431, -1287,  -66, -221, -507, -858, -1144, -1287,  -11,  -55, -166, -341, -517, -627, -330,   -1,  -10,  -45, -121, -220, -297, -330,    0,   -1,   -9,  -36,  -85, -135, -162,  -84,   0,   0,  -1,  -8, -28, -57, -78,  -84,   0,   0,   0,  -1,  -7, -21, -36, -42, -21,   0,   0,   0,   0,  -1,  -6, -15, -21, -21,   0,   0,   0,   0,   0,  -1,  -5, -10, -11,  -5,  0,  0,  0,  0,  0,  0, -1, -4, -6,  -5,  0,  0,  0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0, 1144066},
{ -817190, -410210, -203490, -206720, -203490, -104006, -102714, -50388, -51680, -52326, -50388, -24990, -26690, -25636, -12376, -11560, -13430, -13260, -12376, -5020, -6540, -6890,  -6370, -3003, -2003, -3017, -3523, -3367, -3003,  -715, -1288, -1729, -1794, -1573,  -715, -220, -495, -793, -936,  -858,  -715,  -55, -165, -330, -463, -473, -385, -165,  -10,  -45, -120, -210, -253, -220, -165,   -1,   -9,  -36,  -84, -126, -127,  -93,  -36,   0,  -1,  -8, -28, -56, -70, -57,  -36,   0,   0,  -1,  -7, -21, -35, -35, -22,  -7,   0,   0,   0,  -1,  -6, -15, -20, -15,  -7,   0,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,  0,  0,  0,  0,  0, -1, -4, -6, -4,  -1,  0,  0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  817190},
{ -490314, -257754, -116280, -141474, -116280,  -79458,  -62016, -27132, -44574, -34884, -27132, -24446, -20128, -14756,  -6188, -12886, -11560,  -8568,  -6188, -6436, -6450, -5110,  -3458, -1365, -3003, -3433, -3017, -2093, -1365, -1287, -1716, -1717, -1300,  -793,  -286, -495, -792, -924, -793,  -507,  -286, -165, -330, -462, -462, -331, -176,  -55,  -45, -120, -210, -252, -210, -121,  -55,   -9,  -36,  -84, -126, -126,  -84,  -37,   -9,  -1,  -8, -28, -56, -70, -56, -28,   -9,   0,  -1,  -7, -21, -35, -35, -21,  -7,  -1,   0,   0,  -1,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,  0,  0,  0,  0, -1, -4, -6, -4, -1,   0,  0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  490314},
{ -245157, -136629,  -54264,  -82365,  -54264,  -51357,  -31008, -11628, -31977, -19380, -11628, -19465, -12512,  -6868,  -2380, -11441,  -8024,  -4488,  -2380, -6435, -5006, -3018,  -1470,  -455, -3432, -3003, -2003, -1015,  -455, -1716, -1716, -1287,  -716,  -299,   -78, -792, -924, -792, -495,  -221,   -78, -330, -462, -462, -330, -165,  -56,  -11, -120, -210, -252, -210, -120,  -45,  -11,  -36,  -84, -126, -126,  -84,  -36,   -9,   -1,  -8, -28, -56, -70, -56, -28,  -8,   -1,  -1,  -7, -21, -35, -35, -21,  -7,  -1,   0,   0,  -1,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,   0,  0,  0,  0, -1, -4, -6, -4, -1,  0,   0,  0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  245157},
{ -100947,  -60249,  -20349,  -39900,  -20349,  -27303,  -12597,  -3876, -18582,  -8721,  -3876, -12377,  -6205,  -2516,   -680,  -8008,  -4369,  -1836,   -680, -5005, -3003, -1366,   -470,  -105, -3003, -2002, -1001,  -365,  -105, -1716, -1287,  -715,  -286,   -79,   -13, -924, -792, -495, -220,   -66,   -13, -462, -462, -330, -165,  -55,  -11,   -1, -210, -252, -210, -120,  -45,  -10,   -1,  -84, -126, -126,  -84,  -36,   -9,   -1,    0, -28, -56, -70, -56, -28,  -8,  -1,    0,  -7, -21, -35, -35, -21,  -7,  -1,   0,   0,  -1,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,   0,   0,  0,  0, -1, -4, -6, -4, -1,  0,  0,   0,  0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  100947},
{  -33649,  -21679,   -5985,  -15694,   -5985,  -11647,   -4047,   -969,  -8569,  -3078,   -969,  -6188,  -2381,   -697,   -136,  -4368,  -1820,   -561,   -136, -3003, -1365,  -455,   -106,   -15, -2002, -1001,  -364,   -91,   -15, -1287,  -715,  -286,   -78,   -13,    -1, -792, -495, -220,  -66,   -12,    -1, -462, -330, -165,  -55,  -11,   -1,    0, -252, -210, -120,  -45,  -10,   -1,    0, -126, -126,  -84,  -36,   -9,   -1,    0,    0, -56, -70, -56, -28,  -8,  -1,   0,    0, -21, -35, -35, -21,  -7,  -1,   0,   0,   0,  -6, -15, -20, -15,  -6,  -1,   0,   0,   0,  -1,  -5, -10, -10,  -5,  -1,   0,   0,   0,   0,  0, -1, -4, -6, -4, -1,  0,  0,  0,   0,  0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,   33649},
{   -8855,   -6195,   -1330,   -4865,   -1330,   -3877,    -988,   -171,  -3060,   -817,   -171,  -2380,   -680,   -137,    -17,  -1820,   -560,   -120,    -17, -1365,  -455,  -105,    -15,    -1, -1001,  -364,   -91,   -14,    -1,  -715,  -286,   -78,   -13,    -1,     0, -495, -220,  -66,  -12,    -1,     0, -330, -165,  -55,  -11,   -1,    0,    0, -210, -120,  -45,  -10,   -1,    0,    0, -126,  -84,  -36,   -9,   -1,    0,    0,    0, -70, -56, -28,  -8,  -1,   0,   0,    0, -35, -35, -21,  -7,  -1,   0,   0,   0,   0, -15, -20, -15,  -6,  -1,   0,   0,   0,   0,  -5, -10, -10,  -5,  -1,   0,   0,   0,   0,   0, -1, -4, -6, -4, -1,  0,  0,  0,  0,   0,  0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,    8855},
{   -1771,   -1351,    -210,   -1141,    -210,    -969,    -172,    -19,   -816,   -153,    -19,   -680,   -136,    -17,     -1,   -560,   -120,    -16,     -1,  -455,  -105,   -15,     -1,     0,  -364,   -91,   -14,    -1,     0,  -286,   -78,   -13,    -1,     0,     0, -220,  -66,  -12,   -1,     0,     0, -165,  -55,  -11,   -1,    0,    0,    0, -120,  -45,  -10,   -1,    0,    0,    0,  -84,  -36,   -9,   -1,    0,    0,    0,    0, -56, -28,  -8,  -1,   0,   0,   0,    0, -35, -21,  -7,  -1,   0,   0,   0,   0,   0, -20, -15,  -6,  -1,   0,   0,   0,   0,   0, -10, -10,  -5,  -1,   0,   0,   0,   0,   0,   0, -4, -6, -4, -1,  0,  0,  0,  0,  0,   0, -1, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,    1771},
{    -253,    -211,     -21,    -190,     -21,    -171,     -19,     -1,   -153,    -18,     -1,   -136,    -17,     -1,      0,   -120,    -16,     -1,      0,  -105,   -15,    -1,      0,     0,   -91,   -14,    -1,     0,     0,   -78,   -13,    -1,     0,     0,     0,  -66,  -12,   -1,    0,     0,     0,  -55,  -11,   -1,    0,    0,    0,    0,  -45,  -10,   -1,    0,    0,    0,    0,  -36,   -9,   -1,    0,    0,    0,    0,    0, -28,  -8,  -1,   0,   0,   0,   0,    0, -21,  -7,  -1,   0,   0,   0,   0,   0,   0, -15,  -6,  -1,   0,   0,   0,   0,   0,   0, -10,  -5,  -1,   0,   0,   0,   0,   0,   0,   0, -6, -4, -1,  0,  0,  0,  0,  0,  0,   0, -3, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0, -1, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,     253},
{     -23,     -21,      -1,     -20,      -1,     -19,      -1,      0,    -18,     -1,      0,    -17,     -1,      0,      0,    -16,     -1,      0,      0,   -15,    -1,     0,      0,     0,   -14,    -1,     0,     0,     0,   -13,    -1,     0,     0,     0,     0,  -12,   -1,    0,    0,     0,     0,  -11,   -1,    0,    0,    0,    0,    0,  -10,   -1,    0,    0,    0,    0,    0,   -9,   -1,    0,    0,    0,    0,    0,    0,  -8,  -1,   0,   0,   0,   0,   0,    0,  -7,  -1,   0,   0,   0,   0,   0,   0,   0,  -6,  -1,   0,   0,   0,   0,   0,   0,   0,  -5,  -1,   0,   0,   0,   0,   0,   0,   0,   0, -4, -1,  0,  0,  0,  0,  0,  0,  0,   0, -3, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -2, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,      23},
{      -1,      -1,       0,      -1,       0,      -1,       0,      0,     -1,      0,      0,     -1,      0,      0,      0,     -1,      0,      0,      0,    -1,     0,     0,      0,     0,    -1,     0,     0,     0,     0,    -1,     0,     0,     0,     0,     0,   -1,    0,    0,    0,     0,     0,   -1,    0,    0,    0,    0,    0,    0,   -1,    0,    0,    0,    0,    0,    0,   -1,    0,    0,    0,    0,    0,    0,    0,  -1,   0,   0,   0,   0,   0,   0,    0,  -1,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   0,   0,   0,   0,   0,   0,   0,   0,  -1,   0,   0,   0,   0,   0,   0,   0,   0,   0, -1,  0,  0,  0,  0,  0,  0,  0,  0,   0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,       1}};
