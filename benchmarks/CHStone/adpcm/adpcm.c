/*
   +--------------------------------------------------------------------------+
   | CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
   | ======================================================================== |
   |                                                                          |
   | * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
   |                            H. Takada and K. Ishii                        |
   |                            Nagoya University, Japan                      |
   |                                                                          |
   | * Remark :                                                               |
   |    1. This source code is modified to unify the formats of the benchmark |
   |       programs in CHStone.                                               |
   |    2. Test vectors are added for CHStone.                                |
   |    3. If "main_result" is 0 at the end of the program, the program is    |
   |       correctly executed.                                                |
   |    4. Please follow the copyright of each benchmark program.             |
   +--------------------------------------------------------------------------+
 */
/*************************************************************************/
/*                                                                       */
/*   SNU-RT Benchmark Suite for Worst Case Timing Analysis               */
/*   =====================================================               */
/*                              Collected and Modified by S.-S. Lim      */
/*                                           sslim@archi.snu.ac.kr       */
/*                                         Real-Time Research Group      */
/*                                        Seoul National University      */
/*                                                                       */
/*                                                                       */
/*        < Features > - restrictions for our experimental environment   */
/*                                                                       */
/*          1. Completely structured.                                    */
/*               - There are no unconditional jumps.                     */
/*               - There are no exit from loop bodies.                   */
/*                 (There are no 'break' or 'return' in loop bodies)     */
/*          2. No 'switch' statements.                                   */
/*          3. No 'do..while' statements.                                */
/*          4. Expressions are restricted.                               */
/*               - There are no multiple expressions joined by 'or',     */
/*                'and' operations.                                      */
/*          5. No library calls.                                         */
/*               - All the functions needed are implemented in the       */
/*                 source file.                                          */
/*                                                                       */
/*                                                                       */
/*************************************************************************/
/*                                                                       */
/*  FILE: adpcm.c                                                        */
/*  SOURCE : C Algorithms for Real-Time DSP by P. M. Embree              */
/*                                                                       */
/*  DESCRIPTION :                                                        */
/*                                                                       */
/*     CCITT G.722 ADPCM (Adaptive Differential Pulse Code Modulation)   */
/*     algorithm.                                                        */
/*     16khz sample rate data is stored in the array test_data[SIZE].    */
/*     Results are stored in the array compressed[SIZE] and result[SIZE].*/
/*     Execution time is determined by the constant SIZE (default value  */
/*     is 2000).                                                         */
/*                                                                       */
/*  REMARK :                                                             */
/*                                                                       */
/*  EXECUTION TIME :                                                     */
/*                                                                       */
/*                                                                       */
/*************************************************************************/

#define SIZE 100
#define IN_END 100

int encode (int, int);
void decode (int);
int filtez (int *bpl, int *dlt);
void upzero (int dlt, int *dlti, int *bli);
int filtep (int rlt1, int al1, int rlt2, int al2);
int quantl (int el, int detl);
int logscl (int il, int nbl);
int scalel (int nbl, int shift_constant);
int uppol2 (int al1, int al2, int plt, int plt1, int plt2);
int uppol1 (int al1, int apl2, int plt, int plt1);
int logsch (int ih, int nbh);
void reset ();

/* G722 encode function two ints in, one 8 bit output */

/* put input samples in xin1 = first value, xin2 = second value */
/* returns il and ih stored together */

  int
abs (int n)
{
  int m;

  if (n >= 0)
    m = n;
  else
    m = -n;
  return m;
}

/* filtez - compute predictor output signal (zero section) */
/* input: bpl1-6 and dlt1-6, output: szl */

  int
filtez (int *bpl, int *dlt)
{
  int i;
  int zl = 0;
  //zl = (int) (*bpl++) * (*dlt++);
  for (i = 1; i < 7; i++)
    zl += (int) (*bpl++) * (*dlt++);

  return ((int) (zl >> 14));	/* x2 here */
}

/* filtep - compute predictor output signal (pole section) */
/* input rlt1-2 and al1-2, output spl */

  int
filtep (int rlt1, int al1, int rlt2, int al2)
{
  int pl, pl2;
  pl = rlt1 << 1 ;
  pl = (int) al1 *pl;
  pl2 = rlt2 << 1 ;
  pl += (int) al2 *pl2;
  return ((int) (pl >> 15));
}

/* quantl - quantize the difference signal in the lower sub-band */
  int
quantl (int el, int detl)
{

  const int decis_levl[30] = {
    280, 576, 880, 1200, 1520, 1864, 2208, 2584,
    2960, 3376, 3784, 4240, 4696, 5200, 5712, 6288,
    6864, 7520, 8184, 8968, 9752, 10712, 11664, 12896,
    14120, 15840, 17560, 20456, 23352, 32767
  };
  /* decision levels - pre-multiplied by 8, 0 to indicate end */
  /* quantization table 31 long to make quantl look-up easier,
     last entry is for mil=30 case when wd is max */
  const int quant26bt_pos[31] = {
    61, 60, 59, 58, 57, 56, 55, 54,
    53, 52, 51, 50, 49, 48, 47, 46,
    45, 44, 43, 42, 41, 40, 39, 38,
    37, 36, 35, 34, 33, 32, 32
  };

  /* quantization table 31 long to make quantl look-up easier,
     last entry is for mil=30 case when wd is max */
  const int quant26bt_neg[31] = {
    63, 62, 31, 30, 29, 28, 27, 26,
    25, 24, 23, 22, 21, 20, 19, 18,
    17, 16, 15, 14, 13, 12, 11, 10,
    9, 8, 7, 6, 5, 4, 4
  };


  int ril, mil;
  int wd, decis;

  /* abs of difference signal */
  wd = abs (el);
  /* determine mil based on decision levels and detl gain */
  for (mil = 0; mil < 30; mil++)
  {
    decis = (decis_levl[mil] * (int) detl) >> 15L;
    if (wd <= decis)
      break;
  }
  /* if mil=30 then wd is less than all decision levels */
  if (el >= 0)
    ril = quant26bt_pos[mil];
  else
    ril = quant26bt_neg[mil];
  return (ril);
}

/* logscl - update log quantizer scale factor in lower sub-band */
/* note that nbl is passed and returned */

  int
logscl (int il, int nbl)
{
  const int wl_code_table[16] = {
    -60, 3042, 1198, 538, 334, 172, 58, -30,
    3042, 1198, 538, 334, 172, 58, -30, -60
  };

  int wd;
  int tmp = nbl;
  int val = tmp << 7;
  val -= tmp; 
  wd = (val) >> 7L;	/* leak factor 127/128 */
  nbl = (int) wd + wl_code_table[il >> 2];
  if (nbl < 0)
    nbl = 0;
  if (nbl > 18432)
    nbl = 18432;
  return (nbl);
}

/* scalel: compute quantizer scale factor in lower or upper sub-band*/

  int
scalel (int nbl, int shift_constant)
{
  const int ilb_table[32] = {
    2048, 2093, 2139, 2186, 2233, 2282, 2332, 2383,
    2435, 2489, 2543, 2599, 2656, 2714, 2774, 2834,
    2896, 2960, 3025, 3091, 3158, 3228, 3298, 3371,
    3444, 3520, 3597, 3676, 3756, 3838, 3922, 4008
  };
  int wd1, wd2, wd3;

  wd1 = (nbl >> 6) & 31;
  wd2 = nbl >> 11;
  wd3 = ilb_table[wd1] >> (shift_constant + 1 - wd2);
  return (wd3 << 3);
}

/* upzero - inputs: dlt, dlti[0-5], bli[0-5], outputs: updated bli[0-5] */
/* also implements delay of bli and update of dlti from dlt */

  void
upzero (int dlt, int *dlti, int *bli)
{
  int i, wd2, wd3;
  /*if dlt is zero, then no sum into bli */
  if (dlt == 0)
  {
    for (i = 0; i < 6; i++)
    {
      int tmp = bli[i];
      int val = tmp << 8;
      val -= tmp; 
      bli[i] = (int) (val) >> 8L;	/* leak factor of 255/256 */
    }
  }
  else
  {
    for (i = 0; i < 6; i++)
    {
      if ((int) dlt * dlti[i] >= 0)
        wd2 = 128;
      else
        wd2 = -128;
      int tmp = bli[i];
      int val = tmp << 8;
      val -= tmp; 
      wd3 = (int) (val) >> 8L;	/* leak factor of 255/256 */
      bli[i] = wd2 + wd3;
    }
  }
  /* implement delay line for dlt */
  dlti[5] = dlti[4];
  dlti[4] = dlti[3];
  dlti[3] = dlti[2];
  dlti[2] = dlti[1];
  dlti[1] = dlti[0];
  dlti[0] = dlt;
}

/* uppol2 - update second predictor coefficient (pole section) */
/* inputs: al1, al2, plt, plt1, plt2. outputs: apl2 */

  int
uppol2 (int al1, int al2, int plt, int plt1, int plt2)
{
  int wd2, wd4;
  int apl2;
  wd2 = (int) al1 << 2;
  if ((int) plt * plt1 >= 0L)
    wd2 = -wd2;			/* check same sign */
  wd2 = wd2 >> 7;		/* gain of 1/128 */
  if ((int) plt * plt2 >= 0L)
  {
    wd4 = wd2 + 128;		/* same sign case */
  }
  else
  {
    wd4 = wd2 - 128;
  }
  int tmp = al2;
  int val = tmp << 7;
  val -= tmp; 
  apl2 = wd4 + (val >> 7L);	/* leak factor of 127/128 */

  /* apl2 is limited to +-.75 */
  if (apl2 > 12288)
    apl2 = 12288;
  if (apl2 < -12288)
    apl2 = -12288;
  return (apl2);
}

/* uppol1 - update first predictor coefficient (pole section) */
/* inputs: al1, apl2, plt, plt1. outputs: apl1 */

  int
uppol1 (int al1, int apl2, int plt, int plt1)
{
  int wd2;
  int wd3, apl1;
  int tmp = al1;
  int val = tmp << 8;
  val -= tmp; 
  wd2 = (val) >> 8L;	/* leak factor of 255/256 */
  if ((int) plt * plt1 >= 0L)
  {
    apl1 = (int) wd2 + 192;	/* same sign case */
  }
  else
  {
    apl1 = (int) wd2 - 192;
  }
  /* note: wd3= .9375-.75 is always positive */
  wd3 = 15360 - apl2;		/* limit value */
  if (apl1 > wd3)
    apl1 = wd3;
  if (apl1 < -wd3)
    apl1 = -wd3;
  return (apl1);
}

/* logsch - update log quantizer scale factor in higher sub-band */
/* note that nbh is passed and returned */

  int
logsch (int ih, int nbh)
{
  int wd;
  const int wh_code_table[4] = {
    798, -214, 798, -214
  };

  int tmp = nbh;
  int val = tmp << 7;
  val -= tmp; 
  wd = (val) >> 7L;	/* leak factor 127/128 */
  nbh = wd + wh_code_table[ih];
  if (nbh < 0)
    nbh = 0;
  if (nbh > 22528)
    nbh = 22528;
  return (nbh);
}

/*
   +--------------------------------------------------------------------------+
   | * Test Vectors (added for CHStone)                                       |
   |     test_data : input data                                               |
   |     test_compressed : expected output data for "encode"                  |
   |     test_result : expected output data for "decode"                      |
   +--------------------------------------------------------------------------+
 */

/* G722 C code */


  void
adpcm_main (const int test_data[SIZE], int compressed[SIZE], int result[SIZE])
{
  /* variables for transimit quadrature mirror filter here */
  int tqmf[24];

  /* QMF filter coefficients:
     scaled by a factor of 4 compared to G722 CCITT recomendation */
  const int h[24] = {
    12, -44, -44, 212, 48, -624, 128, 1448,
    -840, -3220, 3804, 15504, 15504, 3804, -3220, -840,
    1448, 128, -624, 48, 212, -44, -44, 12
  };


  /* variables for receive quadrature mirror filter here */
  int accumc[11], accumd[11];

  const int qq2_code2_table[4] = {
    -7408, -1616, 7408, 1616
  };

  const int qq4_code4_table[16] = {
    0, -20456, -12896, -8968, -6288, -4240, -2584, -1200,
    20456, 12896, 8968, 6288, 4240, 2584, 1200, 0
  };
  const int qq6_code6_table[64] = {
    -136, -136, -136, -136, -24808, -21904, -19008, -16704,
    -14984, -13512, -12280, -11192, -10232, -9360, -8576, -7856,
    -7192, -6576, -6000, -5456, -4944, -4464, -4008, -3576,
    -3168, -2776, -2400, -2032, -1688, -1360, -1040, -728,
    24808, 21904, 19008, 16704, 14984, 13512, 12280, 11192,
    10232, 9360, 8576, 7856, 7192, 6576, 6000, 5456,
    4944, 4464, 4008, 3576, 3168, 2776, 2400, 2032,
    1688, 1360, 1040, 728, 432, 136, -432, -136
  };


  int delay_dhx[6];

  int delay_bph[6];

  int dec_del_bpl[6];

  int dec_del_dltx[6];

  /* variables used in filtez */
  int dec_del_bph[6];

  int dec_del_dhx[6];

  int delay_bpl[6];

  int delay_dltx[6];
  /* outputs of decode() */
  int xout1, xout2;

  int xs, xd;

  /* variables for encoder (hi and lo) here */

  int il, szl, spl, sl, el;


  int nbl;			/* delay line */
  int al1, al2;
  int plt, plt1, plt2;
  int dlt;
  int rlt, rlt1, rlt2;

  int detl;

  int deth;
  int sh;				/* this comes from adaptive predictor */
  int eh;

  int ah1, ah2;
  int ph1, ph2;
  int rh1, rh2;

  int dh, ih;
  int nbh, szh;
  int sph, ph, yh, rh;

  /* variables for decoder here */
  int ilr, rl;
  int dec_deth, dec_detl, dec_dlt;
  int dec_plt, dec_plt1, dec_plt2;
  int dec_szl, dec_spl, dec_sl;
  int dec_rlt1, dec_rlt2, dec_rlt;
  int dec_al1, dec_al2;
  int dl;
  int dec_nbl, dec_dh, dec_nbh;

  int dec_szh;
  /* variables used in filtep */
  int dec_rh1, dec_rh2;
  int dec_ah1, dec_ah2;
  int dec_ph, dec_sph;

  int dec_sh;

  int dec_ph1, dec_ph2;
  unsigned int i, j;

  /* reset, initialize required memory */

  detl = dec_detl = 32;		/* reset to min scale factor */
  deth = dec_deth = 8;
  nbl = al1 = al2 = plt1 = plt2 = rlt1 = rlt2 = 0;
  nbh = ah1 = ah2 = ph1 = ph2 = rh1 = rh2 = 0;
  dec_nbl = dec_al1 = dec_al2 = dec_plt1 = dec_plt2 = dec_rlt1 = dec_rlt2 = 0;
  dec_nbh = dec_ah1 = dec_ah2 = dec_ph1 = dec_ph2 = dec_rh1 = dec_rh2 = 0;

  for (i = 0; i < 6; i++)
  {
    delay_dltx[i] = 0;
    delay_dhx[i] = 0;
    dec_del_dltx[i] = 0;
    dec_del_dhx[i] = 0;
  }

  for (i = 0; i < 6; i++)
  {
    delay_bpl[i] = 0;
    delay_bph[i] = 0;
    dec_del_bpl[i] = 0;
    dec_del_bph[i] = 0;
  }

  for (i = 0; i < 24; i++)
    tqmf[i] = 0;		// i<23

  for (i = 0; i < 11; i++)
  {
    accumc[i] = 0;
    accumd[i] = 0;
  }

  for (i = 0; i < IN_END; i += 2)
  {
    int xin1 = test_data[i + 0];
    int xin2 = test_data[i + 1];
    const int *h_ptr;
    int *tqmf_ptr, *tqmf_ptr1;
    int xa = 0, xb = 0;
    int decis;

    /* transmit quadrature mirror filters implemented here */
    h_ptr = h;
    tqmf_ptr = tqmf;
    /* main multiply accumulate loop for samples and coefficients */
    for (int j = 0; j < 12; j++)
    {
      int opA1, opB1;
      int opA2, opB2;
      if(j==11){
        opA1 = (*tqmf_ptr++);
        opB1 = (*h_ptr++);
        opA2 = (*tqmf_ptr);
        opB2 = (*h_ptr++);
      }
      else{
        opA1 = (*tqmf_ptr++);
        opB1 = (*h_ptr++);
        opA2 = (*tqmf_ptr++);
        opB2 = (*h_ptr++);
      }
      xa += (int) opA1 * opB1;
      xb += (int) opA2 * opB2;
    }

    /* update delay line tqmf */
    tqmf_ptr1 = tqmf_ptr - 2;
    for (int j = 0; j < 22; j++)
      *tqmf_ptr-- = *tqmf_ptr1--;
    *tqmf_ptr-- = xin1;
    *tqmf_ptr = xin2;

    /* scale outputs */
    int xl = (xa + xb) >> 15;
    int xh = (xa - xb) >> 15;

    /* end of quadrature mirror filter code */

    /* starting with lower sub band encoder */

    /* filtez - compute predictor output section - zero section */
    szl = filtez (delay_bpl, delay_dltx);

    /* filtep - compute predictor output signal (pole section) */
    spl = filtep (rlt1, al1, rlt2, al2);

    /* compute the predictor output value in the lower sub_band encoder */
    sl = szl + spl;
    el = xl - sl;

    /* quantl: quantize the difference signal */
    il = quantl (el, detl);

    /* computes quantized difference signal */
    /* for invqbl, truncate by 2 lsbs, so mode = 3 */
    dlt = ((int) detl * qq4_code4_table[il >> 2]) >> 15;

    /* logscl: updates logarithmic quant. scale factor in low sub band */
    nbl = logscl (il, nbl);

    /* scalel: compute the quantizer scale factor in the lower sub band */
    /* calling parameters nbl and 8 (constant such that scalel can be scaleh) */
    detl = scalel (nbl, 8);

    /* parrec - simple addition to compute recontructed signal for adaptive pred */
    plt = dlt + szl;

    /* upzero: update zero section predictor coefficients (sixth order)*/
    /* calling parameters: dlt, dlt1, dlt2, ..., dlt6 from dlt */
    /*  bpli (linear_buffer in which all six values are delayed */
    /* return params:      updated bpli, delayed dltx */
    upzero (dlt, delay_dltx, delay_bpl);

    /* uppol2- update second predictor coefficient apl2 and delay it as al2 */
    /* calling parameters: al1, al2, plt, plt1, plt2 */
    al2 = uppol2 (al1, al2, plt, plt1, plt2);

    /* uppol1 :update first predictor coefficient apl1 and delay it as al1 */
    /* calling parameters: al1, apl2, plt, plt1 */
    al1 = uppol1 (al1, al2, plt, plt1);

    /* recons : compute recontructed signal for adaptive predictor */
    rlt = sl + dlt;

    /* done with lower sub_band encoder; now implement delays for next time*/
    rlt2 = rlt1;
    rlt1 = rlt;
    plt2 = plt1;
    plt1 = plt;

    /* high band encode */

    szh = filtez (delay_bph, delay_dhx);

    sph = filtep (rh1, ah1, rh2, ah2);

    /* predic: sh = sph + szh */
    sh = sph + szh;
    /* subtra: eh = xh - sh */
    eh = xh - sh;

    /* quanth - quantization of difference signal for higher sub-band */
    /* quanth: in-place for speed params: eh, deth (has init. value) */
    if (eh >= 0)
    {
      ih = 3;			/* 2,3 are pos codes */
    }
    else
    {
      ih = 1;			/* 0,1 are neg codes */
    }
    decis = (564L * (int) deth) >> 12L;
    if (abs (eh) > decis)
      ih--;			/* mih = 2 case */

    /* compute the quantized difference signal, higher sub-band*/
    dh = ((int) deth * qq2_code2_table[ih]) >> 15L;

    /* logsch: update logarithmic quantizer scale factor in hi sub-band*/
    nbh = logsch (ih, nbh);

    /* note : scalel and scaleh use same code, different parameters */
    deth = scalel (nbh, 10);

    /* parrec - add pole predictor output to quantized diff. signal */
    ph = dh + szh;

    /* upzero: update zero section predictor coefficients (sixth order) */
    /* calling parameters: dh, dhi, bphi */
    /* return params: updated bphi, delayed dhx */
    upzero (dh, delay_dhx, delay_bph);

    /* uppol2: update second predictor coef aph2 and delay as ah2 */
    /* calling params: ah1, ah2, ph, ph1, ph2 */
    ah2 = uppol2 (ah1, ah2, ph, ph1, ph2);

    /* uppol1:  update first predictor coef. aph2 and delay it as ah1 */
    ah1 = uppol1 (ah1, ah2, ph, ph1);

    /* recons for higher sub-band */
    yh = sh + dh;

    /* done with higher sub-band encoder, now Delay for next time */
    rh2 = rh1;
    rh1 = yh;
    ph2 = ph1;
    ph1 = ph;

    /* multiplex ih and il to get signals together */
    compressed[i/2] = (il | (ih << 6));
  }
  for (i = 0; i < IN_END; i += 2)
  {
    int input  = compressed[i / 2];

    int xa1, xa2;		/* qmf accumulators */
    const int *h_ptr;
    int *ac_ptr, *ac_ptr1, *ad_ptr, *ad_ptr1;

    /* split transmitted word from input into ilr and ih */
    ilr = input & 0x3f;
    ih = input >> 6;

    /* LOWER SUB_BAND DECODER */

    /* filtez: compute predictor output for zero section */
    dec_szl = filtez (dec_del_bpl, dec_del_dltx);

    /* filtep: compute predictor output signal for pole section */
    dec_spl = filtep (dec_rlt1, dec_al1, dec_rlt2, dec_al2);

    dec_sl = dec_spl + dec_szl;

    /* compute quantized difference signal for adaptive predic */
    dec_dlt = ((int) dec_detl * qq4_code4_table[ilr >> 2]) >> 15;

    /* compute quantized difference signal for decoder output */
    dl = ((int) dec_detl * qq6_code6_table[il]) >> 15;

    rl = dl + dec_sl;

    /* logscl: quantizer scale factor adaptation in the lower sub-band */
    dec_nbl = logscl (ilr, dec_nbl);

    /* scalel: computes quantizer scale factor in the lower sub band */
    dec_detl = scalel (dec_nbl, 8);

    /* parrec - add pole predictor output to quantized diff. signal */
    /* for partially reconstructed signal */
    dec_plt = dec_dlt + dec_szl;

    /* upzero: update zero section predictor coefficients */
    upzero (dec_dlt, dec_del_dltx, dec_del_bpl);

    /* uppol2: update second predictor coefficient apl2 and delay it as al2 */
    dec_al2 = uppol2 (dec_al1, dec_al2, dec_plt, dec_plt1, dec_plt2);

    /* uppol1: update first predictor coef. (pole setion) */
    dec_al1 = uppol1 (dec_al1, dec_al2, dec_plt, dec_plt1);

    /* recons : compute recontructed signal for adaptive predictor */
    dec_rlt = dec_sl + dec_dlt;

    /* done with lower sub band decoder, implement delays for next time */
    dec_rlt2 = dec_rlt1;
    dec_rlt1 = dec_rlt;
    dec_plt2 = dec_plt1;
    dec_plt1 = dec_plt;

    /* HIGH SUB-BAND DECODER */

    /* filtez: compute predictor output for zero section */
    dec_szh = filtez (dec_del_bph, dec_del_dhx);

    /* filtep: compute predictor output signal for pole section */
    dec_sph = filtep (dec_rh1, dec_ah1, dec_rh2, dec_ah2);

    /* predic:compute the predictor output value in the higher sub_band decoder */
    dec_sh = dec_sph + dec_szh;

    /* in-place compute the quantized difference signal */
    dec_dh = ((int) dec_deth * qq2_code2_table[ih]) >> 15L;

    /* logsch: update logarithmic quantizer scale factor in hi sub band */
    dec_nbh = logsch (ih, dec_nbh);

    /* scalel: compute the quantizer scale factor in the higher sub band */
    dec_deth = scalel (dec_nbh, 10);

    /* parrec: compute partially recontructed signal */
    dec_ph = dec_dh + dec_szh;

    /* upzero: update zero section predictor coefficients */
    upzero (dec_dh, dec_del_dhx, dec_del_bph);

    /* uppol2: update second predictor coefficient aph2 and delay it as ah2 */
    dec_ah2 = uppol2 (dec_ah1, dec_ah2, dec_ph, dec_ph1, dec_ph2);

    /* uppol1: update first predictor coef. (pole setion) */
    dec_ah1 = uppol1 (dec_ah1, dec_ah2, dec_ph, dec_ph1);

    /* recons : compute recontructed signal for adaptive predictor */
    rh = dec_sh + dec_dh;

    /* done with high band decode, implementing delays for next time here */
    dec_rh2 = dec_rh1;
    dec_rh1 = rh;
    dec_ph2 = dec_ph1;
    dec_ph1 = dec_ph;

    /* end of higher sub_band decoder */

    /* end with receive quadrature mirror filters */
    xd = rl - rh;
    xs = rl + rh;

    /* receive quadrature mirror filters implemented here */
    h_ptr = h;
    ac_ptr = accumc;
    ad_ptr = accumd;
    /* main multiply accumulate loop for samples and coefficients */
    for (int j = 0; j < 12; j++)
    {
      int opA1, opB1;
      int opA2, opB2;
      if((int)i==0){
        opA1 = xd;
        opB1 = (*h_ptr++);
        opA2 = xs;
        opB2 = (*h_ptr++);
      }
      else if((int)i==11){
        opA1 = (*ac_ptr++);
        opB1 = (*h_ptr++);
        opA2 = (*ad_ptr++);
        opB2 = (*h_ptr++);
      }
      else{
        opA1 = (*ac_ptr);
        opB1 = (*h_ptr++);
        opA2 = (*ad_ptr);
        opB2 = (*h_ptr++);
      }
      xa1 += (int) opA1 * opB1;
      xa2 += (int) opA2 * opB2;
    }

    /* scale by 2^14 */
    xout1 = xa1 >> 14;
    xout2 = xa2 >> 14;

    /* update delay lines */
    ac_ptr1 = ac_ptr - 1;
    ad_ptr1 = ad_ptr - 1;
    for (j = 0; j < 10; j++)
    {
      *ac_ptr-- = *ac_ptr1--;
      *ad_ptr-- = *ad_ptr1--;
    }
    *ac_ptr = xd;
    *ad_ptr = xs;
    result[i] = xout1;
    result[i + 1] = xout2;
  }
}

  int
main ()
{
  int i;
  int main_result;

  const int test_data[SIZE] = {
    0x44, 0x44, 0x44, 0x44, 0x44,
    0x44, 0x44, 0x44, 0x44, 0x44,
    0x44, 0x44, 0x44, 0x44, 0x44,
    0x44, 0x44, 0x43, 0x43, 0x43,
    0x43, 0x43, 0x43, 0x43, 0x42,
    0x42, 0x42, 0x42, 0x42, 0x42,
    0x41, 0x41, 0x41, 0x41, 0x41,
    0x40, 0x40, 0x40, 0x40, 0x40,
    0x40, 0x40, 0x40, 0x3f, 0x3f,
    0x3f, 0x3f, 0x3f, 0x3e, 0x3e,
    0x3e, 0x3e, 0x3e, 0x3e, 0x3d,
    0x3d, 0x3d, 0x3d, 0x3d, 0x3d,
    0x3c, 0x3c, 0x3c, 0x3c, 0x3c,
    0x3c, 0x3c, 0x3c, 0x3c, 0x3b,
    0x3b, 0x3b, 0x3b, 0x3b, 0x3b,
    0x3b, 0x3b, 0x3b, 0x3b, 0x3b,
    0x3b, 0x3b, 0x3b, 0x3b, 0x3b,
    0x3b, 0x3b, 0x3b, 0x3b, 0x3b,
    0x3b, 0x3b, 0x3c, 0x3c, 0x3c,
    0x3c, 0x3c, 0x3c, 0x3c, 0x3c
  };
  int compressed[SIZE], result[SIZE];
  const int test_compressed[SIZE] = {
    0xfd, 0xde, 0x77, 0xba, 0xf2, 
    0x90, 0x20, 0xa0, 0xec, 0xed, 
    0xef, 0xf1, 0xf3, 0xf4, 0xf5, 
    0xf5, 0xf5, 0xf5, 0xf6, 0xf6, 
    0xf6, 0xf7, 0xf8, 0xf7, 0xf8, 
    0xf7, 0xf9, 0xf8, 0xf7, 0xf9, 
    0xf8, 0xf8, 0xf6, 0xf8, 0xf8, 
    0xf7, 0xf9, 0xf9, 0xf9, 0xf8, 
    0xf7, 0xfa, 0xf8, 0xf8, 0xf7, 
    0xfb, 0xfa, 0xf9, 0xf8, 0xf8
  };
  const int test_result[SIZE] = {
    0, 0xffffffff, 0xffffffff, 0, 0, 
    0xffffffff, 0, 0, 0xffffffff, 0xffffffff, 
    0, 0, 0x1, 0x1, 0, 
    0xfffffffe, 0xffffffff, 0xfffffffe, 0, 0xfffffffc, 
    0x1, 0x1, 0x1, 0xfffffffb, 0x2, 
    0x2, 0x3, 0xb, 0x14, 0x14, 
    0x16, 0x18, 0x20, 0x21, 0x26, 
    0x27, 0x2e, 0x2f, 0x33, 0x32, 
    0x35, 0x33, 0x36, 0x34, 0x37, 
    0x34, 0x37, 0x35, 0x38, 0x36, 
    0x39, 0x38, 0x3b, 0x3a, 0x3f, 
    0x3f, 0x40, 0x3a, 0x3d, 0x3e, 
    0x41, 0x3c, 0x3e, 0x3f, 0x42, 
    0x3e, 0x3b, 0x37, 0x3b, 0x3e, 
    0x41, 0x3b, 0x3b, 0x3a, 0x3b, 
    0x36, 0x39, 0x3b, 0x3f, 0x3c, 
    0x3b, 0x37, 0x3b, 0x3d, 0x41, 
    0x3d, 0x3e, 0x3c, 0x3e, 0x3b, 
    0x3a, 0x37, 0x3b, 0x3e, 0x41, 
    0x3c, 0x3b, 0x39, 0x3a, 0x36
  };

  main_result = 0;
  adpcm_main (test_data,compressed,result);
  for (i = 0; i < IN_END / 2; i++)
  {
    if (compressed[i] != test_compressed[i])
    {
      main_result += 1;
    }
  }/*
  for (i = 0; i < IN_END; i++)
  {
    if (result[i] != test_result[i])
    {
      main_result += 1;
    }
  }*/
  return main_result;
}
