/**********************************************************************
* Felix Winterstein, Imperial College London
*
* File: lloyds_algorithm_top.h
*
* Revision 1.01
* Additional Comments: distributed under a BSD license, see LICENSE.txt
*
**********************************************************************/


#ifndef LLOYDS_ALGORITHM_TOP_H
#define LLOYDS_ALGORITHM_TOP_H

#include <math.h>
#include "ap_int.h" // custom data types

#define D 3         // data dimensionality
#define N 32768     // max. number of data points
#define K 256       // max. number of centres
#define L 6         // max. number of iterations
#define P 40        // parallelisation degree

#define COORD_BITWIDTH 16
#define COORD_BITWITDH_EXT 32
#define NODE_POINTER_BITWIDTH 15    // log2(N)
#define CNTR_INDEX_BITWIDTH 8       // log2(K)

// pointer types to tree nodes and centre lists
typedef ap_uint<NODE_POINTER_BITWIDTH> node_pointer;
typedef ap_uint<CNTR_INDEX_BITWIDTH> centre_index_type;

// force register insertion in the generated RTL for some signals
#define FORCE_REGISTERS
// ... used for saturation
#define MAX_FIXED_POINT_VAL_EXT (1<<(COORD_BITWITDH_EXT-1))-1

typedef unsigned int uint;
typedef ap_int<COORD_BITWIDTH> coord_type;
typedef ap_int<D*COORD_BITWIDTH> coord_type_vector;
typedef ap_int<COORD_BITWITDH_EXT> coord_type_ext;
typedef ap_int<D*COORD_BITWITDH_EXT> coord_type_vector_ext;

//bit width definitions for multiplications
#define MUL_INTEGER_BITS 12
#define MUL_FRACTIONAL_BITS 6
#define MUL_MAX_VAL (1<<(MUL_INTEGER_BITS+MUL_FRACTIONAL_BITS-1))-1
#define MUL_MIN_VAL -1*(1<<(MUL_INTEGER_BITS+MUL_FRACTIONAL_BITS-1))
typedef ap_int<MUL_INTEGER_BITS+MUL_FRACTIONAL_BITS> mul_input_type;

// this should be always 1
#define FILE_INDEX 1

// data point types
struct data_type {
    //coord_type value[D];
    coord_type_vector value;
    data_type& operator=(const data_type& a);
    data_type& operator=(const volatile data_type& a);
};


// data point types ext
struct data_type_ext {
    coord_type_vector_ext value;
    data_type_ext& operator=(const data_type_ext& a);
};


// centre types
struct centre_type {
    data_type_ext wgtCent; // sum of all points assigned to this centre
    coord_type_ext sum_sq; // sum of norm of all points assigned to this centre
    coord_type count;
    centre_type& operator=(const centre_type& a);
};
typedef centre_type* centre_ptr;


#ifdef FORCE_REGISTERS
template<class T>
T Reg(T in) {
    #pragma HLS INLINE off
    #pragma HLS INTERFACE port=return register
    return in;
}
#else
template<class T>
T Reg(T in) {
    #pragma HLS INLINE
    return in;
}
#endif



void lloyds_algorithm_top(  volatile data_type *data,
                            volatile data_type *cntr_pos_init,
                            node_pointer n,
                            centre_index_type k,
                            volatile coord_type_ext *distortion_out,
                            volatile data_type *clusters_out);

void init_node_memory(volatile data_type *node_data, node_pointer n);

void update_centres(centre_type *centres_in,centre_index_type k, data_type *centres_positions_out);

void lloyds (   node_pointer n,
                centre_index_type k,
                centre_type *centres_out);

#endif  /* LLOYDS_ALGORITHM_TOP_H */
