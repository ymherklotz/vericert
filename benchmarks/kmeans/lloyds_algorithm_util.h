/**********************************************************************
* Felix Winterstein, Imperial College London
*
* File: lloyds_algorithm_util.h
*
* Revision 1.01
* Additional Comments: distributed under a BSD license, see LICENSE.txt
*
**********************************************************************/

#ifndef LLOYDS_ALGORITHM_UTIL_H
#define LLOYDS_ALGORITHM_UTIL_H

#include "lloyds_algorithm_top.h"


// helper functions
void set_coord_type_vector_item(coord_type_vector *a, const coord_type b, const uint idx);
void set_coord_type_vector_ext_item(coord_type_vector_ext *a, const coord_type_ext b, const uint idx);
coord_type get_coord_type_vector_item(const coord_type_vector a, const uint idx);
coord_type_ext get_coord_type_vector_ext_item(const coord_type_vector_ext a, const uint idx);

data_type conv_long_to_short(data_type_ext p);
data_type_ext conv_short_to_long(data_type p);
mul_input_type saturate_mul_input(coord_type_ext val);
coord_type_ext fi_mul(coord_type_ext op1, coord_type_ext op2);
coord_type_ext tree_adder(coord_type_ext *input_array);
void tree_cs(coord_type_ext *input_array,centre_index_type *index_array,coord_type_ext *res_val,centre_index_type *res_idx,const uint m);
coord_type_ext tree_adder(coord_type_ext *input_array,const uint m);
void compute_distance(data_type p1, data_type p2, coord_type_ext *dist);


#endif  /* LLOYDS_ALGORITHM_UTIL_H */
