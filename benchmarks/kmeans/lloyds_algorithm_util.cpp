/**********************************************************************
* Felix Winterstein, Imperial College London
*
* File: lloyds_algorithm_util.cpp
*
* Revision 1.01
* Additional Comments: distributed under a BSD license, see LICENSE.txt
*
**********************************************************************/

#include <math.h>
#include "lloyds_algorithm_util.h"


data_type& data_type::operator=(const data_type& a)
{

    value = a.value;
    return *this;
}

data_type& data_type::operator=(const volatile data_type& a)
{

    value = a.value;
    return *this;
}



data_type_ext& data_type_ext::operator=(const data_type_ext& a)
{
    value = a.value;
    return *this;
}



centre_type& centre_type::operator=(const centre_type& a)
{
    count = a.count;
    wgtCent = a.wgtCent;
    sum_sq = a.sum_sq;
    //position = a.position;
    return *this;
}


void set_coord_type_vector_item(coord_type_vector *a, const coord_type b, const uint idx)
{
    #pragma HLS function_instantiate variable=idx
    a->range((idx+1)*COORD_BITWIDTH-1,idx*COORD_BITWIDTH) = b;
}


void set_coord_type_vector_ext_item(coord_type_vector_ext *a, const coord_type_ext b, const uint idx)
{
    #pragma HLS function_instantiate variable=idx
    a->range((idx+1)*COORD_BITWITDH_EXT-1,idx*COORD_BITWITDH_EXT) = b;
}


coord_type get_coord_type_vector_item(const coord_type_vector a, const uint idx)
{
    #pragma HLS function_instantiate variable=idx
    coord_type tmp= a.range((idx+1)*COORD_BITWIDTH-1,idx*COORD_BITWIDTH);
    return tmp;
}


coord_type_ext get_coord_type_vector_ext_item(const coord_type_vector_ext a, const uint idx)
{
    #pragma HLS function_instantiate variable=idx
    coord_type_ext tmp= a.range((idx+1)*COORD_BITWITDH_EXT-1,idx*COORD_BITWITDH_EXT);
    return tmp;
}


/* ****** helper functions *******/


// conversion from data_type_ext to data_type
data_type conv_long_to_short(data_type_ext p)
{
    #pragma HLS inline
    data_type result;
    for (uint d=0; d<D; d++) {
        #pragma HLS unroll
        coord_type tmp = (coord_type)get_coord_type_vector_ext_item(p.value,d);
        set_coord_type_vector_item(&result.value,tmp,d);
    }
    return result;
}

// conversion from data_type to data_type_ext
data_type_ext conv_short_to_long(data_type p)
{
    #pragma HLS inline
    data_type_ext result;
    for (uint d=0; d<D; d++) {
        #pragma HLS unroll
        coord_type_ext tmp = (coord_type_ext)get_coord_type_vector_item(p.value,d);
        set_coord_type_vector_ext_item(&result.value,tmp,d);
    }
    return result;
}


mul_input_type saturate_mul_input(coord_type_ext val)
{
    #pragma HLS inline
    if (val > MUL_MAX_VAL) {
        val = MUL_MAX_VAL;
    } else if (val < MUL_MIN_VAL) {
        val = MUL_MIN_VAL;
    }
    return (mul_input_type)val;
}


// fixed point multiplication with saturation and scaling
coord_type_ext fi_mul(coord_type_ext op1, coord_type_ext op2)
{
    #pragma HLS inline
    mul_input_type tmp_op1 = saturate_mul_input(op1);
    mul_input_type tmp_op2 = saturate_mul_input(op2);

    ap_int<2*(MUL_INTEGER_BITS+MUL_FRACTIONAL_BITS)> result_unscaled;
    result_unscaled = tmp_op1*tmp_op2;
    #pragma HLS resource variable=result_unscaled core=MulnS

    ap_int<2*(MUL_INTEGER_BITS+MUL_FRACTIONAL_BITS)> result_scaled;
    result_scaled = result_unscaled >> MUL_FRACTIONAL_BITS;
    coord_type_ext result;
    result = (coord_type_ext)result_scaled;
    return result;
}

// tree adder
coord_type_ext tree_adder(coord_type_ext *input_array,const uint m)
{
    #pragma HLS inline

    for(uint j=0;j<ceil(log2(m));j++)
    {
        #pragma HLS unroll
        //printf("j = %d\n",j);
        if (j<ceil(log2(m))-1) {
            for(uint i = 0; i < uint((m+m-uint(m/(1<<(j)))*(1<<(j)))/(1<<(j+1))); i++)
            {
                #pragma HLS unroll
                coord_type_ext tmp1 = input_array[2*i];
                coord_type_ext tmp2 = input_array[2*i+1];
                coord_type_ext tmp3 = tmp1+tmp2;
                input_array[i] = tmp3;
                #pragma HLS resource variable=tmp3 core=AddSubnS
                //printf("[%d] = [%d]+[%d]\n",i,2*i,2*i+1);
            }
            if (m > uint((m+m-uint(m/(1<<(j)))*(1<<(j)))/(1<<(j+1)))*(1<<(j+1))) {
                input_array[uint(m/(1<<(j+1)))] = input_array[uint(m/(1<<(j+1))-1)*2+2];
                //printf("[%d] = [%d]\n",uint(m/(1<<(j+1))),uint(m/(1<<(j+1))-1)*2+2);
            }
        }
        if (j== ceil(log2(m))-1) {
            coord_type_ext tmp1 = input_array[0];
            coord_type_ext tmp2 = input_array[1];
            coord_type_ext tmp3 = tmp1+tmp2;
            input_array[0] = tmp3;
            //printf("[%d] = [%d]+[%d]\n",0,0,1);
            #pragma HLS resource variable=tmp3 core=AddSubnS
        }
    }
    return input_array[0];
}


// tree compare select
void tree_cs(coord_type_ext *input_array,centre_index_type *index_array,coord_type_ext *res_val,centre_index_type *res_idx,const uint m)
{
    #pragma HLS inline

    for(uint j=0;j<ceil(log2(m));j++)
    {
        if (j<ceil(log2(m))-1) {
            for(uint i = 0; i < uint(m/(1<<(j+1))); i++)
            {
                coord_type_ext tmp1 = input_array[2*i];
                coord_type_ext tmp1_idx = index_array[2*i];
                coord_type_ext tmp2 = input_array[2*i+1];
                coord_type_ext tmp2_idx = index_array[2*i+1];
                coord_type_ext tmp3;
                centre_index_type tmp3_idx;
                if (tmp1 < tmp2) {
                    tmp3 = tmp1;
                    tmp3_idx = tmp1_idx;
                } else {
                    tmp3 = tmp2;
                    tmp3_idx = tmp2_idx;
                }

                input_array[i] = tmp3;
                index_array[i] = (tmp3_idx);
            }
            if (m > uint(m/(1<<(j+1)))*(1<<(j+1)) ) {
                input_array[uint(m/(1<<(j+1)))] = (input_array[uint(m/(1<<(j+1))-1)*2+2]);
                index_array[uint(m/(1<<(j+1)))] = (index_array[uint(m/(1<<(j+1))-1)*2+2]);
            }
        }
        if (j== ceil(log2(m))-1) {
            coord_type_ext tmp1 = input_array[0];
            coord_type_ext tmp1_idx = index_array[0];
            coord_type_ext tmp2 = input_array[1];
            coord_type_ext tmp2_idx = index_array[1];
            coord_type_ext tmp3;
            centre_index_type tmp3_idx;
            if (tmp1 < tmp2) {
                tmp3 = tmp1;
                tmp3_idx = tmp1_idx;
            } else {
                tmp3 = tmp2;
                tmp3_idx = tmp2_idx;
            }
            input_array[0] = (tmp3);
            index_array[0] = (tmp3_idx);
        }
    }
    *res_val= input_array[0];
    *res_idx= index_array[0];
}


// compute the Euclidean distance
void compute_distance(data_type p1, data_type p2, coord_type_ext *dist)
{
    #pragma HLS inline

    data_type tmp_p1 = p1;
    data_type tmp_p2 = p2;
    coord_type_ext tmp_mul_res[D];

    for (uint d=0; d<D; d++) {
        #pragma HLS unroll
        coord_type tmp_sub1 = get_coord_type_vector_item(tmp_p1.value,d);
        coord_type tmp_sub2 = get_coord_type_vector_item(tmp_p2.value,d);
        coord_type tmp = tmp_sub1 - tmp_sub2;
        coord_type_ext tmp_ext = (coord_type_ext)tmp;
        coord_type_ext tmp_mul = fi_mul(tmp_ext,tmp_ext);
        tmp_mul_res[d] = tmp_mul;
        #pragma HLS resource variable=tmp core=AddSubnS
        //#pragma HLS resource variable=tmp_mul core=MulnS
    }

    *dist = tree_adder(tmp_mul_res,D);
}




