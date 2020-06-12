// source: https://github.com/FelixWinterstein/Vivado-KMeans/tree/b1121f826bdac8db9502e4bf0c8f3b08425bc061/lloyds_algorithm_HLS/source

/**********************************************************************
* Felix Winterstein, Imperial College London
*
* File: lloyds_algorithm_top.cpp
*
* Revision 1.01
* Additional Comments: distributed under a BSD license, see LICENSE.txt
*
**********************************************************************/

#include "lloyds_algorithm_top.h"
#include "lloyds_algorithm_util.h"


// global array for the data (keep it local to this file)
data_type data_int_memory[N];
data_type centre_positions[K*P];
centre_type centre_buffer[K*P];


// top-level function of the design
void lloyds_algorithm_top(  volatile data_type *data,
                            volatile data_type *cntr_pos_init,
                            node_pointer n,
                            centre_index_type k,
                            volatile coord_type_ext *distortion_out,
                            volatile data_type *clusters_out)
{
    // set the interface properties
    #pragma HLS interface ap_none register port=n
    #pragma HLS interface ap_none register port=k
    #pragma HLS interface ap_fifo port=data depth=256

    #pragma HLS interface ap_fifo port=cntr_pos_init depth=256
    #pragma HLS interface ap_fifo port=distortion_out depth=256
    #pragma HLS interface ap_fifo port=clusters_out depth=256

	/*
    #pragma HLS data_pack variable=data
    #pragma HLS data_pack variable=cntr_pos_init
    #pragma HLS data_pack variable=clusters_out
    */
    #pragma HLS data_pack variable=data_int_memory
    #pragma HLS data_pack variable=centre_positions
    #pragma HLS data_pack variable=centre_buffer

    // specify the type of memory instantiated for these arrays: two-port block ram
    #pragma HLS resource variable=data_int_memory core=RAM_2P_BRAM
    #pragma HLS resource variable=centre_positions core=RAM_2P_BRAM
    #pragma HLS resource variable=centre_buffer core=RAM_2P_LUTRAM

    // partition the arrays according to the parallelism degree P
    // NOTE: the part. factor must be updated if P is changed (in lloyds_alogrithm_top.h) !
    #pragma HLS array_partition variable=centre_buffer block factor=40 dim=1
    #pragma HLS array_partition variable=centre_positions block factor=40 dim=1

    init_node_memory(data,n);

    centre_type filt_centres_out[K];
    data_type new_centre_positions[K];
    // more struct-packing
    #pragma HLS data_pack variable=filt_centres_out
    #pragma HLS data_pack variable=filt_centres_out

    // iterate over a constant number of outer clustering iterations
    it_loop: for (uint l=0; l<L; l++) {

        for (centre_index_type i=0; i<=k; i++) {
            data_type tmp_pos;
            if (l==0) {
                tmp_pos = cntr_pos_init[i];
            } else {
                tmp_pos = new_centre_positions[i];
            }
            for (uint p=0; p<P; p++) {
                #pragma HLS unroll
                centre_positions[p*K+i] = tmp_pos;
            }
            if (i==k) {
                break;
            }
        }

        // run the clustering kernel
        lloyds(n, k, filt_centres_out);

        // re-init centre positions
        update_centres(filt_centres_out, k, new_centre_positions);

    }

    // write clustering output: new cluster centres and distortion
    output_loop: for (centre_index_type i=0; i<=k; i++) {
        #pragma HLS pipeline II=1
        distortion_out[i] = filt_centres_out[i].sum_sq;
        clusters_out[i].value = new_centre_positions[i].value;
        if (i==k) {
            break;
        }
    }
}


// load data points from interface into internal memory
void init_node_memory(volatile data_type *node_data, node_pointer n)
{
    #pragma HLS inline
    for (node_pointer i=0; i<=n; i++) {
        #pragma HLS pipeline II=1
        data_int_memory[i] = node_data[i];
        if (i==n) {
            break;
        }
    }
}


// update the new centre positions after one outer clustering iteration
void update_centres(centre_type *centres_in,centre_index_type k, data_type *centres_positions_out)
{
    #pragma HLS inline
    centre_update_loop: for (centre_index_type i=0; i<=k; i++) {
        #pragma HLS pipeline II=1
        centre_type tmp_cent = Reg(centres_in[i]);
        coord_type tmp_count = tmp_cent.count;
        if ( tmp_count == 0 )
            tmp_count = 1;

        data_type_ext tmp_wgtCent = tmp_cent.wgtCent;
        data_type tmp_new_pos;
        for (uint d=0; d<D; d++) {
            #pragma HLS unroll
            coord_type_ext tmp_div_ext = (get_coord_type_vector_ext_item(tmp_wgtCent.value,d) / tmp_count); //let's see what it does with that...
            coord_type tmp_div = (coord_type) tmp_div_ext;
            #pragma HLS resource variable=tmp_div core=DivnS
            set_coord_type_vector_item(&tmp_new_pos.value,Reg(tmp_div),d);
        }
        centres_positions_out[i] = Reg(tmp_new_pos);
        if (i==k) {
            break;
        }
    }
}


// main clustering kernel
void lloyds (   node_pointer n,
                centre_index_type k,
                centre_type *centres_out)
{
    // register ports of this entity
    #pragma HLS interface port=n register
    #pragma HLS interface port=k register
    #pragma HLS interface port=return register
    #pragma HLS interface ap_memory register port=data_int_memory
    #pragma HLS interface ap_memory register port=centre_positions

    // init centre buffer
    init_centre_buffer_loop: for(centre_index_type i=0; i<=k; i++) {
        #pragma HLS pipeline II=1

        for (uint p=0; p<P;p++) {
            #pragma HLS unroll
            centre_buffer[i+K*p].count = 0;
            centre_buffer[i+K*p].sum_sq = 0;
            data_type_ext tmp;
            for (uint d=0; d<D; d++) {
                #pragma HLS unroll
                set_coord_type_vector_ext_item(&tmp.value,0,d);
            }
            centre_buffer[i+K*p].wgtCent = tmp;
        }

        if (i==k) {
            #pragma HLS occurrence cycle=2
            break;
        }
    }

    data_type u[P];
    #pragma HLS array_partition variable=u complete

    // iterate over all data points
    process_data_points_loop: for (node_pointer i=0; i<=n; i+=P) {

        data_fetch_loop: for (uint p=0; p<P; p++) {
            #pragma HLS pipeline II=1
            u[p] = data_int_memory[i+p];
        }

        centre_index_type final_centre_index[P];
        coord_type_ext sum_sq_out[P];

        // iterate over all centres
        minsearch_loop: for (centre_index_type ii=0; ii<=k; ii++) {
            #pragma HLS pipeline II=1

            par_loop: for (uint p=0; p<P; p++) {
                #pragma HLS unroll
                coord_type_ext min_dist[P];

                #pragma HLS array_partition variable=final_centre_index complete
                #pragma HLS array_partition variable=sum_sq_out complete
                #pragma HLS array_partition variable=min_dist complete

                // help the scheduler by declaring inter-iteration dependencies for these variables as false
                #pragma HLS dependence variable=u inter false
                #pragma HLS dependence variable=final_centre_index inter false
                #pragma HLS dependence variable=sum_sq_out inter false
                #pragma HLS dependence variable=min_dist inter false
                #pragma HLS dependence variable=centre_buffer inter false
                #pragma HLS dependence variable=centre_positions inter false

                if (ii==0) {
                    min_dist[p]=MAX_FIXED_POINT_VAL_EXT;
                }

                coord_type_ext tmp_dist;
                compute_distance(centre_positions[p*K+ii], u[p], &tmp_dist);

                // select the centre with the smallest distance to the data point
                if (tmp_dist<min_dist[p]) {
                    min_dist[p] = tmp_dist;
                    final_centre_index[p] = ii;
                    sum_sq_out[p] = tmp_dist;
                }

                //printf("%d: i=%d, %d, %d\n",p,i.VAL+p,final_centre_index[p].VAL,sum_sq_out[p].VAL);

                if (ii == k) {
                    // trigger at most every other cycle
                    #pragma HLS occurrence cycle=2
                    if (p==P-1) {
                        break;
                    }
                }
            }
        }

        // after minsearch loop: update centre buffer
        for (uint p=0; p<P; p++) {
            #pragma HLS unroll
            data_type_ext tmp_wgtCent;
            coord_type_ext tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
            uint tmp_idx = (final_centre_index[p]+K*p);
            // weighted centroid of this centre
            for (uint d=0; d<D; d++) {
                #pragma HLS unroll
                tmp1 = get_coord_type_vector_ext_item(centre_buffer[(tmp_idx)].wgtCent.value,d);
                //if (i+p<=n) {
                    tmp2 = (coord_type_ext)get_coord_type_vector_item(u[p].value,d);
                //} else {
                    //tmp2 = 0;
                //}
                set_coord_type_vector_ext_item(&tmp_wgtCent.value,Reg(tmp1)+Reg(tmp2),d);
            }
            centre_buffer[tmp_idx].wgtCent = tmp_wgtCent;

            // update number of points assigned to centre
            tmp4 =  centre_buffer[(tmp_idx)].count;
            //if (i+p<=n) {
                tmp3 =  1;
            //} else {
                //tmp3 =  0;
            //}
            centre_buffer[tmp_idx].count = Reg(tmp3) + Reg(tmp4);

            //if (i+p<=n) {
                tmp5 =  sum_sq_out[p];
            //} else {
                //tmp5 =  0;
            //}
            tmp6 =  centre_buffer[(tmp_idx)].sum_sq;
            centre_buffer[tmp_idx].sum_sq  = Reg(tmp5) + Reg(tmp6);
        }

        if (i>=n-P+1) {
        //if (i>=n) {
            break;
        }
    }


    // readout centres
    read_out_centres_loop: for(centre_index_type i=0; i<=k; i++) {
        #pragma HLS pipeline II=1

        coord_type_ext arr_count[P];
        coord_type_ext arr_sum_sq[P];
        coord_type_vector_ext arr_wgtCent[P];
        #pragma HLS array_partition variable=arr_count complete
        #pragma HLS array_partition variable=arr_sum_sq complete
        #pragma HLS array_partition variable=arr_wgtCent complete

        for (uint p=0; p<P; p++) {
            #pragma HLS unroll
            arr_count[p] = ((coord_type_ext)centre_buffer[i+K*p].count);
            arr_sum_sq[p] = (centre_buffer[i+K*p].sum_sq);
            arr_wgtCent[p] = (centre_buffer[i+K*p].wgtCent.value);
        }

        centres_out[i].count = tree_adder(arr_count,P);
        //printf("%d\n",centres_out[i].count.VAL);
        centres_out[i].sum_sq = tree_adder(arr_sum_sq,P);
        coord_type_vector_ext tmp_sum;
        for (uint d=0; d<D; d++) {
            #pragma HLS unroll
            coord_type_ext tmp_a[P];
            for (uint p=0; p<P; p++) {
                #pragma HLS unroll
                tmp_a[p] = get_coord_type_vector_ext_item(arr_wgtCent[p],d);
            }
            coord_type_ext tmp = tree_adder(tmp_a,P);
            set_coord_type_vector_ext_item(&tmp_sum,tmp,d);
        }
        centres_out[i].wgtCent.value = tmp_sum;

        if (i==k) {
            break;
        }
    }

}

