/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Non-restoring unsigned divider                             ////
////                                                             ////
////  Author: Richard Herveille                                  ////
////          richard@asics.ws                                   ////
////          www.asics.ws                                       ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2002 Richard Herveille                        ////
////                    richard@asics.ws                         ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

`timescale 1 ns / 1 ns

module div_unsigned(clock, clken, numer, denom, quotient, remain);

   //
   // parameters
   //
   parameter stages = 32; // controls # of pipeline stages
   localparam width = stages;
   parameter z_width = 2*width; // internally used width

   parameter width_n = width; // width of numerator and quotient <= width
   parameter width_d = width; // width of denominator and remainder <= width

   //
   // inputs & outputs
   //
   input clock;               // system clock
   input clken;               // clock enable

   input [width_n -1:0] numer; // dividend
   input [width_d -1:0] denom; // divisor
   output [width_n -1:0] quotient; // quotient
   output [width_d -1:0] remain; // remainder
   reg [width_n-1:0] 	 quotient = {(width_n){1'b0}};
   reg [width_d-1:0] 	 remain =  {(width_d){1'b0}};

   //
   // functions
   //
   function [z_width:0] gen_s;
      input [z_width:0]  si;
      input [z_width:0]  di;
      begin
	 if(si[z_width])
	   gen_s = {si[z_width-1:0], 1'b0} + di;
	 else
	   gen_s = {si[z_width-1:0], 1'b0} - di;
      end
   endfunction

   function [width-1:0] gen_q;
      input [width-1:0] qi;
      input [z_width:0]   si;
      begin
	 gen_q = {qi[width-2:0], ~si[z_width]};
      end
   endfunction

   function [width-1:0] assign_s;
      input [z_width:0] si;
      input [z_width:0] di;
      reg [z_width:0] 	tmp;
      begin
	 if(si[z_width])
	   tmp = si + di;
	 else
	   tmp = si;

	 assign_s = tmp[z_width-1:z_width-width];
      end
   endfunction

   //
   // variables
   //
   reg [width-1:0] q_pipe  [width-1:0];
   reg [z_width:0]   s_pipe  [width:0];
   reg [z_width:0]   d_pipe  [width:0];

   integer 	     n0, n1, n2;

   // generate divisor (d) pipe
   always @(denom)
     begin
	d_pipe[0] <= {1'b0, {(width-width_d){1'b0}}, denom, {(z_width-width){1'b0}} };
     end

   always @(posedge clock)
     if(clken)
       for(n0=1; n0 <= width; n0=n0+1)
	 d_pipe[n0] <= d_pipe[n0-1];

   // generate internal remainder pipe
   always @(numer)
     begin
	s_pipe[0] <= {{(width){1'b0}}, {(width-width_d){1'b0}}, numer};
     end

   always @(posedge clock)
     if(clken)
       for(n1=1; n1 <= width; n1=n1+1)
	 s_pipe[n1] <= gen_s(s_pipe[n1-1], d_pipe[n1-1]);

   // generate quotient pipe
   always @(posedge clock)
     q_pipe[0] <= 0;

   always @(posedge clock)
     if(clken)
       for(n2=1; n2 < width; n2=n2+1)
	 q_pipe[n2] <= gen_q(q_pipe[n2-1], s_pipe[n2]);


   always @(posedge clock)
     if(clken)
	  quotient <= gen_q(q_pipe[width-1], s_pipe[width]);

   always @(posedge clock)
     if(clken)
       remain <= assign_s(s_pipe[width], d_pipe[width]);
endmodule
