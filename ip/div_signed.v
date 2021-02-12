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

module div_signed(clock, clken, numer, denom, quotient, remain);

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

   // added by janders; April 2015
   // spipe1 and spipe2 keep track of whether we need to change the sign
   // of the quotient and remainder
   // inumer, idenom are the numerator and denominator in absolute value
   reg [width-1:0]     spipe1;
   reg [width-1:0] 	 spipe2;
   reg [width-1:0] 	 inumer;
   reg [width-1:0] 	 idenom;

   integer 	     n0, n1, n2;

   // This always block takes the absolute value of the numerator
   always @(numer)
     if (numer[width_n-1])
       inumer = ~numer + 1'b1;
     else
       inumer = numer;

   // Take the absolute value of the denominator
   always @(denom)
     if (denom[width_d-1])
       idenom = ~denom + 1'b1;
     else
       idenom = denom;


   // generate divisor (d) pipe
   always @(idenom)
     begin
	d_pipe[0] 	<= {1'b0, idenom, {(z_width-width){1'b0}} };
     end

   always @(posedge clock)
     if(clken)
       for(n0=1; n0 <= width; n0=n0+1)
	 d_pipe[n0] <= d_pipe[n0-1];

   // generate internal remainder pipe
   always @(inumer)
     begin
	s_pipe[0] <= {{(width){1'b0}}, inumer};
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

   // This is a little tricky.  The spipe1 stores whether the
   // remainder's should be made negative.  In the LLVM srem instruction
   // the remainder takes the sign of the numerator.

   // The spipe2 stores whether the quotient is to be made negative.
   // This follows the usual math semantics.  It should be negative
   // if the signs of the dividend and divisor are different (XOR).

   // Added by janders; April 2015
   integer n,m;
   always @(posedge clock)
     if(clken)
       begin
	  spipe1[0] <= numer[width-1];

	  for(n=1; n < width; n=n+1)
	    spipe1[n] <= spipe1[n-1];

	  spipe2[0] <= numer[width-1] ^ denom[width-1];
	  for(m=1; m < width; m=m+1)
	    spipe2[m] <= spipe2[m-1];
       end

   always @(posedge clock)
     if(clken) // we may need to change the sign of the remainder
       remain <= spipe1[width-1] ? ~assign_s(s_pipe[width], d_pipe[width]) + 1'b1 : assign_s(s_pipe[width], d_pipe[width]);

   always @(posedge clock)
     if(clken) // we may need to change the sign of the quotient
       quotient <= spipe2[width-1] ? ~gen_q(q_pipe[width-1], s_pipe[width]) + 1'b1 : gen_q(q_pipe[width-1], s_pipe[width]);

endmodule
