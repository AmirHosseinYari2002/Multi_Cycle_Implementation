
// (mult , sll , srl , sra) There are additional instruction that have been implemented.

`timescale 1ns/100ps

   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'b1000
   `define SLL  4'b1001
   `define SRL  4'b1010
   `define SRA  4'b1011
   
module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE, start1 , start_s;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;

   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [3:0] aluOp;
   reg [1:0] PCsrc;
   reg [1:0] aluSelB,RegDst;
   reg [2:0] MemtoReg;
   reg SgnExt, aluSelA, IorD;

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2, Hi, Low, Hiu, Lowu;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt ) begin
         case (PCsrc)
            2'b00: PC <= #0.1 aluResult;
            2'b01: PC <= #0.1 {PC[31:28] , IR[25:0] , 2'b00}; //jump
            2'b10: PC <= #0.1 rfRD1;
         endcase
      end

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;

   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( (IR[31:26] == 6'b000_000  &&  IR[5:3] == 3'b000) ?IR[10:6] : IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR(RegDst[1]? (5'b11111) :(RegDst[0] ? IR[15:11] : IR[20:16])),
      .WD(MemtoReg[2]?PC:(MemtoReg[1]?(MemtoReg[0]? Lowu:Hiu):(MemtoReg[0]?MDR:aluResult)))
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase


   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );

   my_multiplier multiplier(
      .clk (clk),  
      .start(start1),
      .A(A), 
      .B(B),

      .Product({Hiu , Lowu}),
      .ready()
   );
     
   my_multiplier_signed multiplier_signed(
      .clk (clk),  
      .start(start_s),
      .A(A), 
      .B(B),

      .Product({Hi , Low}),
      .ready()
   );


   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BEQ_1 = 25, EX_BEQ_2 = 26, EX_BNE_1 = 5, EX_BNE_2 = 6,
      EX_JL_1 = 30, EX_J_1 = 17, EX_JR_1 = 31, EX_JLR_1 = 24,
      EX_ML_1 = 27, EX_ML_2 = 9, EX_MV_1 = 28;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;

      PCwrt = 0; PCsrc = 2'b00;
      Awrt = 0; Bwrt = 0; start1 = 1'b0;
      RFwrt = 0; IRwrt = 0; start_s = 1'b0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: nxt_state = EX_ALU_R; //sll & srl & sra
                     3'b001:
                     if (IR[2:0] == 3'b000)
                        begin
                           PCsrc = 2'b10;
                           PCwrt = 1'b1;
                           nxt_state = EX_JR_1; //jr
                        end
                     else if (IR[2:0] == 3'b001)begin  //jalr
                           RFwrt = 1'b1;
                           RegDst = 2'b10;
                           MemtoReg = 3'b100;
                           PCsrc = 2'b10;
                           PCwrt = 1'b1;
                           nxt_state = EX_JLR_1;
                        end
                     3'b010: nxt_state = EX_MV_1;  //mflo,mfhi
                     3'b011: nxt_state = EX_ML_1;  //multu & mult
                     3'b100: nxt_state = EX_ALU_R; 
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,             // xori
               6'b001_111:              //lui
                  nxt_state = EX_ALU_I;

               6'b100_011:             //lw
                  nxt_state = EX_LW_1;

               6'b101_011:             //sw
                  nxt_state = EX_SW_1;

               6'b000_100:
                  nxt_state = EX_BEQ_1; //beq
               6'b000_101:
                  nxt_state = EX_BNE_1; //bne

               6'b000_010: begin        //j
                  PCsrc = 2'b01;
                  PCwrt = 1'b1;
                  nxt_state = EX_J_1;
               end

               6'b000_011: begin              //jal
                  RFwrt = 1'b1;
                  RegDst = 2'b10;
                  MemtoReg = 3'b100;
                  PCsrc = 2'b01;
                  PCwrt = 1'b1;
                  nxt_state = EX_JL_1;
               end

               // rest of instructiones should be decoded here

            endcase
         end

         EX_ALU_R: begin
            aluSelA = 1'b1;
            aluSelB = 2'b00;
            RegDst = 2'b01;
            MemtoReg = 3'b000;
            RFwrt = 1'b1;
            case (IR[5:0])
               6'b100_000: // add
                  aluOp = `ADD;
               6'b100_001: //addu
                  aluOp = `ADD;
               6'b100_010: // sub
                  aluOp = `SUB;
               6'b100_011: //subu
                  aluOp = `SUB;
               6'b100_100: // and
                  aluOp = `AND;
               6'b100_101: //or
                  aluOp = `OR;
               6'b100_110: // xor
                  aluOp = `XOR;
               6'b100_111: //nor
                  aluOp = `NOR; 
               6'b101_010: // slt
                  aluOp = `SLT;
               6'b101_011: //sltu
                  aluOp = `SLTU; 
               6'b000_000: //sll
                  aluOp = `SLL;
               6'b000_010: //srl
                  aluOp = `SRL;
               6'b000_011: //sra
                  aluOp = `SRA;
            endcase
            PrepareFetch;
         end

         EX_ALU_I: begin
            aluSelA = 1'b1;
            aluSelB = 2'b10;
            RegDst = 2'b00;
            MemtoReg = 3'b000;
            RFwrt = 1'b1;
            case (IR[31:26])
               6'b001_000: begin // addi
                  SgnExt = 1'b1;
                  aluOp = `ADD;
               end
               6'b001_001: begin // addiu
                  SgnExt = 1'b1;
                  aluOp = `ADD;
               end
               6'b001_010: begin // slti
                  SgnExt = 1'b1;
                  aluOp = `SLT;
               end
               6'b001_011: begin // sltiu
                  SgnExt = 1;
                  aluOp = `SLTU;
               end
               6'b001_100: begin // andi
                  SgnExt = 0;
                  aluOp = `AND;
               end
               6'b001_101: begin // ori
                  SgnExt = 0;
                  aluOp = `OR;
               end
               6'b001_110: begin // xori
                  SgnExt = 0;
                  aluOp = `XOR;
               end
               6'b001_111: begin //lui
                  SgnExt = 0;
                  aluOp = `LUI;
               end
            endcase
            PrepareFetch;
         end

         EX_LW_1: begin
            SgnExt = 1'b1;
            aluSelA = 1'b1;
            aluSelB = 2'b10;
            aluOp = `ADD;
            IorD = 1'b1;
            MARwrt = 1'b1;
            setMRE = 1'b1;
            nxt_state = EX_LW_2;
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            MDRwrt = 1'b1;
            clrMRE = 1'b1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            RegDst = 2'b00;
            MemtoReg = 3'b001;
            RFwrt = 1'b1;
            PrepareFetch;
         end

         EX_SW_1: begin
            SgnExt = 1'b1;
            aluSelA = 1'b1;
            aluSelB = 2'b10;
            aluOp = `ADD;
            setMWE = 1'b1;
            MARwrt = 1'b1;
            IorD = 1;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1'b1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BEQ_1: begin
            aluSelA = 1'b1;
            aluSelB = 2'b00;
            aluOp = `SUB;
            if (aluZero) begin
               nxt_state = EX_BEQ_2;
            end
            else
               PrepareFetch;
         end

         EX_BEQ_2: begin
            aluSelA = 1'b0;
            aluSelB = 2'b11;
            SgnExt = 1'b1;
            aluOp = `ADD;
            IorD = 1'b1;
            setMRE = 1'b1;
            MARwrt = 1'b1;
            PCwrt = 1'b1;
            nxt_state = FETCH1;
         end

         EX_BNE_1: begin
            aluSelA = 1'b1;
            aluSelB = 2'b00;
            aluOp = `SUB;
            if (!aluZero) begin
               nxt_state = EX_BNE_2;
            end
            else
               PrepareFetch;
         end

         EX_BNE_2: begin
            aluSelA = 1'b0;
            aluSelB = 2'b11;
            SgnExt = 1'b1;
            aluOp = `ADD;
            IorD = 1'b1;
            setMRE = 1'b1;
            MARwrt = 1'b1;
            PCwrt = 1'b1;
            nxt_state = FETCH1;
         end

         EX_JR_1: begin // jr
            PrepareFetch;
         end

         EX_MV_1: begin //mflo & mfhi
            RegDst = 2'b01;
            RFwrt = 1'b1;
            case (IR[2:0])
               3'b000: MemtoReg = 3'b010; 
               3'b010: MemtoReg = 3'b011; 
            endcase
            PrepareFetch;
         end

         EX_ML_1: begin //multu & mult
            aluSelA = 1'b1;
            aluSelB = 2'b00;
            case (IR[2:0])
               3'b000: start_s = 1'b1; //mult 
               3'b001: start1 = 1'b1;  //multu 
            endcase
            nxt_state = EX_ML_2;
         end

         EX_ML_2: begin
            start1 = 1'b0;
            start_s = 1'b0;
            case (IR[2:0])
            3'b000: begin //mult
                  if (multiplier_signed.ready) begin
                     PrepareFetch;
                  end
                  else
                     nxt_state = EX_ML_2;
               end
            3'b001: begin //multu
                  if (multiplier.ready) begin
                     PrepareFetch;
                  end
                  else
                     nxt_state = EX_ML_2;
               end
            endcase
         end

         EX_J_1: begin
            PrepareFetch;
         end
         
         EX_JL_1: begin //jal
            PrepareFetch;
         end

         EX_JLR_1: begin //jalr
            PrepareFetch;
         end

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [3:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `LUI : x = {B[15:0],16'h0000};
         `SLL : x = (A << B);
         `SRL : x = (A >> B);
         `SRA : x = {{31{A[31]}} , (A>>B)};
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================

module my_multiplier(
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );

reg [63:0] Multiplicand;
reg [31:0]  Multiplier;
reg [5:0]  counter;

wire product_write_enable;
wire [63:0] adder_output;

assign adder_output = Multiplicand + Product;
assign product_write_enable = Multiplier[0];
assign ready = counter[5];

always @ (posedge clk)

   if(start) begin
      counter <= 6'h0 ;
      Multiplier <= B;
      Product <= 64'h0000_0000;
      Multiplicand <= {32'h0000, A};
   end
   else if(!ready) begin
         counter <= counter + 1;
         Multiplier <= Multiplier >> 1;
         Multiplicand <= Multiplicand << 1;

      if(product_write_enable)
         Product <= adder_output;
   end   

endmodule

//==============================================================================

module my_multiplier_signed(
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );

reg [31:0] Multiplicand ;
reg [5:0]  counter;

reg [31:0] adder_output;
reg sign_bit;

assign ready = counter[5];
always @(*) begin
     if(counter == 6'b011111  &&  sign_bit == 1) begin
        if (!Product[0])
            adder_output = {Product[63] , Product[63:32]} + 33'd0;       
        else
            adder_output = 33'd1 + {Product[63] , Product[63:32]} + (~{Multiplicand[31] , Multiplicand}); 
    end
    else begin
        if (!Product[0])
            adder_output = {Product[63] , Product[63:32]} + 33'd0;
        else
            adder_output = {Product[63] , Product[63:32]} + {Multiplicand[8] , Multiplicand};
    end
end
always @(*) begin
    if (counter == 6'b100000  &&  sign_bit == 1) begin
        Product = Product + 64'd1;
    end
end

always @ (posedge clk)

   if(start) begin
      sign_bit <= B[31];
      counter <= 6'b000000;
      Product <= {{32{B[31]}} , B};
      Multiplicand <=  A;
   end

   else if(!ready) begin
         counter <= counter + 1;
         Product <= {adder_output , Product[31:1]};
   end 

endmodule

