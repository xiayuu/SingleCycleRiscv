module core (
    input  clk_i,
    input  rst_i,
    input  [31:0] inst_i,
    output [31:0] inst_addr_o,
    output [31:0] data_o,
    output [31:0] data_addr_o,
    output        data_rw_o,
    output [1:0]  data_width_o,
    output        fence_o
);
//assume memory can be read immediately


//PCsel
`define BR    3
`define RIND  2
`define JABS  1
`define PC_4  0

//ALU OP
`define ALU_NONE                                4'b0000
`define ALU_SHIFTL                              4'b0001
`define ALU_SHIFTR                              4'b0010
`define ALU_SHIFTR_ARITH                        4'b0011
`define ALU_ADD                                 4'b0100
`define ALU_SUB                                 4'b0110
`define ALU_AND                                 4'b0111
`define ALU_OR                                  4'b1000
`define ALU_XOR                                 4'b1001
`define ALU_LESS_THAN                           4'b1010
`define ALU_LESS_THAN_SIGNED                    4'b1011


//instru
`define LUI_OP   7'b0110111
`define AUIPC_OP 7'b0010111
`define JAL_OP   7'b1101111
`define JALR_OP  7'b1100111

`define B_OP     7'b1100011
`define BEQ      3'b000
`define BNE      3'b001
`define BLT      3'b100
`define BGE      3'b101
`define BLTU     3'b110
`define BGEU     3'b111

`define L_OP     7'b0000011
`define LB       3'b000
`define LH       3'b001
`define LW       3'b010
`define LBU      3'b100
`define LHU      3'b101

`define S_OP     7'b0100011
`define SB       3'b000
`define SH       3'b001
`define SW       3'b010

`define AI_OP    7'b0010011
`define ADDI     3'b000
`define SLTI     3'b010
`define SLTIU    3'b011
`define XORI     3'b100
`define ORI      3'b110
`define ANDI     3'b111
`define SLLI     3'b001
`define SRLI     3'b101
`define SRAI     3'b101
`define SRLI_F7  7'b0000000
`define SRAI_F7  7'b0100000

`define AR_OP    7'b0110011
`define ADD_F3   3'b000
`define ADD_F7   7'b0000000
`define SUB_F3   3'b000
`define SUB_F7   7'b0100000
`define SLL_F3   3'b001
`define SLL_F7   7'b0000000
`define SLT_F3   3'b010
`define SLT_F7   7'b0000000
`define SLTU_F3  3'b011
`define SLTU_F7  7'b0000000
`define XOR_F3   3'b100
`define XOR_F7   7'b0000000
`define SRL_F3   3'b101
`define SRL_F7   7'b0000000
`define SRA_F3   3'b101
`define SRA_F7   7'b0100000
`define OR_F3    3'b110
`define OR_F7    7'b0000000
`define AND_F3   3'b111
`define AND_F7   7'b0000000

`define FENCE    7'b0001111
`define ECALL    7'b1110011
`define EBREAK   7'b1110011
//decode
wire [6:0] opcode_w;
wire [4:0] rd_w;
wire [2:0] funct3_w;
wire [4:0] rs1_w;
wire [4:0] rs2_w;
wire [6:0] funct7_w;

wire [31:0] wd_w;

assign opcode_w = inst_i[6:0];
assign rd_w     = inst_i[11:7];
assign funct3_w = inst_i[14:12];
assign rs1_w    = inst_i[19:15];
assign rs2_w    = inst_i[24:20];
assign funct7_w = inst_i[31:25];

//ctl
reg [1:0] PCsel;
reg       WAsel;
reg [1:0] WBsel;
reg       Op1sel;
reg       Op2sel;
reg [3:0] ALUsel;
reg [1:0] immsel;

reg [31:0] rd1_w;
reg [31:0] rd2_w;

wire [31:0] pc_next_w;
reg [31:0] result_r;
reg        data_rw_r;
reg        fence_r;
reg [31:0] pc;

assign pc_next_w = {pc[31:2], 2'b0} + 32'd4;
assign data_addr_o = result_r;
assign data_rw_o = data_rw_r;
assign inst_addr_o = pc;
assign fence_o = fence_r;

always @ (posedge clk_i) begin
    case (PCsel)
        `PC_4:
             pc <= pc_next_w;
        `JABS:
             pc <= pc + {{12{funct7_w[6]}}, rs1_w, funct3_w, rs2_w[0], funct7_w[5:0], rs2_w[4:1], 1'b0};
        `RIND:
             pc <= rd1_w + {{20{funct7_w[6]}}, funct7_w, rs2_w[4:1], 1'b0};
        `BR:
             pc <= pc + {{20{funct7_w[6]}}, rd_w[0], funct7_w[5:0], rd_w[4:1], 1'b0};
    endcase
end

//alu
wire [31:0] op2_w;
wire [31:0] op1_w;
wire [31:0] imm_w;

reg [31:0] mem_r;
reg [1:0]  data_width_r;

assign data_width_o = data_width_r;

assign op2_w = Op2sel ? rd2_w : imm_w;
//
assign op1_w = Op1sel ? pc : rd1_w;

//00 I, 01 S, 10/11 U
assign imm_w = immsel[1] ? {funct7_w, rs2_w, rs1_w, funct3_w, 12'b0} : (immsel[0] ? {{20{funct7_w[6]}}, funct7_w, rd_w} : {{20{funct7_w[6]}}, funct7_w, rs2_w});

//00 PC, 01 alu result, 10/11 mem
assign wd_w = WBsel[1] ? mem_r : (WBsel[0] ? result_r : pc_next_w);

always @ * begin
    mem_r = data_o;
    if (funct3_w == `LH || funct3_w == `SH) begin
        mem_r = {{16{data_o[15]}}, data_o[15:0]};
        data_width_r = 2'b01;
    end
    else if (funct3_w == `LHU) begin
        mem_r = {16'b0000000000000000, data_o[15:0]};
        data_width_r = 2'b01;
    end
    else if (funct3_w == `LB || funct3_w == `SB) begin
        mem_r = {{24{data_o[7]}}, data_o[7:0]};
        data_width_r = 2'b11;
    end
    else if (funct3_w == `LBU) begin
        mem_r = {24'b000000000000000000000000, data_o[7:0]};
        data_width_r = 2'b11;
    end
end


//ctl logic
function [0:0] less_than_signed;
    input [31:0] x;
    input [31:0] y;
    reg [31:0] v;
begin
    v = (x - y);
    if (x[31] != y[31])
        less_than_signed = x[31];
    else
        less_than_signed = v[31];
end
endfunction

function [0:0] greater_than_signed;
    input [31:0] x;
    input [31:0] y;
    reg [31:0] v;
begin
    v = (y - x);
    if (x[31] != y[31])
        greater_than_signed = y[31];
    else
        greater_than_signed = v[31];
end
endfunction

reg branch_token_r;

always @ * begin
    branch_token_r = 0;
    if (funct3_w == `BEQ) begin
        branch_token_r = (rd1_w == rd2_w);
    end
    else if (funct3_w == `BNE) begin
        branch_token_r = (rd1_w != rd2_w);
    end
    else if (funct3_w == `BLT) begin
        branch_token_r = less_than_signed(rd2_w, rd1_w);
    end
    else if (funct3_w == `BGE) begin
        branch_token_r = greater_than_signed(rd2_w, rd1_w) | (rd2_w == rd1_w);
    end
    else if (funct3_w == `BLTU) begin
        branch_token_r = (rd2_w < rd1_w);
    end
    else if (funct3_w == `BGEU) begin
        branch_token_r = (rd2_w >= rd1_w);
    end
end

always @ * begin
    PCsel = `PC_4;
    WAsel = 0;
    WBsel = 2'b00;
    data_rw_r = 0;
    immsel = 2'b00;
    Op2sel = 0;
    Op1sel = 0;
    ALUsel = `ALU_NONE;

    if (opcode_w == `JAL_OP) begin
        PCsel = `JABS;
        WAsel = 1;
        WBsel = 2'b00;
        data_rw_r = 0;
    end
    else if (opcode_w == `JALR_OP) begin
        PCsel = `RIND;
        immsel = 2'b00;
        WAsel = 1;
        WBsel = 2'b00;
        data_rw_r = 0;
    end
    else if (opcode_w == `B_OP && branch_token_r) begin
        PCsel = `BR;
        WAsel = 1;
        WBsel = 2'b00;
        data_rw_r = 0;
    end
    else if (opcode_w == `LUI_OP) begin
        immsel = 2'b10;
        Op2sel = 0;
        ALUsel = `ALU_NONE;
        WAsel  = 1;
        WBsel  = 2'b01;
        data_rw_r = 0;
    end
    else if (opcode_w == `AUIPC_OP) begin
        immsel = 2'b10;
        Op1sel = 1;
        Op2sel = 0;
        WAsel  = 1;
        WBsel  = 2'b01;
        data_rw_r = 0;
    end
    else if (opcode_w == `L_OP) begin
        immsel = 2'b00;
        Op1sel = 0;
        Op2sel = 0;
        ALUsel = `ALU_ADD;
        WAsel  = 1;
        WBsel  = 2'b10;
        data_rw_r = 0;
    end
    else if (opcode_w == `S_OP) begin
        immsel = 2'b01;
        Op1sel = 0;
        Op2sel = 0;
        ALUsel = `ALU_ADD;
        WAsel  = 0;
        data_rw_r = 1;
    end
    else if (opcode_w == `AI_OP) begin
        immsel = 2'b00;
        Op1sel = 0;
        Op2sel = 0;
        WAsel  = 1;
        WBsel  = 2'b01;
        data_rw_r = 0;
        case (funct3_w)
            `ADDI:
                 ALUsel = `ALU_ADD;
            `SLTI:
                 ALUsel = `ALU_LESS_THAN_SIGNED;
            `SLTIU:
                 ALUsel = `ALU_LESS_THAN;
            `XORI:
                 ALUsel = `ALU_XOR;
            `ORI:
                 ALUsel = `ALU_OR;
            `ANDI:
                 ALUsel = `ALU_AND;
            `SLLI:
                 ALUsel = `ALU_SHIFTL;
            `SRLI:
                 ALUsel = (funct7_w == `SRLI_F7) ?  `ALU_SHIFTR : `ALU_SHIFTR_ARITH;
        endcase
    end
    else if (opcode_w == `AR_OP) begin
        Op1sel = 0;
        Op2sel = 1;
        WAsel  = 1;
        WBsel  = 2'b01;
        data_rw_r = 0;
        case (funct3_w)
            `ADD_F3:
                 ALUsel = (funct7_w == `ADD_F7) ? `ALU_ADD : `ALU_SUB;
            `SLT_F3:
                 ALUsel = `ALU_LESS_THAN_SIGNED;
            `SLTU_F3:
                 ALUsel = `ALU_LESS_THAN;
            `XOR_F3:
                 ALUsel = `ALU_XOR;
            `OR_F3:
                 ALUsel = `ALU_OR;
            `AND_F3:
                 ALUsel = `ALU_AND;
            `SLL_F3:
                 ALUsel = `ALU_SHIFTL;
            `SRL_F3:
                 ALUsel = (funct7_w == `SRL_F7) ? `ALU_SHIFTR : `ALU_SHIFTR_ARITH;
        endcase
    end
    else if (opcode_w == `FENCE) begin
        WAsel  = 0;
        fence_r= 1;
    end
//    else if (opcode_w == `ECALL) begin
//        WAsel  = 0;
//    end
//    else if (opcode_w == `EBREAK) begin
//        WAsel  = 0;
//    end
end

// ALU copy from Ultra-Embedded/riscv

reg [31:16]     shift_right_fill_r;
reg [31:0]      shift_right_1_r;
reg [31:0]      shift_right_2_r;
reg [31:0]      shift_right_4_r;
reg [31:0]      shift_right_8_r;

reg [31:0]      shift_left_1_r;
reg [31:0]      shift_left_2_r;
reg [31:0]      shift_left_4_r;
reg [31:0]      shift_left_8_r;

wire [31:0]     sub_res_w = op1_w - op2_w;


always @ *
begin
    shift_right_fill_r = 16'b0;
    shift_right_1_r = 32'b0;
    shift_right_2_r = 32'b0;
    shift_right_4_r = 32'b0;
    shift_right_8_r = 32'b0;

    shift_left_1_r = 32'b0;
    shift_left_2_r = 32'b0;
    shift_left_4_r = 32'b0;
    shift_left_8_r = 32'b0;

    case (ALUsel)
       //----------------------------------------------
       // Shift Left
       //----------------------------------------------   
       `ALU_SHIFTL :
       begin
            if (op2_w[0] == 1'b1)
                shift_left_1_r = {op1_w[30:0],1'b0};
            else
                shift_left_1_r = op1_w;

            if (op2_w[1] == 1'b1)
                shift_left_2_r = {shift_left_1_r[29:0],2'b00};
            else
                shift_left_2_r = shift_left_1_r;

            if (op2_w[2] == 1'b1)
                shift_left_4_r = {shift_left_2_r[27:0],4'b0000};
            else
                shift_left_4_r = shift_left_2_r;

            if (op2_w[3] == 1'b1)
                shift_left_8_r = {shift_left_4_r[23:0],8'b00000000};
            else
                shift_left_8_r = shift_left_4_r;

            if (op2_w[4] == 1'b1)
                result_r = {shift_left_8_r[15:0],16'b0000000000000000};
            else
                result_r = shift_left_8_r;
       end
       //----------------------------------------------
       // Shift Right
       //----------------------------------------------
       `ALU_SHIFTR, `ALU_SHIFTR_ARITH:
       begin
            // Arithmetic shift? Fill with 1's if MSB set
            if (op1_w[31] == 1'b1 && ALUsel == `ALU_SHIFTR_ARITH)
                shift_right_fill_r = 16'b1111111111111111;
            else
                shift_right_fill_r = 16'b0000000000000000;

            if (op2_w[0] == 1'b1)
                shift_right_1_r = {shift_right_fill_r[31], op1_w[31:1]};
            else
                shift_right_1_r = op1_w;

            if (op2_w[1] == 1'b1)
                shift_right_2_r = {shift_right_fill_r[31:30], shift_right_1_r[31:2]};
            else
                shift_right_2_r = shift_right_1_r;

            if (op2_w[2] == 1'b1)
                shift_right_4_r = {shift_right_fill_r[31:28], shift_right_2_r[31:4]};
            else
                shift_right_4_r = shift_right_2_r;

            if (op2_w[3] == 1'b1)
                shift_right_8_r = {shift_right_fill_r[31:24], shift_right_4_r[31:8]};
            else
                shift_right_8_r = shift_right_4_r;

            if (op2_w[4] == 1'b1)
                result_r = {shift_right_fill_r[31:16], shift_right_8_r[31:16]};
            else
                result_r = shift_right_8_r;
       end       
       //----------------------------------------------
       // Arithmetic
       //----------------------------------------------
       `ALU_ADD : 
       begin
            result_r      = (op1_w + op2_w);
       end
       `ALU_SUB : 
       begin
            result_r      = sub_res_w;
       end
       //----------------------------------------------
       // Logical
       //----------------------------------------------       
       `ALU_AND : 
       begin
            result_r      = (op1_w & op2_w);
       end
       `ALU_OR  : 
       begin
            result_r      = (op1_w | op2_w);
       end
       `ALU_XOR : 
       begin
            result_r      = (op1_w ^ op2_w);
       end
       //----------------------------------------------
       // Comparision
       //----------------------------------------------
       `ALU_LESS_THAN : 
       begin
            result_r      = (op1_w < op2_w) ? 32'h1 : 32'h0;
       end
       `ALU_LESS_THAN_SIGNED : 
       begin
            if (op1_w[31] != op2_w[31])
                result_r  = op1_w[31] ? 32'h1 : 32'h0;
            else
                result_r  = sub_res_w[31] ? 32'h1 : 32'h0;            
       end
       default  : 
       begin
            result_r      = op2_w;
       end
    endcase
end

//reg
reg [31:0] x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31;

always @ * begin
    case (rs1_w)
        5'd0: rd1_w = 32'b0;
        5'd1: rd1_w = x1;
        5'd2: rd1_w = x2;
        5'd3: rd1_w = x3;
        5'd4: rd1_w = x4;
        5'd5: rd1_w = x5;
        5'd6: rd1_w = x6;
        5'd7: rd1_w = x7;
        5'd8: rd1_w = x8;
        5'd9: rd1_w = x9;
        5'd10: rd1_w = x10;
        5'd11: rd1_w = x11;
        5'd12: rd1_w = x12;
        5'd13: rd1_w = x13;
        5'd14: rd1_w = x14;
        5'd15: rd1_w = x15;
        5'd16: rd1_w = x16;
        5'd17: rd1_w = x17;
        5'd18: rd1_w = x18;
        5'd19: rd1_w = x19;
        5'd20: rd1_w = x20;
        5'd21: rd1_w = x21;
        5'd22: rd1_w = x22;
        5'd23: rd1_w = x23;
        5'd24: rd1_w = x24;
        5'd25: rd1_w = x25;
        5'd26: rd1_w = x26;
        5'd27: rd1_w = x27;
        5'd28: rd1_w = x28;
        5'd29: rd1_w = x29;
        5'd30: rd1_w = x30;
        5'd31: rd1_w = x31;
    endcase
end

always @ * begin
    case (rs2_w)
        5'd0: rd2_w = 32'b0;
        5'd1: rd2_w = x1;
        5'd2: rd2_w = x2;
        5'd3: rd2_w = x3;
        5'd4: rd2_w = x4;
        5'd5: rd2_w = x5;
        5'd6: rd2_w = x6;
        5'd7: rd2_w = x7;
        5'd8: rd2_w = x8;
        5'd9: rd2_w = x9;
        5'd10: rd2_w = x10;
        5'd11: rd2_w = x11;
        5'd12: rd2_w = x12;
        5'd13: rd2_w = x13;
        5'd14: rd2_w = x14;
        5'd15: rd2_w = x15;
        5'd16: rd2_w = x16;
        5'd17: rd2_w = x17;
        5'd18: rd2_w = x18;
        5'd19: rd2_w = x19;
        5'd20: rd2_w = x20;
        5'd21: rd2_w = x21;
        5'd22: rd2_w = x22;
        5'd23: rd2_w = x23;
        5'd24: rd2_w = x24;
        5'd25: rd2_w = x25;
        5'd26: rd2_w = x26;
        5'd27: rd2_w = x27;
        5'd28: rd2_w = x28;
        5'd29: rd2_w = x29;
        5'd30: rd2_w = x30;
        5'd31: rd2_w = x31;
    endcase
end

always @ (posedge clk_i) begin
    if (WAsel) begin
    case (rd_w)
        5'd0: x0 <= 32'b0;
        5'd1: x1 <= wd_w;
        5'd2: x2 <= wd_w;
        5'd3: x3 <= wd_w;
        5'd4: x4 <= wd_w;
        5'd5: x5 <= wd_w;
        5'd6: x6 <= wd_w;
        5'd7: x7 <= wd_w;
        5'd8: x8 <= wd_w;
        5'd9: x9 <= wd_w;
        5'd10: x10 <= wd_w;
        5'd11: x11 <= wd_w;
        5'd12: x12 <= wd_w;
        5'd13: x13 <= wd_w;
        5'd14: x14 <= wd_w;
        5'd15: x15 <= wd_w;
        5'd16: x16 <= wd_w;
        5'd17: x17 <= wd_w;
        5'd18: x18 <= wd_w;
        5'd19: x19 <= wd_w;
        5'd20: x20 <= wd_w;
        5'd21: x21 <= wd_w;
        5'd22: x22 <= wd_w;
        5'd23: x23 <= wd_w;
        5'd24: x24 <= wd_w;
        5'd25: x25 <= wd_w;
        5'd26: x26 <= wd_w;
        5'd27: x27 <= wd_w;
        5'd28: x28 <= wd_w;
        5'd29: x29 <= wd_w;
        5'd30: x30 <= wd_w;
        5'd31: x31 <= wd_w;
    endcase
    end
end


endmodule
