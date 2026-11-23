// Independently written combinational specification, with wide signed intermediates.
module reference(
  input wire signed [7:0] w0, w1, w2, w3,
  output wire signed [7:0] out0
);
  wire signed [31:0] p0 = $signed(w0) * $signed(w1);
  wire signed [31:0] p1 = $signed(w2) * $signed(w3);
  wire signed [31:0] acc = p0 + p1;
  wire signed [63:0] rounded = {{32{acc[31]}}, acc} + 64'sd256;
  wire signed [7:0] scaled = $signed(rounded) >>> 9;
  assign out0 = $signed(scaled) < 0 ? 8'sd0 : scaled;
endmodule

module primitive_reference(
  input wire signed [7:0] w0,
  input wire [7:0] w1,
  output wire signed [15:0] out0, out1,
  output wire signed [3:0] out2,
  output wire [3:0] out3,
  output wire [7:0] out4,
  output wire signed [7:0] out5,
  output wire [7:0] out6
);
  wire signed [31:0] sx = w0;
  wire signed [31:0] uy = {1'b0, w1};
  assign out0 = sx * uy;
  assign out1 = -32'sd3 * uy;
  assign out2 = uy - 32'sd128;
  assign out3 = sx < 0 ? 4'd0 : (sx > 15 ? 4'd15 : sx[3:0]);
  assign out4 = 8'd0;
  assign out5 = sx < 0 ? -8'sd1 : 8'sd0;
  assign out6 = 8'd11;
endmodule

// Fixed parameters are deliberately written independently of the Lean lowering.
// Wide mathematical intermediates specify the intended arithmetic for all codes.
module model_reference(
  input wire [7:0] w0, w1,
  output wire signed [7:0] out0
);
  wire signed [63:0] x = $signed({1'b0, w0}) - 64'sd128;
  wire signed [63:0] y = $signed({1'b0, w1}) - 64'sd128;
  wire signed [63:0] acc0 = 64'sd13 + 64'sd4 * x - 64'sd3 * y;
  wire signed [63:0] acc1 = -64'sd16 - 64'sd6 * x + 64'sd5 * y;
  wire signed [63:0] r0 = (acc0 * 64'sd8 + 64'sd32) >>> 6;
  wire signed [63:0] r1 = (acc1 * 64'sd4 + 64'sd32) >>> 6;
  wire signed [63:0] relu0 = r0 < 0 ? 64'sd0 : r0;
  wire signed [63:0] relu1 = r1 < 0 ? 64'sd0 : r1;
  wire signed [63:0] code0 = relu0 + 64'sd3;
  wire signed [63:0] code1 = relu1 + 64'sd3;
  wire signed [63:0] h0 = code0 > 255 ? 64'sd255 : code0;
  wire signed [63:0] h1 = code1 > 255 ? 64'sd255 : code1;
  wire signed [63:0] acc2 = 64'sd18 + 64'sd6 * (h0 - 64'sd3) - 64'sd4 * (h1 - 64'sd3);
  wire signed [63:0] code2 = ((acc2 * 64'sd5 + 64'sd32) >>> 6) - 64'sd5;
  assign out0 = code2 < -128 ? -8'sd128 : (code2 > 127 ? 8'sd127 : code2[7:0]);
endmodule
