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
