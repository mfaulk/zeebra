pragma circom 2.2.3;
template Roles() {
 signal input used;
 signal input unused[4];
 signal output result;
 signal t;
 t <== used*used;
 result <== t*t;
}
component main = Roles();
