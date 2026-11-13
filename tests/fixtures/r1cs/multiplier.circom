pragma circom 2.2.3;

template Multiplier() {
    signal input a;
    signal input b;
    signal output product;
    product <== a * b;
}

component main {public [a]} = Multiplier();
