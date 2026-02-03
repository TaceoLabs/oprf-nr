# tests babyjubjub and oprf
test-all: test-babyjubjub test-oprf test-example

# test babyjubjub
test-babyjubjub: 
    cd babyjubjub && nargo test

# test oprf
test-oprf: 
    cd oprf && nargo test

# test example
test-example: 
    cd oprf_example && nargo test
