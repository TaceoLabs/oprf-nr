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

# fmt
fmt:
    cd babyjubjub && nargo fmt
    cd oprf && nargo fmt
    cd oprf_example && nargo fmt

# check
check:
    cd babyjubjub && nargo check
    cd oprf && nargo check
    cd oprf_example && nargo check
