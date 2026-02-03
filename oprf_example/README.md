## OPRF example

This directory contains an example implementation of the proof flow for an OPRF-based service.

### Protocol overview

1. **Client proves knowledge of secret**
    - The client proves that they know the preimage to a hash.
    - The hash is provided to the circuit as a **public input**.
    - The client provides the input to the hash function as a **private input**:
    - The circuit verifies that the provided input evaluates to the hash input.

2. **Encode, blind, and query OPRF**
    - The user input is **encoded to the curve** (BabyJubJub here).
    - The encoded point is **blinded** using $\beta$ to get $b_q$.
    - The blinded point is sent to the OPRF nodes as the client’s query input.

3. **OPRF Response computation**
    - The OPRF nodes apply their secret key $k$ to the query point $b_q$ to get $b_q^k$ (check out the [paper](https://github.com/TaceoLabs/oprf-service/blob/main/docs/oprf.pdf) for details), which is sent to the client again.
    - The client unblinds $b_q^k$ by applying $β^{-1}$ and verifies the unblinding in-circuit by injecting the inverse of $\beta$ into the circuit (to avoid in-circuit inverse computation).
    - The client then computes the final (verified) output by applying Poseidon2 to the unblinded point, the original query input (i.e. the address in this case) and a domain separator $ds_n$.

