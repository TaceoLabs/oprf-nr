# Noir circuits for TACEO:OPRF

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

This repo contains Noir libraries that implement:

- A BabyJubJub curve gadget library (group operations, subgroup checks, hash-to-curve)
- Circuits/gadgets for an OPRF flow used by the [TACEO:OPRF](https://github.com/TaceoLabs/oprf-service) service, including Chaum–Pedersen DLog equality verification

For a detailed writeup of the OPRF protocol we refer to the [paper](https://github.com/TaceoLabs/oprf-service/blob/main/docs/oprf.pdf).

## Packages

This repository contains two independent Nargo packages:

- `babyjubjub/` (library)
	- Twisted Edwards BabyJubJub operations (`BabyJubJubPoint`): add/double/negate, scalar mul (variable-base)
	- Subgroup check (`check_sub_group`) and scalar-field validation helpers
	- Hash-to-curve (`hash_to_curve::encode`) based on Elligator2 (RFC 9380 style mapping) with cofactor clearing
	- Optimized fixed-base multiplication for the generator (`generator_scalar_mul`) using a window method

- `oprf/` (library)
	- `blinded_query`: derives the blinded query point
	- `dlog`: verifies a Chaum–Pedersen discrete-log equality proof using Poseidon2 as the challenge hash
	- `oprf_output`: end-to-end gadget that checks the proof + unblinding and computes the final output

## High-level protocol shape

At a high level, the `oprf` library helps prove (in-circuit) that:

1. A client input $q$ was mapped to a BabyJubJub point $Q = encode(q)$.
2. The client blinded the query with randomness $\beta$ to get $b_q = \beta \cdot Q$.
3. The OPRF servers responded with a blinded response and a Chaum–Pedersen proof showing consistency with their public key.
4. The client unblinded the response off-circuit (to avoid in-circuit inversion) and the circuit verifies the unblinding.
5. The verified output is derived as a Poseidon2 hash of a domain separator, the query, and the unblinded response point coordinates.

## Testing

We provide a justfile in the root of the repository. Write `just` in your terminal to execute the tests. In case you do not have an installation of `just`, you can `cd` into the directories and write

```bash
nargo test
```

## Disclaimer

This is **experimental software** and is provided on an "as is" and "as available" basis. We do **not give any warranties** and will **not be liable for any losses** incurred through any use of this code base.
