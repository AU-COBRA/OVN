# OVN
Verified implementation of the Open Vote Network protocol

# Hax
Currently using https://github.com/cmester0/hax/tree/ssprove_backend_lib for code extraction to Rocq (SSProve and ConCert)

To regenerate `Hacspec_ovn.v` (and Hacspec_`ovn_Ovn_traits.v`) file(s) do:
```
cargo hax into ssprove
```
in `rust_src/ovn/` and then call `./sed.sh` in `rust_src/ovn/proofs/ssprove`.
Then the new (fixed) files will be in `rust_src/ovn/proofs/ssprove/extraction/`.

