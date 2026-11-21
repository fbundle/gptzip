# Verified arithmetic codec

This standalone Lean 4 library encodes token sequences with exact integer
arithmetic. A model supplies a strictly increasing integer CDF for each context.
The context contains the previously coded tokens in reverse order. The encoder
and decoder use the same model.

Build with `cd lean && lake build`. To try this example, save it as a Lean file
and run `lake env lean /path/to/example.lean` from this directory.

```lean
import Gptzip

open Gptzip

def exampleRoundTrip : Option (List Nat) := do
  let initialCdf ← CDF.ofArray #[0, 1, 3]
  let afterOne ← CDF.ofArray #[0, 3, 4]
  let model : Model := fun context =>
    if context.head? == some 1 then afterOne else initialCdf
  let frame ← encodePacked model [1, 0, 1, 1, 0]
  decodePacked model frame

#eval exampleRoundTrip  -- some [1, 0, 1, 1, 0]
```

`decodePacked_encodePacked` proves that every valid token sequence encodes and
decodes back to itself, including the empty sequence. Validity means that each
token is in the vocabulary for its context. The proof covers exact interval
subdivision, binary search for the token, selection of a terminating binary
fraction, and byte packing.

## Exact arithmetic v1

A Lean `PackedFrame` carries a token count, a payload bit count, and a list
of payload bytes. Each byte contains up to eight consecutive bits, least
significant first, with unused high bits set to zero. Applications that store
frames must supply their own serialization of the counts and a format tag.

`decodePacked_rejects_short_payload` proves that a shortened payload is
rejected when the declared bit count is intact. The codec does not authenticate
payloads or metadata. The proof assumes the same model CDFs on both sides and
does not cover tokenization, model inference, or float-to-integer conversion.

This is an exact reference implementation with arbitrary-precision intervals.
It has its own format and does not read the Python codec's payloads. A
fixed-width streaming implementation with verified renormalization remains
future work.
