--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/MovesAtM4.lean: this file defines part of the honest prover: the vector W
that it commits to behind the batching of the rows on the committed matrix. A definition with code;
no theorem.

The batching (kind K13) leaves one claim on the matrix M: < g (x) eq(psi, .), M > + a mask form = a
target. The prover then sends W, said to be g^T M: one entry for each of the 2^k columns. The row
weights g are the claim's. They hang on the challenges of the batching, so W is no part of the
model's computation: it is a function of the matrix and of the claim.
Main name:
  `wEntry mat g e`: entry number e of W: the combination of the matrix's rows at the column e, under
    the weights g; 0 from entry 2^k on.

What is not claimed. Nothing is proved here. `wEntry` is the vector, not W's table: how W is
encoded, where the pad of its OOD sample lies (there an honest sender lays a coin, not 0) and what
its mask rows hold is the sending's matter. A SENDER OWES THE VALUE 0 AT EVERY PLACE OF A ROW FROM
THE CODE's MESSAGE LENGTH ON: no code word holds such a place, while the row of an OOD sample has a
coefficient on it. A table that holds `wEntry` by the entries' numbers meets that where the message
length is a power of two, since the table then has no such place (`table_places`,
Johnson/Desc/K13/Honest/RealPlaces.lean); where it is not, an entry below 2^k may lie at such a
place, and this vector is then no lawful filling. The number nR of the matrix's rows is a free
parameter. The later row (Dot) cuts the row weights at the shape's number of rows (`linDotRow`,
OnBytes/Iop/Lin.lean), so an honest W is `wEntry` at that number: this is proved nowhere. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.K13.Law.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.K13.Law

variable {nR k : ℕ}

/-- **Entry number e of W**: the matrix's rows at the column e, under the weights g; 0 from entry
2^k on. -/
def wEntry (mat : Fin nR → (Fin k → Bool) → GE) (g : List Tensor) (e : ℕ) : GE :=
  if e < 2 ^ k then ∑ i, weights ρg nR g i * mat i (lowBits k e) else 0

end VerifiableInference.Desc.K13.Honest
