-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/FreshAtL.lean: the two texts of a fold's fresh table are
one table: part 5's `K1.Ride.lay` (Johnson/Desc/ProofFile/Honest/K1/Coins.lean), by which the finish
of the code switch lays the message, and the library's `packedN` at `hideAt`
(Johnson/Prover/Link/BodyPack.lean; K12/Coins.lean), by which `TestJob.first` lays the test's first
state. One equation, at every list of coefficients.

By what. `freshRow_packedN`, `coefU_byName` (K12/FreshAtJob.lean).

Limits. Within the table alone: rows below 2 ^ h, places below the mask code's message length; where
h ≤ k and 2 k + 1 ≤ h + that length. On the table's entries alone: nothing on the rows' tails, on
which random values the two sides are handed, or on what a column reads. Nothing on completeness,
soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FreshAtJob
import Johnson.Desc.ProofFile.Honest.K1.Coins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light (freshRow_packedN coefU_byName)
open OnBytes.Slice (GE toE ofE readE readE_ofTriple)
open Johnson.Prover.Link (packedN coefU)
open Fmt.M1 (Stage)
open H2K.Pub (sgOf)

/-- **Part 5's laying of a fold's fresh table is the library's packing, entry by entry**, at every
list of coefficients: within the table, where h ≤ k and the rows have room. -/
theorem lay_is_packed (s : Stage) (hk : s.h ≤ s.k) (hroom : 2 * s.k + 1 ≤ s.h + s.Z.l)
    (c : ℕ → GE) (b j : ℕ) (hb : b < 2 ^ s.h) (hj : j < s.Z.l) :
    (⟨s.k, s.h⟩ : K1.Ride).lay c b j =
      packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) c) b j := by
  have hK : (sgOf s).h + (sgOf s).g = s.k := by
    show s.h + (s.k - s.h) = s.k
    omega
  unfold K1.Ride.lay
  rw [freshRow_packedN s hk hroom _ b j hb hj]
  congr 1
  have e := coefU_byName ((sgOf s).h + (sgOf s).g) s.k hK
    (fun n => OnBytes.E.ofTriple (ofE (c n))) c
    (fun n _ => by rw [readE_ofTriple, OnBytes.Slice.toE_ofE])
  unfold hideAt
  rw [hK]
  rw [hK] at e
  exact e

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.lay_is_packed
