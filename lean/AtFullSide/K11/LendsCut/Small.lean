-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsCut/Small.lean: the test k11Lends reads of the entries of a book only those that name
a part of the place. So at the place of the kind it can be evaluated at a book with the written rows and
the kind's two entries alone.

  k11Sum, k11Ends      the kind's two entries
  k11BookS             the written rows, with these two entries
  lendsRowAt_of_ahead, lendsRow_of_fields   two books that agree in their rows and in the entries of
                       the parts of a place lend a row at that place alike
  filter_spender       the entries of a part, from those of its place
  k11LendsS, k11LendsS_short   the two evaluations, over two entries

Limits. Closed facts by evaluation in Lean's kernel. A term for the kernel, no book of record.
-/
import AtFullSide.K11.LendsBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Place)
open ProofFile.Honest
open ProofFile.Honest.K11 (k11Lends k11PublicRow)
open AtFullSide.K14 (rawRowsFirstW rawRowsSharedW rawRowsSecondW)

/-- The entry of the sum of the kind's part. -/
def k11Sum : Ahead :=
  ⟨runName maskRowRun ⟨IM.k11Place, 1⟩ "sum", ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 3970⟩, ⟨0, 38⟩,
    ⟨IM.k11Place, 1⟩, true⟩

/-- The entry of the ends of the kind's part. -/
def k11Ends : Ahead :=
  ⟨runName indexMaskRun ⟨IM.k11Place, 1⟩ "ends", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨25848, 8659⟩, ⟨0, 1⟩,
    ⟨IM.k11Place, 1⟩, true⟩

/-- **The written rows, with the kind's two entries.** No book of record. -/
def k11BookS : ProverCoinCounts := ⟨rawRowsFirstW, rawRowsSharedW, rawRowsSecondW, [k11Sum, k11Ends], []⟩

variable {V W X : Type}

/-- Two books whose entries agree at the parts of a place lend a row there alike. -/
theorem lendsRowAt_of_ahead {B B' : ProverCoinCounts} (rows : List (Addr × Due)) (due : Addr → Due) (a : Place)
    (h : ∀ i, (B.ahead.filter fun e => e.spender == ⟨a, i⟩) =
      B'.ahead.filter fun e => e.spender == ⟨a, i⟩) :
    ∀ (ps : List (Part V W X)) (j : Nat),
      lendsRowAt B rows due a ps j = lendsRowAt B' rows due a ps j
  | [], _ => rfl
  | p :: ps, j => by
    simp only [lendsRowAt, lendsPart]
    rw [h j, lendsRowAt_of_ahead rows due a h ps (j + 1)]

/-- **Two books with one set of rows, whose entries agree at the parts of a place, lend a row there
alike.** -/
theorem lendsRow_of_fields {B B' : ProverCoinCounts} (h1 : B.first = B'.first) (h2 : B.shared = B'.shared)
    (h3 : B.second = B'.second) (ch : Nat) (a : Place)
    (h : ∀ i, (B.ahead.filter fun e => e.spender == ⟨a, i⟩) =
      B'.ahead.filter fun e => e.spender == ⟨a, i⟩) (ps : List (Part V W X)) :
    lendsRow B ch a ps = lendsRow B' ch a ps := by
  have e₁ : B.rowsOf ch = B'.rowsOf ch := by
    unfold ProverCoinCounts.rowsOf
    rw [h1, h2, h3]
  have e₂ : lookDue B ch = lookDue B' ch := by
    funext o
    unfold lookDue
    rw [h1, h2, h3]
  unfold lendsRow
  rw [e₁, e₂]
  exact lendsRowAt_of_ahead _ _ a h ps 0

/-- The entries of a part are among those of its place. -/
theorem filter_spender (l : List Ahead) (pl : Place) (i : Nat) :
    (l.filter fun e => e.spender == ⟨pl, i⟩) =
      (l.filter fun e => e.spender.place == pl).filter fun e => e.spender == ⟨pl, i⟩ := by
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  cases hq : (e.spender == (⟨pl, i⟩ : Addr)) with
  | false => rfl
  | true =>
    rw [beq_iff_eq.1 hq]
    simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Over the written rows and the two entries the merge's row is lent.** -/
theorem k11LendsS : k11Lends k11BookS 0 IM.k11Place (k11ParW 18) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: with one column bit fewer the row is not lent. -/
theorem k11LendsS_short : k11Lends k11BookS 0 IM.k11Place (k11ParW 17) = false := by
  decide +kernel

end AtFullSide.K11

#print axioms AtFullSide.K11.k11Sum
#print axioms AtFullSide.K11.k11Ends
#print axioms AtFullSide.K11.k11BookS
#print axioms AtFullSide.K11.lendsRowAt_of_ahead
#print axioms AtFullSide.K11.lendsRow_of_fields
#print axioms AtFullSide.K11.filter_spender
#print axioms AtFullSide.K11.k11LendsS
#print axioms AtFullSide.K11.k11LendsS_short
