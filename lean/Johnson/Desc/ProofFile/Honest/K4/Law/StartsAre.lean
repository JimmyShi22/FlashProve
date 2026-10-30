-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/StartsAre.lean: THE NUMBERS OF THE ROUNDS AT WHICH THE PUBLIC
TEST ASKS THE MAKERS (`starts`, `rowsNamed`: Johnson/Desc/K4/Honest/Front.lean; `k4MakersFit`,
Honest/K4/Part.lean), WRITTEN OUT: the seven rounds "PSC epsilon" and the four rounds that batch
rows of the verifier's table of the feed-forward layers' rounds (`rounds`,
OnBytes/Desc/First/K4/Rounds.lean), at every plan. The test asks at the seven and at the first two
of the four. A definition, and statements with their proofs.

  `idxOf_rep`, `idxOf_nil`, `idxOf_one`, `masked_len`, `masked_eps`, `masked_bat`   the rows that
     bear a name, in the table's stretches.
  `k4StartAt`, `starts_eq`   **the seven.**
  `bats_eq`   **the four.**

Limits. Equations on a public table. THAT THESE NUMBERS ARE THE MOVES OF THE ROW's PARTS IN FRONT OF
EACH PART IS NOT SAID HERE: `k4_row_nums` (Law/SlotsTrue.lean) has the row's numbers, under names of
its own (rJ1 … rE: Law/SlotsUnder.lean), for all parts named here but the merge's; that its numbers
are `k4StartAt`'s is arithmetic, and is not typed.

Kin. No twin is known to its writers. Of kin: the table's length as a number: `rounds_len`
(Johnson/Road/K4/K4CutRows.lean); the places on the tape at which `hearNorms_tape`
(OnBytes/Desc/First/K4/NormsTape.lean, imported here for `k0`) finds the squares' layer, the second
batching round and the first token sumcheck.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.PtsSizes
import OnBytes.Desc.First.K4.NormsTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (RoundName)
open OnBytes.Desc.First.K4 (Rd rounds masked layerRds pointRd batchRd k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw (idxOf rowsNamed_eq idxOf_cons idxOf_append)

theorem idxOf_rep (r : RoundName) (x : Rd) (hx : (x.name == r) = false) :
    ∀ n k : Nat, idxOf (List.replicate n x) r k = []
  | 0, _ => rfl
  | n + 1, k => by
    rw [List.replicate_succ, idxOf_cons, hx, idxOf_rep r x hx n]
    rfl

theorem idxOf_nil (r : RoundName) (k : Nat) : idxOf [] r k = [] := rfl

theorem idxOf_one (x : Rd) (r : RoundName) (k : Nat) :
    idxOf [x] r k = if x.name == r then [k] else [] := by
  rw [idxOf_cons]
  rfl

theorem masked_len (k a b c : Nat) : (masked k a b c).length = k + 3 := by
  simp [masked]

theorem masked_eps (k a b c s : Nat) : idxOf (masked k a b c) .pscEpsilon s = [s] := by
  unfold masked
  rw [idxOf_append, idxOf_append, idxOf_rep _ _ rfl]
  rfl

theorem masked_bat (k a b c s : Nat) : idxOf (masked k a b c) .batSigma s = [] := by
  unfold masked
  rw [idxOf_append, idxOf_append, idxOf_rep _ _ rfl]
  rfl

/-- The number of the first round of masked sumcheck number k, from 0: each from the one before, by
the rounds that lie between. There are seven, 0 to 6: at every k above 6 it returns number 6's. -/
def k4StartAt (Q : K4Pub) : Nat → Nat
  | 0 => k0 Q.g + 2
  | 1 => k0 Q.g + 2 + (Q.P.rd.muV + 5)
  | 2 => k0 Q.g + 2 + (Q.P.rd.muV + 5) + (Q.P.y.h.lt + 3)
  | 3 => k0 Q.g + 2 + (Q.P.rd.muV + 5) + (Q.P.y.h.lt + 3) + (Q.P.y.h.lt + 4)
  | 4 => k0 Q.g + 2 + (Q.P.rd.muV + 5) + (Q.P.y.h.lt + 3) + (Q.P.y.h.lt + 4) + (Q.hp.lamS + 3)
  | 5 => k0 Q.g + 2 + (Q.P.rd.muV + 5) + (Q.P.y.h.lt + 3) + (Q.P.y.h.lt + 4) + (Q.hp.lamS + 3) +
      (Q.P.rd.muH + 5)
  | _ => k0 Q.g + 2 + (Q.P.rd.muV + 5) + (Q.P.y.h.lt + 3) + (Q.P.y.h.lt + 4) + (Q.hp.lamS + 3) +
      (Q.P.rd.muH + 5) + (Q.P.rd.muH2 + 5)

/-- **The seven rounds "PSC epsilon".** -/
theorem starts_eq (Q : K4Pub) : starts Q = (List.range 7).map (k4StartAt Q) := by
  show starts Q = [k4StartAt Q 0, k4StartAt Q 1, k4StartAt Q 2, k4StartAt Q 3, k4StartAt Q 4,
    k4StartAt Q 5, k4StartAt Q 6]
  unfold starts
  rw [rowsNamed_eq]
  unfold rounds layerRds k4StartAt k0
  by_cases hg : (Q.g == 0) = true
  · simp only [hg, if_true, idxOf_append, idxOf_cons, idxOf_nil, masked_eps, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | omega
  · simp only [hg, idxOf_append, idxOf_cons, idxOf_nil, masked_eps, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true, Bool.false_eq_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | omega

/-- **The four rounds that batch rows**: the first stands two rounds in front of the first masked
sumcheck; each other just in front of one. -/
theorem bats_eq (Q : K4Pub) :
    rowsNamed Q .batSigma =
      [k0 Q.g, k4StartAt Q 1 - 1, k4StartAt Q 3 - 1, k4StartAt Q 6 - 1] := by
  rw [rowsNamed_eq]
  unfold rounds layerRds k4StartAt k0
  by_cases hg : (Q.g == 0) = true
  · simp only [hg, if_true, idxOf_append, idxOf_cons, idxOf_nil, masked_bat, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega
  · simp only [hg, if_true, idxOf_append, idxOf_cons, idxOf_nil, masked_bat, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true, Bool.false_eq_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega

end ProofFile.Honest.K4



#print axioms ProofFile.Honest.K4.idxOf_rep
#print axioms ProofFile.Honest.K4.idxOf_nil
#print axioms ProofFile.Honest.K4.idxOf_one
#print axioms ProofFile.Honest.K4.masked_len
#print axioms ProofFile.Honest.K4.masked_eps
#print axioms ProofFile.Honest.K4.masked_bat
#print axioms ProofFile.Honest.K4.k4StartAt
#print axioms ProofFile.Honest.K4.starts_eq
#print axioms ProofFile.Honest.K4.bats_eq
