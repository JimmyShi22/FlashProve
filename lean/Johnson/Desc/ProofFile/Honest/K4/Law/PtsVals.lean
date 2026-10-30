-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsVals.lean: three definitions, and statements with their
proofs.

What is here. THE SAMPLED VALUES THAT THE HONEST PARTS OF THE FEED-FORWARD LAYERS' ROUNDS READ
(`ptsOf`, Johnson/Desc/K4/Honest/Front.lean), FIELD BY FIELD, IN THE CHALLENGES' OWN LETTERS: each
field is written of the challenge, or the run of challenges, whose number in the sub-protocol's own
rounds is written out; but fo, which is the input's reader of the lookup at the challenges IN FRONT
of the sub-protocol.

  `masked_zero`, `masked_join`, `zeros_eq`, `joins_eq`   the rounds named "zero" and "join", by
     number
  `elemsAt`, `powersAt`, `innerAt`   a challenge's elements; the powers of its first; the first
     elements of a run of challenges, once all are heard
  `pts_fo_val` … `pts_rhoW_val`   **the sixteen fields**
  `own_take`, `elemsAt_take`, `powersAt_take`, `innerAt_take`   at the challenges in front of the
     sub-protocol and the first n of its own

Limits. Equations between machine words, at every plan and every list of challenges: where a
challenge has not been heard yet the right side is empty as the left is. NO VERIFIER IS NAMED HERE:
that these are the values which the verifier has heard is said in PtsNorms.lean (the norms'
stretch), PtsHear.lean, PtsAt.lean and PtsPow.lean beside this file: for all fields but fo, under
premises (the hearing's return opened, and that the tape has sampled what the challenges hold); of
rhoI, rhoM, om and rhoW, which what the verifier has heard does not hold, they say what the tape's
round has sampled. It stands on StartsAre.lean (the numbers of the rounds "PSC epsilon" and of the
rounds that batch rows).

Kin. How many coordinates five of these fields have: Johnson/Desc/K4/Honest/Law/PtsSizes.lean, which
finds the same rounds by cutting the table in front of them; here they are found by their numbers
(`zeros_eq`, `joins_eq`, and `starts_eq` of StartsAre.lean). `elemsAt` IS IN THE LIBRARY ALREADY, IN
OTHER LETTERS: the trials' kit of this kind has it under the same name, array for array
(Honest/K4/ToyCubeKit.lean, in the trials' namespace); another kind has the same reading as a list,
with a law of the same name as `elemsAt_take` on it, at a list with a front (Honest/K3/Heard.lean,
Honest/K3/HeardLaw.lean). This file builds on none of them; no statement that its writers know of
ties them.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StartsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (RoundName powers orderDefault orderRange ledNS ledNP)
open OnBytes.Desc.First.K4 (Rd rounds masked layerRds pointRd batchRd k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw (idxOf rowsNamed_eq idxOf_cons idxOf_append)

/-! ## 1 The rounds named "zero" and "join" -/

/-- A masked sumcheck has no round named "zero". -/
theorem masked_zero (k a b c s : Nat) : idxOf (masked k a b c) .zero s = [] := by
  unfold masked
  rw [idxOf_append, idxOf_append, idxOf_rep _ _ rfl]
  rfl

/-- Nor one named "join". -/
theorem masked_join (k a b c s : Nat) : idxOf (masked k a b c) .join s = [] := by
  unfold masked
  rw [idxOf_append, idxOf_append, idxOf_rep _ _ rfl]
  rfl

/-- **The rounds named "zero"**: the first; in the first group of layers the next two besides. -/
theorem zeros_eq (Q : K4Pub) :
    rowsNamed Q .zero = if Q.g == 0 then [0, 1, 2] else [0] := by
  rw [rowsNamed_eq]
  unfold rounds layerRds
  by_cases hg : (Q.g == 0) = true
  · simp only [hg, if_true, idxOf_append, idxOf_cons, idxOf_nil, masked_zero, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append]
  · simp only [hg, idxOf_append, idxOf_cons, idxOf_nil, masked_zero, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, if_true, List.append_nil, List.nil_append, List.cons_append,
      Bool.false_eq_true]

/-- **The two rounds named "join"**: each stands just in front of a masked sumcheck. -/
theorem joins_eq (Q : K4Pub) :
    rowsNamed Q .join = [k4StartAt Q 0 - 1, k4StartAt Q 5 - 1] := by
  rw [rowsNamed_eq]
  unfold rounds layerRds k4StartAt k0
  by_cases hg : (Q.g == 0) = true
  · simp only [hg, if_true, idxOf_append, idxOf_cons, idxOf_nil, masked_join, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> first | trivial | omega
  · simp only [hg, if_true, idxOf_append, idxOf_cons, idxOf_nil, masked_join, masked_len,
      List.length_append, List.length_cons, List.length_nil, pointRd, batchRd, beq_iff_eq,
      reduceCtorEq, if_false, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true, Bool.false_eq_true]
    refine ⟨?_, ?_⟩ <;> first | trivial | omega

/-! ## 2 Three readers of a list of challenges -/

/-- The elements of challenge number j; none where it has not been heard. -/
def elemsAt (own : List Fmt.Drawn) (j : Nat) : Array E := ((own[j]?).map elemsOf).getD #[]

/-- The first n powers of the first element of challenge number j; none where there is no such
element. -/
def powersAt (own : List Fmt.Drawn) (j n : Nat) : Array E :=
  (((elemsAt own j)[0]?).map fun x => powers x n).getD #[]

/-- The first elements of the n challenges behind number s; none until all n have been heard. A
challenge without an element reads as 0 (`onesFrom`). The table has such rounds (the seven named
"PSC values"); the six runs that section 3 reads hold none of them: there each row of the table
draws one element, so under `OwnFits` (Johnson/Desc/K4/Honest/Law/PtsSizes.lean) no 0 is read for a
lacking element: by reading; no statement here says so. -/
def innerAt (own : List Fmt.Drawn) (s n : Nat) : Array E := whole n (onesFrom own (s + 1) n)

/-! ## 3 The sixteen fields -/

variable (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn)

theorem pts_fo_val : (ptsOf Q w heard).fo = w.look (heard.take Q.r0) := rfl

theorem pts_PV_val : (ptsOf Q w heard).PV = elemsAt (heard.drop Q.r0) 0 := by
  have hi : (rowsNamed Q .zero)[0]? = some 0 := by
    rw [zeros_eq]
    split <;> rfl
  simp only [ptsOf]
  rw [hi]
  rfl

theorem pts_ZE_val :
    (ptsOf Q w heard).ZE = if Q.g == 0 then elemsAt (heard.drop Q.r0) 1 else #[] := by
  simp only [ptsOf]
  split
  · rename_i hg
    rw [zeros_eq, if_pos hg]
    rfl
  · rfl

theorem pts_tkh_val :
    (ptsOf Q w heard).tkh = if Q.g == 0 then elemsAt (heard.drop Q.r0) 2 else #[] := by
  simp only [ptsOf]
  split
  · rename_i hg
    rw [zeros_eq, if_pos hg]
    rfl
  · rfl

theorem pts_gp_val :
    (ptsOf Q w heard).gp = powersAt (heard.drop Q.r0) (k0 Q.g) (ledNS Q.P.y.h.xl) := by
  simp only [ptsOf]
  rw [bats_eq]
  rfl

theorem pts_rhoI_val : (ptsOf Q w heard).rhoI = elemsAt (heard.drop Q.r0) (k4StartAt Q 0 - 1) := by
  simp only [ptsOf]
  rw [joins_eq]
  rfl

theorem pts_r6_val :
    (ptsOf Q w heard).r6 = levelR Q.P.rd.muV (orderDefault Q.P.rd.muV)
      (innerAt (heard.drop Q.r0) (k4StartAt Q 0) Q.P.rd.muV) := by
  simp only [ptsOf]
  rw [starts_eq]
  rfl

theorem pts_omV_val :
    (ptsOf Q w heard).omV =
      powersAt (heard.drop Q.r0) (k4StartAt Q 1 - 1) (ledNP Q.P.y.h.xl * Q.P.y.NI) := by
  simp only [ptsOf]
  rw [bats_eq]
  rfl

theorem pts_rtV_val :
    (ptsOf Q w heard).rtV = innerAt (heard.drop Q.r0) (k4StartAt Q 1) Q.P.y.h.lt := by
  simp only [ptsOf]
  rw [starts_eq]
  rfl

theorem pts_rt_val :
    (ptsOf Q w heard).rt = innerAt (heard.drop Q.r0) (k4StartAt Q 2) Q.P.y.h.lt := by
  simp only [ptsOf]
  rw [starts_eq]
  rfl

theorem pts_om_val : (ptsOf Q w heard).om = powersAt (heard.drop Q.r0) (k4StartAt Q 3 - 1) 2 := by
  simp only [ptsOf]
  rw [bats_eq]
  rfl

theorem pts_rs_val :
    (ptsOf Q w heard).rs = (innerAt (heard.drop Q.r0) (k4StartAt Q 3) Q.hp.lamS).reverse := by
  simp only [ptsOf]
  rw [starts_eq]
  rfl

theorem pts_r12_val :
    (ptsOf Q w heard).r12 = levelR Q.P.rd.muH (orderRange Q.P.rd.muH)
      (innerAt (heard.drop Q.r0) (k4StartAt Q 4) Q.P.rd.muH) := by
  simp only [ptsOf]
  rw [starts_eq]
  rfl

theorem pts_rhoM_val : (ptsOf Q w heard).rhoM = elemsAt (heard.drop Q.r0) (k4StartAt Q 5 - 1) := by
  simp only [ptsOf]
  rw [joins_eq]
  rfl

theorem pts_r14_val :
    (ptsOf Q w heard).r14 = levelR Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      (innerAt (heard.drop Q.r0) (k4StartAt Q 5) Q.P.rd.muH2) := by
  simp only [ptsOf]
  rw [starts_eq]
  rfl

theorem pts_rhoW_val :
    (ptsOf Q w heard).rhoW = powersAt (heard.drop Q.r0) (k4StartAt Q 6 - 1) Q.hp.NCL := by
  simp only [ptsOf]
  rw [bats_eq]
  rfl

/-! ## 4 At the challenges in front and the first n of the sub-protocol's own -/

/-- h: the challenges in front of the sub-protocol. ds: its own. -/
theorem own_take (h ds : List Fmt.Drawn) (hh : h.length = Q.r0) (n : Nat) :
    (h ++ ds.take n).drop Q.r0 = ds.take n := by
  rw [← hh]
  exact List.drop_left

/-- A challenge that stands among the first n is read as in the whole list. -/
theorem elemsAt_take (ds : List Fmt.Drawn) (j n : Nat) (hj : j < n) :
    elemsAt (ds.take n) j = elemsAt ds j := by
  unfold elemsAt
  rw [List.getElem?_take_of_lt hj]

theorem powersAt_take (ds : List Fmt.Drawn) (j k n : Nat) (hj : j < n) :
    powersAt (ds.take n) j k = powersAt ds j k := by
  unfold powersAt
  rw [elemsAt_take ds j n hj]

/-- So is a run of challenges that ends among the first n. -/
theorem innerAt_take (ds : List Fmt.Drawn) (s k n : Nat) (hj : s + 1 + k ≤ n) :
    innerAt (ds.take n) s k = innerAt ds s k := by
  unfold innerAt onesFrom
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.masked_zero
#print axioms ProofFile.Honest.K4.masked_join
#print axioms ProofFile.Honest.K4.zeros_eq
#print axioms ProofFile.Honest.K4.joins_eq
#print axioms ProofFile.Honest.K4.elemsAt
#print axioms ProofFile.Honest.K4.powersAt
#print axioms ProofFile.Honest.K4.innerAt
#print axioms ProofFile.Honest.K4.pts_fo_val
#print axioms ProofFile.Honest.K4.pts_PV_val
#print axioms ProofFile.Honest.K4.pts_ZE_val
#print axioms ProofFile.Honest.K4.pts_tkh_val
#print axioms ProofFile.Honest.K4.pts_gp_val
#print axioms ProofFile.Honest.K4.pts_rhoI_val
#print axioms ProofFile.Honest.K4.pts_r6_val
#print axioms ProofFile.Honest.K4.pts_omV_val
#print axioms ProofFile.Honest.K4.pts_rtV_val
#print axioms ProofFile.Honest.K4.pts_rt_val
#print axioms ProofFile.Honest.K4.pts_om_val
#print axioms ProofFile.Honest.K4.pts_rs_val
#print axioms ProofFile.Honest.K4.pts_r12_val
#print axioms ProofFile.Honest.K4.pts_rhoM_val
#print axioms ProofFile.Honest.K4.pts_r14_val
#print axioms ProofFile.Honest.K4.pts_rhoW_val
#print axioms ProofFile.Honest.K4.own_take
#print axioms ProofFile.Honest.K4.elemsAt_take
#print axioms ProofFile.Honest.K4.powersAt_take
#print axioms ProofFile.Honest.K4.innerAt_take
