-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpecStages.lean: the honest side of the kind "lookup" (K3): the
hypothesis that the statement on the masked sumcheck asks of a caller (`SumsTo`,
Honest/SumLaw/Terms.lean), at each of the specification's five jobs, with the verifier's own
variables. Theorems.

Terms. Honest/K3/GLOSSARY.md ("specification", "job, summand", "lawful", "relation after the
challenge").

What is shown. Honest/K3/JobsSpecSums.lean carries `Job.Lawful` (Johnson/HonestTrace/LookDefs.lean)
to that hypothesis, if the job's lists are as long as its degrees say (`JobSized`) and the caller's
variables are the job's (`VarsFit`). This file shows both for the tie's steps, the levels of the two
trees, the leaves and the bits, at the variables that the verifier's text makes
(`First.ProdV.levelVars`, `K3.leafVars`, `K3.bitsCall`), takes `Job.Lawful` of the five jobs from
Johnson/HonestTrace/LookCube.lean and Johnson/HonestTrace/LookJobs.lean, and states the results.
  1 `perm_of_orderOk`, `perm_orderDefault`: the verifier's test on an order gives the
    specification's hypothesis on it.
  2 `sized_tie`, `sized_pj`, `sized_leaves`, `sized_bits`: `JobSized`.
  3 `varsFit_map`, `varsFit_level`, `varsFit_leaves`, `varsFit_bits` (helper: `ups_toList`):
    `VarsFit`.
  4 `tie_sums`, `level_sums` (both trees' levels), `leaves_sums`, `bits_sums`: the hypothesis at the
    five jobs.

Hypotheses that remain.
  `hM`: (in `tie_sums`) the relation after the challenge (`Data.Mid`).
  In all: tests of orders and sizes of points: `h`, `ho`, `hE`, `hB`: the order passes the
    verifier's test, has its length, is a permutation, or is the default order; `hz`, `hr`, `hm`:
    the point, the challenges and the mask entries are as many as they should be; `hw`, `hd`: the
    data's numbers w and d are the face's mu and d; `hs`: (in `tie_sums`) s ≤ n. In `varsFit_map`:
    `hz`, `hd`: the job's points and degrees are the list's.

Imported. Honest/SumLaw/Terms.lean lies beneath this file.

Users. Honest/K3/Law/SpecMember.lean calls `perm_of_orderOk`.

Limits. `tie_sums` is conditional on the relation after the challenge (`Data.Mid`); all are
conditional on tests of orders and on sizes of points, which are hypotheses here. What the true sums
and the summands at the shown values come to in the verifier's terms is not said here. Shown in:
Honest/K3/Law/SpecValues.lean (`endTerm_tie0`, `endTerm_tie`, `endTerm_level`, `endTerm_bits` and
others).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecSums
import Johnson.HonestTrace.LookJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE)
open OnBytes.Model (orderDefault)
open OnBytes.HonestTrace.Look (Job Data pj tieJob keyJob tabJob leavesJob bitsJob shownL)
open ProofFile.Honest.SumLaw (SumsTo)
open VerifiableInference.Desc.Part.MaskedSum (Var)
open VerifiableInference.Desc.First.ProdV (levelVars orderOk)
open VerifiableInference.Desc.K3 (leafVars bitsCall)

variable {P : Type}

/-! ## 1 Orders -/

/-- The verifier's test on an order gives what the specification's statements ask: the order lists
the numbers below m, each once. -/
theorem perm_of_orderOk {m : Nat} {o : List Nat} (h : orderOk m o = true) :
    o.Perm (List.range m) := by
  obtain ⟨_, hlt, hcnt⟩ := VerifiableInference.Desc.First.ProdV.orderOk_facts h
  rw [List.perm_iff_count]
  intro a
  by_cases ha : a < m
  · rw [hcnt a ha, List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 ha)]
  · rw [List.count_eq_zero_of_not_mem (fun hm => ha (hlt a hm)),
      List.count_eq_zero_of_not_mem (fun hm => ha (List.mem_range.1 hm))]

/-- The order that counts down lists the numbers below m, each once. -/
theorem perm_orderDefault (m : Nat) : (orderDefault m).Perm (List.range m) :=
  List.reverse_perm _

/-! ## 2 The jobs' lists are as long as their degrees say -/

/-- A step of the tie: no variable; four coefficients in Y at the most. -/
theorem sized_tie (D : Data P KE) (s : Nat) : JobSized (tieJob D s) := by
  refine ⟨rfl, fun rs h => absurd h (Nat.not_lt_zero _), fun dY hY xs m => ?_⟩
  have e : dY = 3 := (Option.some.inj hY).symm
  subst e
  show (if s = 0 then _ else _ : List KE).length ≤ 4
  split <;> simp [OnBytes.HonestTrace.Look.sqMul, OnBytes.HonestTrace.Look.addP]

/-- The job of a product of two halves: three coefficients in each round and in Y, where the order
has as many members as there are variables. -/
theorem sized_pj (m : Nat) (k : KE) (A B : Nat → KE) (o : List Nat) (z : List KE)
    (ho : o.length = m) : JobSized (pj m k A B o z) := by
  refine ⟨?_, fun rs h => ?_, fun dY hY xs mk => ?_⟩
  · show (List.replicate m 2).length = (TwV.inRounds o z).length
    simp [TwV.inRounds, ho]
  · have h' : rs.length < m := by
      have : (TwV.inRounds o z).length = m := by simp [TwV.inRounds, ho]
      rw [← this]; exact h
    show (OnBytes.HonestTrace.Look.pjRound m k A B o z rs).length ≤
      (List.replicate m 2).getD rs.length 0 + 1
    rw [List.getD_eq_getElem _ _ (by simpa using h'), List.getElem_replicate]
    simp [OnBytes.HonestTrace.Look.pjRound]
  · have e : dY = 2 := (Option.some.inj hY).symm
    subst e
    show (List.length [_, _, _]) ≤ 3
    simp

/-- The leaves: three coefficients in a row's bit, two in a plane's. -/
theorem sized_leaves (D : Data P KE) (z : List KE) : JobSized (leavesJob D z) := by
  refine ⟨?_, fun rs h => ?_, fun dY hY => absurd hY (by simp [leavesJob])⟩
  · show (TwV.dgE D.N).length = (TwV.inRounds D.N.oE z).length
    simp [TwV.dgE, TwV.inRounds]
  · have h' : rs.length < D.N.oE.length := by
      have : (TwV.inRounds D.N.oE z).length = D.N.oE.length := by simp [TwV.inRounds]
      rw [← this]; exact h
    show ((OnBytes.HonestTrace.Look.pjRound (D.N.w + D.N.d) 1 D.bitAt D.rowAt D.N.oE z rs).take
      (if D.N.oE.getD rs.length 0 < D.N.w then 2 else 3)).length ≤
        (TwV.dgE D.N).getD rs.length 0 + 1
    have e : (TwV.dgE D.N).getD rs.length 0 =
        if D.N.oE.getD rs.length 0 < D.N.w then 1 else 2 := by
      unfold TwV.dgE
      rw [List.getD_eq_getElem _ _ (by simpa using h'), List.getElem_map,
        List.getD_eq_getElem _ _ h']
    rw [e, List.length_take]
    split <;> omega

/-- The bits: as the job of a product. -/
theorem sized_bits (D : Data P KE) (z : List KE) (ho : D.N.oB.length = D.N.w + D.N.d) :
    JobSized (bitsJob D z) := by
  have h := sized_pj (D.N.w + D.N.d) 0 D.bitAt (fun X => D.bitAt X - 1) D.N.oB z ho
  refine ⟨h.dg, h.round, fun dY hY xs mk => ?_⟩
  have e : dY = 2 := (Option.some.inj hY).symm
  subst e
  show (List.length [_, _, _]) ≤ 3
  simp

/-! ## 3 The verifier's variables are the jobs' -/

/-- Variables that are made member by member of a list. -/
theorem varsFit_map {α : Type} (l : List α) (g : α → E) (dd : α → Nat) (J : Job KE)
    (hz : J.zs = l.map fun b => up (g b)) (hd : J.dg = l.map dd) :
    VarsFit (l.map fun b => Var.point (g b) (dd b + 1)) J := by
  refine ⟨by rw [hz, List.length_map, List.length_map], fun i hi => ?_⟩
  have hi' : i < l.length := by simpa using hi
  refine ⟨g l[i], ?_, ?_⟩
  · rw [hd, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
      List.getElem?_map, List.getElem?_eq_getElem hi']
    rfl
  · rw [hz, List.getElem?_map, List.getElem?_eq_getElem hi']
    rfl

/-- **A level's variables** are those of the job of a product of two halves at the translated
point. -/
theorem varsFit_level (m : Nat) (k : KE) (A B : Nat → KE) (o : List Nat) (z : Array E)
    (hz : z.size = m) (ho : o.Perm (List.range m)) :
    VarsFit (levelVars m z o) (pj m k A B o (byBit z)) := by
  have hlt : ∀ b ∈ o, b < m := fun b hb => List.mem_range.1 (ho.mem_iff.1 hb)
  refine varsFit_map o (fun b => z.getD (m - 1 - b) zeroE) (fun _ => 2) _ ?_ ?_
  · show TwV.inRounds o (byBit z) = _
    unfold TwV.inRounds
    refine List.map_congr_left fun b hb => ?_
    rw [byBit_getD z b (by rw [hz]; exact hlt b hb), hz]
  · show List.replicate m 2 = _
    rw [List.map_const', ho.length_eq, List.length_range]

/-- An array's members, read one by one. -/
theorem ups_toList (z : Array E) :
    ups z.toList = (List.range z.size).map fun j => up (z.getD j zeroE) := by
  unfold ups
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < z.size := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp

/-- **The leaves' variables** are those of the leaves' job at the translated point, where the job's
order counts down. -/
theorem varsFit_leaves (f : LFace) (D : Data P KE) (z : Array E) (hw : D.N.w = f.mu)
    (hE : D.N.oE = orderDefault (f.mu + f.d)) (hz : z.size = f.mu + f.d) :
    VarsFit (leafVars f z) (leavesJob D (byBit z)) := by
  have e : leafVars f z = (List.range (f.mu + f.d)).map fun j =>
      Var.point (z.getD j zeroE) ((if j < f.d then 2 else 1) + 1) := by
    unfold leafVars
    refine List.map_congr_left fun j _ => ?_
    split <;> rfl
  rw [e]
  refine varsFit_map _ _ _ _ ?_ ?_
  · show TwV.inRounds D.N.oE (byBit z) = _
    rw [hE, ← hz, inRounds_down, ups_toList]
  · show TwV.dgE D.N = _
    unfold TwV.dgE
    rw [hE, ← countDown_eq, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < f.mu + f.d := List.mem_range.1 hj
    show (if FoNums.placeOf (f.mu + f.d) j < D.N.w then 1 else 2) = _
    unfold FoNums.placeOf
    rw [hw]
    split <;> split <;> omega

/-- **The bits' variables** are those of the bits' job at the translated point, where the job's
order counts down. -/
theorem varsFit_bits (D : Data P KE) (z : Array E) (hB : D.N.oB = orderDefault (D.N.w + D.N.d))
    (hz : z.size = D.N.w + D.N.d) : VarsFit (bitsCall z.toList).vs (bitsJob D (byBit z)) := by
  show VarsFit (z.toList.map fun x => Var.point x (2 + 1)) _
  refine varsFit_map z.toList (fun x => x) (fun _ => 2) _ ?_ ?_
  · show TwV.inRounds D.N.oB (byBit z) = _
    rw [hB, ← hz, inRounds_down]
    rfl
  · show List.replicate (D.N.w + D.N.d) 2 = _
    rw [List.map_const', Array.length_toList, hz]

/-! ## 4 The hypothesis of the statement on the masked sumcheck, at the five jobs -/

/-- **A step of the tie.** Conditional on the relation after the challenge (`Data.Mid`). -/
theorem tie_sums (D : Data P KE) (hM : D.Mid) {s : Nat} (hs : s ≤ D.N.n) (m : List E) (beta : E)
    (hm : m.length = ((tieJob D s).ends []).length) :
    SumsTo gl [.point zeroE 4] (polyOf (tieJob D s) m) [] [beta] (tieJob D s).sum
      ((tieJob D s).S0 (shownL (up beta) ((tieJob D s).ends []) (ups m))) :=
  sums_ends (tieJob D s) (OnBytes.HonestTrace.Look.tieJob_lawful D hM hs) (sized_tie D s) 3 rfl []
    ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩ m [] beta rfl hm

/-- **A level: the job of a product of two halves**, at the verifier's variables. Conditional on an
order that lists the level's variables and on sizes. -/
theorem level_sums (l : Nat) (A B : Nat → KE) (o : List Nat) (z : Array E) (hz : z.size = l)
    (ho : o.Perm (List.range l)) (m rs : List E) (beta : E) (hr : rs.length = l)
    (hm : m.length = 2) :
    SumsTo gl (levelVars l z o ++ [.point zeroE 3]) (polyOf (pj l 0 A B o (byBit z)) m) []
      (rs ++ [beta]) (pj l 0 A B o (byBit z)).sum
      ((pj l 0 A B o (byBit z)).S0
        (shownL (up beta) ((pj l 0 A B o (byBit z)).ends (ups rs)) (ups m))) :=
  sums_ends _ (OnBytes.HonestTrace.Look.pj_lawful l 0 A B o _ ho (by rw [byBit_length, hz]))
    (sized_pj l 0 A B o _ (by rw [ho.length_eq, List.length_range])) 2 rfl _
    (varsFit_level l 0 A B o z hz ho) m rs beta
    (by
      show rs.length = (TwV.inRounds o (byBit z)).length
      unfold TwV.inRounds
      rw [List.length_map, ho.length_eq, List.length_range, hr]) hm

/-- **The leaves.** Conditional on the job's numbers being the face's, its order counting down, and
on sizes. -/
theorem leaves_sums (f : LFace) (D : Data P KE) (z : Array E) (hw : D.N.w = f.mu) (hd : D.N.d = f.d)
    (hE : D.N.oE = orderDefault (f.mu + f.d)) (hz : z.size = f.mu + f.d) (m rs : List E)
    (hr : rs.length = f.mu + f.d) :
    SumsTo gl (leafVars f z) (polyOf (leavesJob D (byBit z)) m) [] rs (leavesJob D (byBit z)).sum
      ((leavesJob D (byBit z)).fin (ups rs)) :=
  sums_open _
    (OnBytes.HonestTrace.Look.leavesJob_lawful D _ (by rw [byBit_length, hz, hw, hd])
      (by rw [hE, hw, hd]; exact perm_orderDefault _))
    (sized_leaves D _) _ (varsFit_leaves f D z hw hE hz) m rs
    (by
      show rs.length = (TwV.inRounds D.N.oE (byBit z)).length
      unfold TwV.inRounds
      rw [List.length_map, hE, (perm_orderDefault _).length_eq, List.length_range, hr])

/-- **The bits.** Conditional on the job's order counting down and on sizes. -/
theorem bits_sums (D : Data P KE) (z : Array E) (hB : D.N.oB = orderDefault (D.N.w + D.N.d))
    (hz : z.size = D.N.w + D.N.d) (m rs : List E) (beta : E) (hr : rs.length = D.N.w + D.N.d)
    (hm : m.length = 1) :
    SumsTo gl ((bitsCall z.toList).vs ++ [.point zeroE 3]) (polyOf (bitsJob D (byBit z)) m) []
      (rs ++ [beta]) (bitsJob D (byBit z)).sum
      ((bitsJob D (byBit z)).S0
        (shownL (up beta) ((bitsJob D (byBit z)).ends (ups rs)) (ups m))) :=
  sums_ends _
    (OnBytes.HonestTrace.Look.bitsJob_lawful D _ (by rw [byBit_length, hz])
      (by rw [hB]; exact perm_orderDefault _))
    (sized_bits D _ (by rw [hB, (perm_orderDefault _).length_eq, List.length_range])) 2 rfl _
    (varsFit_bits D z hB hz) m rs beta
    (by
      show rs.length = (TwV.inRounds D.N.oB (byBit z)).length
      unfold TwV.inRounds
      rw [List.length_map, hB, (perm_orderDefault _).length_eq, List.length_range, hr]) hm

#print axioms ProofFile.Honest.K3.ups_toList
#print axioms ProofFile.Honest.K3.varsFit_leaves
#print axioms ProofFile.Honest.K3.varsFit_bits
#print axioms ProofFile.Honest.K3.tie_sums
#print axioms ProofFile.Honest.K3.level_sums
#print axioms ProofFile.Honest.K3.leaves_sums
#print axioms ProofFile.Honest.K3.bits_sums
#print axioms ProofFile.Honest.K3.perm_of_orderOk
#print axioms ProofFile.Honest.K3.perm_orderDefault
#print axioms ProofFile.Honest.K3.sized_tie
#print axioms ProofFile.Honest.K3.sized_pj
#print axioms ProofFile.Honest.K3.sized_leaves
#print axioms ProofFile.Honest.K3.sized_bits
#print axioms ProofFile.Honest.K3.varsFit_map
#print axioms ProofFile.Honest.K3.varsFit_level

end ProofFile.Honest.K3
