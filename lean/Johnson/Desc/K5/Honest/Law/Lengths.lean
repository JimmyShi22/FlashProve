-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Lengths.lean: the honest side of an attention segment's own rounds: HOW
MANY values each list of hidden values holds, and how many variables and end values each summand
has. Statements with their proofs, and one test with code.

  `aloneOk_spec`, `aloneOk_of`   what the test `aloneOk` (Johnson/Desc/K5/Honest/Alone.lean) says
  under the namespace `Lengths`:
  `aloneKR_length`, `aloneK_length`, `leadK_length`, `leadSE_length`, `m6_length`   the lists of
      values that are sent by themselves
  `sK_vars` .. `sHB_ends`   the two numbers of the seven texts of summands (Products.lean,
      Index.lean; the first serves every softmax-table unit)
  `Pub5.counted`   A TEST WITH CODE ON PUBLIC NUMBERS: the planner's numbers of these rounds are
      those of the shape from which the claims' numbers are made: there is a softmax-table unit;
      pairs, bits of a token's number, bits of a head's number, layers; the variables of two
      sumchecks; each softmax-table unit's number of pieces
  `counted_spec`   what it says

The lengths of the first four lists are CONDITIONAL on `aloneOk`: where the verifier's function for
the named points refuses, these lists are empty, but for `leadK`, which then holds the total alone.

Limits. Counts alone: nothing is said of a value. Nothing here shows that `counted` holds at the
planner's own numbers. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Alone
import Johnson.Desc.K5.Honest.Products
import Johnson.Desc.K5.Honest.Index

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E)
open VerifiableInference.Desc.First.Att.P (Pts)

/-! ## 1 The test on the points -/

/-- What the test says. -/
theorem aloneOk_spec {P : Pub5} {c : Chal} (h : aloneOk P c = true) :
    ∃ p, ptsOf P c = some p ∧ P.x.planeMessages ≤ p.planes.size ∧
      p.scores.size = P.x.score.length ∧ ∀ k ∈ p.scores, k.claim < p.planes.size := by
  unfold aloneOk at h
  cases hp : ptsOf P c with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem] at h
    exact ⟨p, rfl, h.1.1, h.1.2, h.2⟩

/-- And back. -/
theorem aloneOk_of {P : Pub5} {c : Chal} {p : Pts} (hp : ptsOf P c = some p)
    (h1 : P.x.planeMessages ≤ p.planes.size) (h2 : p.scores.size = P.x.score.length)
    (h3 : ∀ k ∈ p.scores, k.claim < p.planes.size) : aloneOk P c = true := by
  unfold aloneOk
  rw [hp]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true_iff_forall_mem]
  exact ⟨⟨h1, h2⟩, h3⟩

namespace Lengths

/-! ## 2 The lists of values that are sent by themselves -/

private theorem flatMap_three {α : Type} (f : α → Nat → E) : ∀ l : List α,
    (l.flatMap fun u => (List.range 3).map (f u)).length = l.length * 3
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, flatMap_three f l, List.length_map,
      List.length_range, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Three values for each remainder-table unit. Conditional: `aloneOk`. -/
theorem aloneKR_length {P : Pub5} {c : Chal} (h : aloneOk P c = true) (w : K5In) :
    (aloneKR P w c).length = P.x.planeMessages * 3 := by
  obtain ⟨p, hp, h1, -, -⟩ := aloneOk_spec h
  unfold aloneKR
  rw [hp]
  show ((p.planes.toList.take P.x.planeMessages).flatMap fun u =>
    (List.range 3).map (planeOf P.g w u)).length = _
  rw [flatMap_three (fun u => planeOf P.g w u), List.length_take, Array.length_toList,
    Nat.min_eq_left h1]

/-- Six values for a softmax-table unit. Conditional: `aloneOk`; there is such a unit. -/
theorem aloneK_length {P : Pub5} {c : Chal} (h : aloneOk P c = true) (w : K5In) {i : Nat}
    (hi : i < P.x.score.length) : (aloneK P w c i).length = 6 := by
  obtain ⟨p, hp, -, h2, h3⟩ := aloneOk_spec h
  have hi' : i < p.scores.size := by
    rw [h2]
    exact hi
  have e1 : p.scores[i]? = some p.scores[i] := Array.getElem?_eq_getElem hi'
  have hc : p.scores[i].claim < p.planes.size := h3 _ (Array.getElem_mem hi')
  have e2 : p.planes[p.scores[i].claim]? = some p.planes[p.scores[i].claim] :=
    Array.getElem?_eq_getElem hc
  simp [aloneK, kAt, hp, e1, e2]

/-- Seven scalars in front of a softmax-table unit's sumcheck. Conditional: as `aloneK_length`. -/
theorem leadK_length {P : Pub5} {c : Chal} (h : aloneOk P c = true) (w : K5In) {i : Nat}
    (hi : i < P.x.score.length) (sv : E) : (leadK P w c i sv).length = 7 := by
  unfold leadK
  rw [List.length_append, aloneK_length h w hi]
  rfl

/-- The scalars in front of the division's sumcheck. Conditional: `aloneOk`. -/
theorem leadSE_length {P : Pub5} {c : Chal} (h : aloneOk P c = true) (w : K5In) (zo : E) :
    (leadSE P w c zo).length = 5 + P.g.lt + 2 := by
  obtain ⟨p, hp, -, -, -⟩ := aloneOk_spec h
  simp [leadSE, hp, ibAt]
  omega

/-- One maximum for each pair. No premise. -/
theorem m6_length (P : Pub5) (w : K5In) (c : Chal) : (m6 P w c).length = P.g.NP := by
  simp [m6]

/-! ## 3 The summands' two numbers -/

theorem sK_vars (P : Pub5) (w : K5In) (c : Chal) (i : Nat) :
    (sK P w c i).vars = (cut P.x).getD i 3 - 3 := by
  rcases h1 : P.g.scores[i]? with _ | u <;>
    rcases h2 : (ptsOf P c).bind (·.scores[i]?) with _ | k <;>
    simp [sK, h1, h2, noProducts, ofProducts]
theorem sK_ends (P : Pub5) (w : K5In) (c : Chal) (i : Nat) :
    (sK P w c i).ends = 2 * ((P.g.scores[i]?).map (·.pcs.length)).getD 0 := by
  rcases h1 : P.g.scores[i]? with _ | u <;>
    rcases h2 : (ptsOf P c).bind (·.scores[i]?) with _ | k <;>
    simp [sK, h1, h2, noProducts, ofProducts]
theorem sSE_vars (P : Pub5) (w : K5In) (c : Chal) :
    (sSE P w c).vars = (cut P.x).getD (iSE P.x) 3 - 3 := by
  unfold sSE
  split <;> rfl
theorem sSE_ends (P : Pub5) (w : K5In) (c : Chal) : (sSE P w c).ends = 2 * P.g.NP := by
  unfold sSE
  split <;> rfl
theorem sVM_vars (P : Pub5) (w : K5In) (c : Chal) :
    (sVM P w c).vars = (cut P.x).getD (iVM P.x) 3 - 3 := by
  unfold sVM
  split <;> rfl
theorem sVM_ends (P : Pub5) (w : K5In) (c : Chal) : (sVM P w c).ends = 2 * P.g.NP := by
  unfold sVM
  split <;> rfl
theorem sVD_vars (P : Pub5) (w : K5In) (c : Chal) :
    (sVD P w c).vars = (cut P.x).getD (iVD P.x) 3 - 3 := by
  unfold sVD
  split <;> rfl
theorem sVD_ends (P : Pub5) (w : K5In) (c : Chal) : (sVD P w c).ends = 2 * P.g.NP := by
  unfold sVD
  split <;> rfl
theorem sSF_vars (P : Pub5) (w : K5In) (c : Chal) :
    (sSF P w c).vars = P.g.lt + P.g.lgk + P.g.ldh := rfl
theorem sSF_ends (P : Pub5) (w : K5In) (c : Chal) : (sSF P w c).ends = 2 * P.g.NP := rfl
theorem sSD_vars (P : Pub5) (w : K5In) (c : Chal) : (sSD P w c).vars = 2 * P.g.lt + P.g.lgk := rfl
theorem sSD_ends (P : Pub5) (w : K5In) (c : Chal) :
    (sSD P w c).ends = P.g.Lam + P.g.NP * P.g.lt := rfl
theorem sHB_vars (P : Pub5) (w : K5In) (c : Chal) : (sHB P w c).vars = P.g.lt + P.g.lgk + 4 := rfl
theorem sHB_ends (P : Pub5) (w : K5In) (c : Chal) : (sHB P w c).ends = 2 * P.g.NP := rfl

end Lengths

/-! ## 4 The planner's numbers against the shape's -/

/-- **A test with code on public numbers alone**: the planner's numbers of these rounds are those
of the shape from which the claims' numbers are made. -/
def Pub5.counted (P : Pub5) : Bool :=
  !P.x.score.isEmpty && P.x.pairs == P.g.NP && P.x.lt == P.g.lt && P.x.lgk == P.g.lgk &&
    P.x.Lam == P.g.Lam && P.x.attained == P.g.lt + P.g.lgk + P.g.ldh &&
    P.x.bits == P.g.lt + P.g.lgk + 4 &&
    (List.range P.x.score.length).all fun i =>
      ((P.g.scores[i]?).map (·.pcs.length)).getD 0 == ((P.x.score[i]?).map (·.2)).getD 0

/-- What it says. -/
theorem counted_spec {P : Pub5} (h : P.counted = true) :
    P.x.score.isEmpty = false ∧ P.x.pairs = P.g.NP ∧ P.x.lt = P.g.lt ∧ P.x.lgk = P.g.lgk ∧
      P.x.Lam = P.g.Lam ∧ P.x.attained = P.g.lt + P.g.lgk + P.g.ldh ∧
      P.x.bits = P.g.lt + P.g.lgk + 4 ∧
      ∀ (i : Nat) (u : Nat × Nat), P.x.score[i]? = some u →
        ((P.g.scores[i]?).map fun v => v.pcs.length).getD 0 = u.2 := by
  unfold Pub5.counted at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun i u hu => ?_⟩
  rw [h8 i (List.getElem?_eq_some_iff.1 hu).1, hu]
  rfl

end H2K5.Honest

#print axioms H2K5.Honest.aloneOk_spec
#print axioms H2K5.Honest.aloneOk_of
#print axioms H2K5.Honest.Lengths.aloneKR_length
#print axioms H2K5.Honest.Lengths.aloneK_length
#print axioms H2K5.Honest.Lengths.leadK_length
#print axioms H2K5.Honest.Lengths.leadSE_length
#print axioms H2K5.Honest.Lengths.m6_length
#print axioms H2K5.Honest.Lengths.sK_vars
#print axioms H2K5.Honest.Lengths.sK_ends
#print axioms H2K5.Honest.Lengths.sSE_vars
#print axioms H2K5.Honest.Lengths.sSE_ends
#print axioms H2K5.Honest.Lengths.sVM_vars
#print axioms H2K5.Honest.Lengths.sVM_ends
#print axioms H2K5.Honest.Lengths.sVD_vars
#print axioms H2K5.Honest.Lengths.sVD_ends
#print axioms H2K5.Honest.Lengths.sSF_vars
#print axioms H2K5.Honest.Lengths.sSF_ends
#print axioms H2K5.Honest.Lengths.sSD_vars
#print axioms H2K5.Honest.Lengths.sSD_ends
#print axioms H2K5.Honest.Lengths.sHB_vars
#print axioms H2K5.Honest.Lengths.sHB_ends
#print axioms H2K5.Honest.counted_spec
