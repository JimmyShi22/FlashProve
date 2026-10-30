-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LedgersAtAll.lean: TWO TESTS WITH CODE THAT ARE OWED BENEATH THE NAMED CONDITION
OF THE SUB-PROTOCOL K1 ACCEPT AT ALL PUBLIC FILES IN THE GOALS' SCOPE: theorems: `readsWideB`
(Johnson/Desc/K1/Law/HeadNumbersAtAll.lean) and `hKlB` (Johnson/Desc/K1/Law/ArmLettersB.lean): both
read, of the planner's list of segments, the planned ledgers alone. Statements with their proofs;
one small closed fact by Lean's kernel, with its negative test.

  `built_back`   the planner's entry is the blank letters' but for its routine (`blank_built`,
      Johnson/IMR/OwnSeat.lean): so it has that entry's planned ledger
  `looks_K`   the look of an array of a planned ledger bears the array's number of columns
  `ledgers_in_scope`   the planner's entry of attention segment 2 g + 1 has the g-th attention
      plan's ledger; that of segment 24 the head's plan's (`ground_tails`,
      Johnson/IMR/K8Seat.lean)
  `readsWide_in_scope`   **readsWideB accepts**: the head's plan's ledger has an array number 0 with
      just as many columns as the plan asks (`public_array`,
      Johnson/Desc/Kinds/Law/ReadsArray.lean); the array of the reads is number 0 (`public_third`)
  `attOdd`, `attOdd_fails`   BY LEAN's KERNEL: the attention segments are the odd numbers below 24
  `hKl_in_scope`   **hKlB accepts** (at 0 columns more): the array that the test finds in the
      planner's ledger is the one that `plannedK` reads; it is there (`ofPlan_u3_tree`,
      Johnson/Desc/First/Att/Claims/OfPlan.lean, under `planIs_public`)
  `hWide_atAll`, `hKlB_atAll`   the two at the closed constant, each in the owed field's
      own type, under the head and an opening of the maker

What is not claimed. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HeadNumbersAtAll
import Johnson.Desc.K1.Law.ArmLettersB
import Johnson.Desc.Kinds.Law.ReadsArray
import Johnson.IMR.K8Seat
import Johnson.IMR.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.FillSent (treesAt looksOf)
open VerifiableInference.Desc.First.Att.P (plannedK planIs_public)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)
open IM (Open)

/-- The planner's entry has the blank letters' entry's planned ledger. -/
theorem built_back {Z : ProofFile.Pub} {G : ProofFile.Ground} {links : Array Stages.LinkH}
    (e : G.built = Z.p.built.links.zipWith (fun b l => { b with run := l.run }) links) {k : ℕ}
    {l : Stages.LinkH} (h : G.built[k]? = some l) :
    ∃ b, Z.p.built.links[k]? = some b ∧ b.Fp = l.Fp := by
  rw [e] at h
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 h
  have hl1 : k < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  exact ⟨_, Array.getElem?_eq_getElem hl1, congrArg (·.Fp) e'⟩

/-- The look of an array of a planned ledger bears the array's number of columns. -/
theorem looks_K {built : Array Stages.LinkH} {m i : ℕ} {b : Stages.LinkH} {T : HTree}
    (hb : built[m]? = some b) (hT : b.Fp.trees[i]? = some T) :
    ∃ t, (treesAt built m)[i]? = some t ∧ t.2.1 = T.K := by
  unfold treesAt
  rw [hb]
  show ∃ t, (looksOf b.Fp)[i]? = some t ∧ t.2.1 = T.K
  unfold looksOf
  rw [List.getElem?_map, Array.getElem?_toList, hT]
  exact ⟨_, rfl, rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The planner's ledgers at the attention segments and at the head's. -/
theorem ledgers_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) :
    (∀ g < 12, ∃ a b, Z.p.X.A[g]? = some a ∧ Z.p.built.links[2 * g + 1]? = some b ∧
      b.Fp = a.seam.Fp) ∧ ∃ b, Z.p.built.links[24]? = some b ∧ b.Fp = Z.p.X.H.Fp := by
  obtain ⟨tails, l24, h24, -, hF24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built O.blank
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨_, a, _, l', _, hA, _, _, _, _, _, _, hb, _, hFp, _⟩ := tails g hg
    obtain ⟨b, hb', hF⟩ := built_back e hb
    rw [O.W] at hA
    exact ⟨a, b, hA, hb', hF.trans hFp⟩
  · obtain ⟨b, hb', hF⟩ := built_back e h24
    rw [O.W] at hF24
    exact ⟨b, hb', hF.trans hF24⟩

/-- **readsWideB accepts.** -/
theorem readsWide_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) :
    readsWideB Z.p.built.links Z.p.X = true := by
  obtain ⟨-, b, hb, hF⟩ := ledgers_in_scope hS hR O
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := O.W ▸ O.public
  obtain ⟨h0, hK, -⟩ := Kinds.Head.Law.ReadsArray.public_array hX
  have hr : readsOf Z.p.X = 0 := by
    have h : Z.p.X.H.tl.ix.U.getD 2 none = some 0 := Kinds.Head.Law.ReadsNamed.public_third hX
    unfold readsOf
    rw [h]
    rfl
  have hT : b.Fp.trees[0]? = some (Z.p.X.H.Fp.trees.getD 0 {}) := by
    rw [hF, Array.getElem?_eq_getElem h0]
    simp [Array.getD, h0]
  obtain ⟨t, ht, hk⟩ := looks_K hb hT
  unfold readsWideB
  rw [hr, ht, Option.any_some, hk, hK]
  exact decide_eq_true (Nat.le_refl _)

set_option maxRecDepth 100000 in
theorem attOdd : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == ModelPart.attention) || (l % 2 == 1 && decide (l < 24))) =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The negative test: they are not the even numbers. -/
theorem attOdd_fails : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == ModelPart.attention) || (l % 2 == 0 && decide (l < 24))) =
      false := by
  decide +kernel

/-- **hKlB accepts.** -/
theorem hKl_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) :
    hKlB Z.p.X (treesAt Z.p.built.links) 0 = true := by
  obtain ⟨hatt, -⟩ := ledgers_in_scope hS hR O
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := O.W ▸ O.public
  unfold hKlB
  rw [List.all_eq_true]
  intro l hl
  have h1 := List.all_eq_true.1 attOdd l hl
  cases hs : ((linksFull[l]?).getD .layers == ModelPart.attention) with
  | false => rfl
  | true =>
    rw [hs, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
    have ho : l % 2 = 1 := eq_of_beq h1.1
    have hlt : l < 24 := of_decide_eq_true h1.2
    obtain ⟨a, b, hA, hb, hF⟩ := hatt (l / 2) (by omega)
    have el : 2 * (l / 2) + 1 = l := by omega
    rw [el] at hb
    obtain ⟨A0, pf, h0, e⟩ := planIs_public hX (l / 2) a hA
    obtain ⟨_, T, hT, _, _, _⟩ := _root_.K5Law.ofPlan_u3_tree ⟨_, _, _, A0, pf, h0, e⟩
    obtain ⟨t, ht, htk⟩ := looks_K hb (by rw [hF]; exact hT)
    have hk : plannedK a = T.K := by
      unfold plannedK
      rw [hT]
      rfl
    rw [Bool.not_true, Bool.false_or, hA]
    show (match (treesAt Z.p.built.links l)[a.iU3]? with
      | none => false
      | some t => t.2.1 == plannedK a + 0) = true
    rw [ht, hk]
    show (t.2.1 == T.K + 0) = true
    rw [htk]
    simp

end

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
include hA O

/-- **hWide.** -/
theorem hWide_atAll : readsWideB Zp.made.p.built.links Zp.p.X = true :=
  readsWide_in_scope hA.scope hA.reads O

/-- **hKlB.** -/
theorem hKlB_atAll : hKlB (P5J.At.X Zp) hA.𝔇.pubD.dS.trees 0 = true :=
  hKl_in_scope hA.scope hA.reads O

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.built_back
#print axioms VerifiableInference.Desc.K1.looks_K
#print axioms VerifiableInference.Desc.K1.ledgers_in_scope
#print axioms VerifiableInference.Desc.K1.readsWide_in_scope
#print axioms VerifiableInference.Desc.K1.attOdd
#print axioms VerifiableInference.Desc.K1.attOdd_fails
#print axioms VerifiableInference.Desc.K1.hKl_in_scope
#print axioms VerifiableInference.Desc.K1.hWide_atAll
#print axioms VerifiableInference.Desc.K1.hKlB_atAll
