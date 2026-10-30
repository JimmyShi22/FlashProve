-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/PlanNumbers.lean: code switching (K2): THE NUMBERS IN TWO OF THE THREE NAMED
TESTS ON THE PLANNER's OUTPUT (linkPlanB · headPlanB: Johnson/P1K2R/PlanBools.lean), IN SCOPE, WITH
NO VALUE AND NO DECISION OF LEAN's KERNEL: each conjunct is a law of a text, or a conjunct of the
description's own test on the plan at the lookup's sub-protocol of the same link.
  x_scope      in scope the public record has profile 4 and twelve groups (Meaning.scope_plans)
  look_room    THE LOOKUP ON THE CALLS HAS ROOM, at every link l < 25: placeAt Z.p.X l false is
               there, it makes a shape h, and p.first + Forest.elems h ≤ p.ns: by k3_of
               (Johnson/IMR/K3Seat.lean: the chain's sub-protocol there is the kind's own, alone) ·
               the description's test on the plan, carried down (flat_planOk · alone_planOk) · the
               kind's stated_planOk (Johnson/Desc/First/Look/K3PlanOfOk.lean)
  placeAt_lay · placeAt_att · placeAt_head   lookAt's text: the lookup's first slot and number of
               slots are the link's plan's
  sort_low · sort_at24   the piece 2 (the head's link: 3) is the lookup on the calls. KIN of the
               second: OnPublicFiles.sort_head (Johnson/Desc/First/Look/K3HeadFill.lean): a call
               wants an instance of its section's: three lines are typed instead
  madeLook_of  madeLookB at the closed constant's letters (P5J.At), out of these
  headPlanB_of_built   headPlanB ACCEPTS, given the built link at 24 and «its ns is the head's
               plan's»
  linkPlanB_of_built   linkPlanB ACCEPTS at l, 1 ≤ l < 24, given the built link at l with its kind,
               group, ns and Fp, and «nothing is heard» at the link's plan
LEFT, BY NAME: the built link's own facts (kind · g · ns · Fp: laws of the planner's text) ·
«nothing is heard». k5PlanB IS NOT HERE.
LIMITS. Joins and laws of texts. The premises hS · hR · O · hpl are not shown met: no example. No
soundness is claimed.
-/
import Johnson.P1K2R.PlanBools
import Johnson.IMR.K3Seat
import Johnson.IMR.PlacesScope
import Johnson.Desc.First.Look.K3PlanOfOk
import Johnson.Goal.Meaning.PlanShapes
import Johnson.P1K2R.SitsLaw
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt K3Data k3SortAt)
open VerifiableInference.Desc.First.K2 (madeLookB)
open Johnson.Desc.First.Walk.Seat (pubOf)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the public record's profile and number of groups. -/
theorem x_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    Z.p.X.p4 = true ∧ Z.p.X.NGr = 12 := by
  have h := Meaning.scope_plans hS hR (O.W ▸ O.public)
  exact ⟨h.1, h.2.1⟩

/-- **THE LOOKUP ON THE CALLS HAS ROOM**: a conjunct of the description's own test on the plan, at
the lookup's sub-protocol of link l. -/
theorem look_room (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) {l : ℕ}
    (hl : l < 25) :
    ∃ p h, placeAt Z.p.X l false = some p ∧ p.shape = some h ∧
      p.first + Forest.elems h ≤ p.ns := by
  obtain ⟨h4, h12⟩ := x_scope hS hR O
  obtain ⟨Lk, b, b', e1, e2, e3, hla⟩ := IM.k3_of hS hR O l hl false
  have hf := IM.hear_at_flat e1 e2
  have hb := flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hb' : b'.planOk = true := by rw [← IM.alone_planOk hla]; exact hb
  rw [ProofFile.Law.blankBy_W O.blank] at e3
  obtain ⟨i, d, p, laid, hi, hpc, hp, hok⟩ :=
    VerifiableInference.Desc.K3.stated_planOk _ _ _ _ _ _ b' e3 hb'
  obtain rfl : l = i := Option.some.inj hi
  have hd : d = false := by
    cases d with
    | false => rfl
    | true =>
      exfalso
      have hp1 : (IM.k3Place l false).piece = if l = 24 then 3 else 2 := by
        by_cases e : l = 24 <;> simp [IM.k3Ix, e]
      have hp2 : VerifiableInference.Desc.K3.pieceAt Z.p.X l true = if l = 24 then 8 else 7 := by
        unfold VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
        rw [h4, h12]
        by_cases e : l = 24 <;> simp [e]
      rw [hp1, hp2] at hpc
      by_cases e : l = 24 <;> simp [e] at hpc
  subst hd
  unfold VerifiableInference.Desc.First.Look.P.planOk at hok
  cases hs : p.shape with
  | none => rw [hs] at hok; cases hok
  | some h =>
    rw [hs] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨p, h, hp, hs, hok.1.1.2⟩

/-! ## lookAt's text, at the lookup on the calls -/

theorem placeAt_lay {X : Verify.Public} (h4 : X.p4 = true) (h12 : X.NGr = 12) {l : ℕ}
    (hl : l < 24) (he : l % 2 = 0) {hp : Layer.HPlan2} (hG : X.G[l / 2]? = some hp) :
    ∃ p, placeAt X l false = some p ∧ p.first = hp.Fp.next ∧ p.ns = hp.ns := by
  have e1 : (l == 2 * 12) = false := by simpa using (by omega : l ≠ 24)
  have e2 : (l % 2 == 0) = true := by simpa using he
  unfold VerifiableInference.Desc.First.Look.placeAt VerifiableInference.Desc.First.Look.lookAt
  simp only [h4, h12, if_true, e1, e2, hG, Option.bind_some, Bool.false_eq_true, if_false,
    Option.map_some]
  exact ⟨_, rfl, rfl, rfl⟩

theorem placeAt_att {X : Verify.Public} (h4 : X.p4 = true) (h12 : X.NGr = 12) {l : ℕ}
    (he : l % 2 = 1) {a : Attention.Plan} (hA : X.A[l / 2]? = some a) :
    ∃ p, placeAt X l false = some p ∧ p.first = a.seam.Fp.next ∧ p.ns = a.ns := by
  have e1 : (l == 2 * 12) = false := by simpa using (by omega : l ≠ 24)
  have e2 : (l % 2 == 0) = false := by simpa using (by omega : l % 2 ≠ 0)
  unfold VerifiableInference.Desc.First.Look.placeAt VerifiableInference.Desc.First.Look.lookAt
  simp only [h4, h12, if_true, e1, e2, hA, Option.bind_some, Bool.false_eq_true, if_false,
    Option.map_some]
  exact ⟨_, rfl, rfl, rfl⟩

theorem placeAt_head {X : Verify.Public} (h4 : X.p4 = true) (h12 : X.NGr = 12) :
    ∃ p, placeAt X 24 false = some p ∧ p.first = 0 ∧ p.ns = X.H.ns := by
  unfold VerifiableInference.Desc.First.Look.placeAt VerifiableInference.Desc.First.Look.lookAt
  simp only [h4, h12, if_true, Bool.false_eq_true, if_false]
  exact ⟨_, rfl, rfl, rfl⟩

theorem sort_low {X : Verify.Public} (h4 : X.p4 = true) (h12 : X.NGr = 12) {l : ℕ} (hl : l < 24) :
    VerifiableInference.Desc.First.Look.k3SortAt X l 2 = some false := by
  have e1 : (l == 2 * 12) = false := by simpa using (by omega : l ≠ 24)
  unfold VerifiableInference.Desc.First.Look.k3SortAt VerifiableInference.Desc.K3.pieceAt
    VerifiableInference.Desc.K3.isHead
  simp [h4, h12, e1]

/-- Kin: VerifiableInference.OnPublicFiles.sort_head (Johnson/Desc/First/Look/K3HeadFill.lean), at the
head's link as a term of X; it stands under its section's letters, among them an instance. -/
theorem sort_at24 {X : Verify.Public} (h4 : X.p4 = true) (h12 : X.NGr = 12) :
    VerifiableInference.Desc.First.Look.k3SortAt X 24 3 = some false := by
  unfold VerifiableInference.Desc.First.Look.k3SortAt VerifiableInference.Desc.K3.pieceAt
    VerifiableInference.Desc.K3.isHead
  simp [h4, h12]

/-! ## madeLookB at the constant's data -/

theorem madeLook_of {l pc next ns : ℕ} {X : Stages.LinkH} (hX : Z.p.built.links[l]? = some X)
    (hs : k3SortAt Z.p.X l pc = some false) {p : VerifiableInference.Desc.First.Look.P}
    {h : Forest.Shape} (hp : placeAt Z.p.X l false = some p) (hsh : p.shape = some h)
    (hf : p.first = next) (hn : p.ns = ns) (hroom : p.first + Forest.elems h ≤ p.ns) :
    madeLookB (K3Data.of (P5J.At.X Z) (P5J.At.sentAt Z)) l pc X.arrayOf next ns = true := by
  have ea : ((K3Data.of (P5J.At.X Z) (P5J.At.sentAt Z))).arrayOf.getD l #[] = X.arrayOf := by
    show (Z.p.built.links.map (·.arrayOf)).getD l #[] = X.arrayOf
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hX]
    rfl
  unfold madeLookB
  rw [ea]
  show (k3SortAt Z.p.X l pc == some false && X.arrayOf == X.arrayOf &&
    (placeAt Z.p.X l false).any fun p => p.first == next && p.shape.any fun h =>
      decide (p.first + Forest.elems h ≤ ns)) = true
  rw [hs, hp, Option.any_some, hsh, Option.any_some, hf, ← hn]
  rw [hf] at hroom
  simp [hroom]

/-! ## The two tests -/

/-- **headPlanB ACCEPTS**, given the built link at 24. -/
theorem headPlanB_of_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    {b : Stages.LinkH} (hb : Z.p.built.links[24]? = some b) (hns : b.ns = Z.p.X.H.ns) :
    headPlanB Z (P5J.At.nsOf Z) (K3Data.of (P5J.At.X Z) (P5J.At.sentAt Z)) = true := by
  obtain ⟨h4, h12⟩ := x_scope hS hR O
  obtain ⟨p, h, hp, hsh, hroom⟩ := look_room hS hR O hpl (l := 24) (by omega)
  obtain ⟨p', hp', hf, hn⟩ := placeAt_head h4 h12
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  have e : P5J.At.nsOf Z 24 = some Z.p.X.H.ns := by
    show (Z.p.built.links[24]?).map (·.ns) = _
    rw [hb, Option.map_some, hns]
  unfold headPlanB
  rw [hb]
  show (decide (P5J.At.nsOf Z 24 = some Z.p.X.H.ns) &&
    madeLookB (K3Data.of (P5J.At.X Z) (P5J.At.sentAt Z)) 24 3 b.arrayOf 0 Z.p.X.H.ns) = true
  rw [madeLook_of hb (sort_at24 h4 h12) hp hsh hf hn hroom, decide_eq_true e]
  rfl

/-- **linkPlanB ACCEPTS**, given the built link at l and «nothing is heard». -/
theorem linkPlanB_of_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    {l : ℕ} (hl : l < 24) {X : Stages.LinkH} (hX : Z.p.built.links[l]? = some X)
    (hg : X.g = l / 2)
    (arms : (l % 2 = 1 ∧ X.kind = 1 ∧ ∃ a, Z.p.X.A[l / 2]? = some a ∧ X.ns = a.ns ∧
        X.Fp = a.seam.Fp ∧ a.seam.tl.heard = none) ∨
      (l % 2 = 0 ∧ X.kind = 0 ∧ ∃ hp, Z.p.X.G[l / 2]? = some hp ∧ X.ns = hp.ns ∧ X.Fp = hp.Fp ∧
        hp.tl.heard = none)) :
    linkPlanB Z (P5J.At.nsOf Z) (K3Data.of (P5J.At.X Z) (P5J.At.sentAt Z)) l = true := by
  obtain ⟨h4, h12⟩ := x_scope hS hR O
  obtain ⟨p, h, hp, hsh, hroom⟩ := look_room hS hR O hpl (l := l) (by omega)
  have hsub : (ProofFile.subsOf Z)[l]? = some (IM.subW l) := IM.subs_scope hS hR O l (by omega)
  have ens : P5J.At.nsOf Z l = some X.ns := by
    show (Z.p.built.links[l]?).map (·.ns) = _
    rw [hX, Option.map_some]
  unfold linkPlanB
  rw [decide_eq_true hsub, Bool.true_and, hX]
  rcases arms with ⟨he, hk, a, hA, n1, f1, u1⟩ | ⟨he, hk, q, hG, n1, f1, u1⟩
  · obtain ⟨p', hp', hf, hn⟩ := placeAt_att h4 h12 he hA
    obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
    have m := madeLook_of hX (sort_low h4 h12 hl) hp hsh
      (hf.trans (by show _ = X.Fp.next; rw [f1])) hn hroom
      (next := (pubOf X).Fp.next)
    simp only [hk, if_true, hg, hA]
    rw [ens, n1, u1]
    simp only [decide_true, Bool.true_and, Option.isNone_none, Bool.and_true]
    exact m
  · obtain ⟨p', hp', hf, hn⟩ := placeAt_lay h4 h12 hl he hG
    obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
    have m := madeLook_of hX (sort_low h4 h12 hl) hp hsh
      (hf.trans (by show _ = X.Fp.next; rw [f1])) hn hroom
      (next := (pubOf X).Fp.next)
    simp only [hk, hg, hG]
    rw [ens, n1, u1]
    simp only [decide_true, Bool.true_and, Option.isNone_none, Bool.and_true]
    exact m

end P1K2

#print axioms P1K2.x_scope
#print axioms P1K2.look_room
#print axioms P1K2.placeAt_lay
#print axioms P1K2.placeAt_att
#print axioms P1K2.placeAt_head
#print axioms P1K2.sort_low
#print axioms P1K2.sort_at24
#print axioms P1K2.madeLook_of
#print axioms P1K2.headPlanB_of_built
#print axioms P1K2.linkPlanB_of_built
