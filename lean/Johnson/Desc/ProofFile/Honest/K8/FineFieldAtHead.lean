-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FineFieldAtHead.lean: THE SMALLNESS TEST, AT THE FIRST CHAIN's
THREAD AT THE HEAD: THE FIELDS fine AND some OF THE RECORD `K8ItemsAt`
(Johnson/Desc/ProofFile/Honest/K8/SeatedItemsAt.lean) ARE MET AT ALL 25 DRAWS: fine WHEREVER THE
KIND's MEMBER IS SEATED, some AT THE DESCRIPTION's OWN PARAMETERS. Four theorems and two unnamed
checks; no definition; none of the library's goals.

  `extra_behind_keeps`   `K8Keeps` s s' carries the library's `Extra` from s to s'
  `cols_behind_keeps`    `K8Keeps` s s' · the record of s has the seven fields of tlP · the public
                   test `DgP.colsTest` says yes at tlP ⊢ it says yes at the record of s'
  **`fine_field_at_head`**   under the library's head (h : `P5J.AtMgA`): l < 25 · `K8Seated` at the
                   border 14 * l + (if l = 24 then 5 else 4) + 2 ⊢ the field's sentence, to the
                   letter: from a stand of the thread and a step of the member: Extra s' and
                   colsTest at the record of s'
  `some_field_at_head`   l < 25 · the blank ground G · the built segment Xl ⊢ the parameters
                   ProofFile.k8Par Zp G Xl l name a matrix (`ks_ne_at_built`,
                   Johnson/Desc/K8/Honest/SomeAtBuilt.lean)
  two `example`s    checks by Lean that the two theorems' ends are the record's fields; they state
                   nothing
HOW. CALLS OF THE LIBRARY's LAWS AT THE FOLD THAT THE STAND HOLDS (the clause `Made`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean): `front_at_place`, `own_at_place`
(Johnson/P1K8R/FrontAtSeat.lean) · `planFitsAll_of_test` (Johnson/P1K8R/PlanFitsTest.lean) at the
head's `k8_planFits` (Johnson/Goal/Skeleton/Kinds/K8Rest.lean) · `cond_of_front`
(Johnson/Desc/First/K8/LawFront.lean) · `lay7_of_test` (Johnson/Desc/First/K8/LawCondAtt.lean) ·
`colsTest_of_seven` (Johnson/Desc/First/K8/LawItemsAt.lean) · `public_cols`
(Johnson/Desc/First/Look/ColsAt.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
NO TACTIC THAT SEARCHES.
Limits. TWO FIELDS OF SIX; public data alone. `K8Seated` is a premise; the form behind the step and
what is said are not spent. THAT THE THREAD STANDS AT ANY OF THESE BORDERS, AT ANY PROVER, IS NOT
SAID HERE: where it stands at none, all is idle. THE FULL SIZE ALONE.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedItemsAt
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.P1K8R.PlanFitsTest
import Johnson.Goal.Skeleton.Kinds.K8Rest
import Johnson.Desc.First.K8.LawFront
import Johnson.Desc.First.K8.LawItemsAt
import Johnson.Desc.First.Look.ColsAt
import Johnson.Desc.K8.Honest.SomeAtBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (Par Extra colsTest_of_seven)
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7_of_test cond_of_front planFitsAllB)
open VerifiableInference.Desc.First.K8.Honest
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- The draw's member leaves the two further conditions. -/
theorem extra_behind_keeps {s s' : S} (hk : K8Keeps s s') (h : Extra s) : Extra s' := by
  obtain ⟨tl, cf, first, h1, h2⟩ := hk.tl
  obtain ⟨hF, h3⟩ := h tl h1
  intro tl' e
  obtain rfl := Option.some.inj (h2.symm.trans e)
  exact ⟨hF.of_same rfl rfl rfl, h3⟩

/-- The draw's member leaves the test on the digits' columns. -/
theorem cols_behind_keeps {s s' : S} (hk : K8Keeps s s') {tlP tl' : HTailF2}
    (h7 : lay7 s = some (seven tlP)) (hc : DgP.colsTest tlP = true) (ht : s'.tl? = some tl') :
    DgP.colsTest tl' = true := by
  obtain ⟨tl, cf, first, h1, h2⟩ := hk.tl
  obtain rfl := Option.some.inj (h2.symm.trans ht)
  unfold lay7 at h7
  rw [h1] at h7
  have e : seven tl = seven tlP := Option.some.inj h7
  exact (colsTest_of_seven (tl := { tl with cfF := cf, cfFirst := first }) (tlP := tlP) e).trans hc

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FIELD fine, AT ALL 25 DRAWS.** Public data alone. -/
theorem fine_field_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {P : Par × List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P) :
    ∀ k s m E ds y cols s' tl',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' → Extra s' ∧ DgP.colsTest tl' = true := by
  intro k s m E ds y cols s' tl' hA _ hS _ ht
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, -, s₀, cols₀, hbeg, -, hfold⟩ := hA.1.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hfold
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hW : planFitsAllB Bs.G₀.W = true := by
    rw [O.W]
    exact h.k8_planFits
  have hk : K8Keeps s s' := keeps_of_stepped hK hS
  obtain ⟨-, -, -, hX, -, -⟩ := cond_of_front
    (P1K8S.front_at_place h.scope h.reads O (P1K8S.planFitsAll_of_test hW) hx _ _ _ _ hfold)
  obtain ⟨tlP, hP, h7, -⟩ := P1K8S.own_at_place h.scope h.reads O hx _ _ _ _ hfold
  obtain ⟨cG, cA, cH⟩ := _root_.Fo.ZPlan.public_cols O.public
  have hc : DgP.colsTest tlP = true := by
    rcases hP with ⟨-, rfl⟩ | ⟨g, hp, -, -, e, rfl⟩ | ⟨g, a, -, -, e, rfl⟩
    · exact cH
    · exact cG g hp e
    · exact cA g a e
  exact ⟨extra_behind_keeps hk hX, cols_behind_keeps hk (lay7_of_test h7) hc ht⟩

include h in
/-- **THE FIELD some, AT ALL 25 DRAWS**, at the description's own parameters. Public data alone. -/
theorem some_field_at_head {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    (ProofFile.k8Par Zp G Xl l).ks ≠ [] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact ks_ne_at_built h.scope h.reads O h.laid.planOk hl e3

/- A check by Lean, no statement: that theorem's end is the record's field some. -/
example (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {blk : Block S ProofFile.Cl} {cells : Tr → Cells} {mats : List (Nat × String × Nat)}
    {A : ProofFile.InstPub × S → WtF → TableE} {iS iD : Item}
    (hI : K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats) A iS iD) :
    K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats) A iS iD :=
  { hI with some := some_field_at_head h hl hG e3 }

/- A check by Lean, no statement: the theorem's end is the record's field. -/
example (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {P : Par × List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P)
    {A : ProofFile.InstPub × S → WtF → TableE} {iS iD : Item}
    (hI : K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P A iS iD) :
    K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells P A iS iD :=
  { hI with
    fine := fine_field_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hK }

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.extra_behind_keeps
#print axioms ProofFile.Honest.K8.cols_behind_keeps
#print axioms ProofFile.Honest.K8.fine_field_at_head
#print axioms ProofFile.Honest.K8.some_field_at_head
