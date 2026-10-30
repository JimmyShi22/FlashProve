-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/LeftOverOfHeard.lean: THE SMALLNESS TEST: THE NAMED PREMISE
`LeftOverAtStand` (Johnson/Desc/ProofFile/Honest/K8/FrontOfReach.lean; group (6) of what the three
sentences of K8BehindTop.lean still owe) FROM SMALLER ONES, AT THE 24 SEGMENTS IN FRONT OF THE
HEAD's, WHERE THE THREAD's BLOCKS ARE THE FIRST CHAIN's OWN, IN THE GOALS' SCOPE: that the lookup
has heard something falls; `FrontLeftOver`'s eight give way to ONE PUBLIC TEST WITH CODE AT THE
BUILT SEGMENT's DATA AND, AT EVERY STAND, TWO SENTENCES: the words of one coordinate of the lookup's
key point lie below the prime · the digits' array has the name "ZZ". A joining; none of the
library's goals.

  `LeftHeardAtStand` a named premise between: at every stand the state in front shows tl, F and
                   funs; at whatever the lookup has heard FrontLeftHeard tl F g
                   (Johnson/Desc/K8/Honest/FrontFromSizes.lean); a member of the link's list for
                   each array
  `leftOverAtStand_of_heard` the scope · the files read · an opening of the description · the
                   description's test on its plan · l < 24 · the built segment number l ·
                   ChainThread T b c Z l · the public test at the built segment's data ·
                   LeftHeardAtStand ⊢ LeftOverAtStand
  `LeftBelowAtStand` THE NAMED PREMISE THAT STAYS: the same with the two sentences in the stead of
                   FrontLeftHeard
  **`leftHeardAtStand_of_below`**, **`leftOverAtStand_of_below`** under the same: LeftBelowAtStand ⊢
                   LeftHeardAtStand, and so LeftOverAtStand
By: `reach_at_stand` (FrontOfReach.lean) · `forms_at_batch`
(Johnson/Desc/K8/Honest/AllFrontAtBatch.lean) · `six_of_heard` (FrontFromSizes.lean) ·
`leftOver_of_six` (FrontSharper.lean) · `heardSizes_at_batch` (HeardAtReach.lean) ·
`pointsHeld_at_batch` (WeightsAtReach.lean).
Limits. AN IMPLICATION STILL: `LeftBelowAtStand`, `ChainThread` and the public test ARE PAID BY
NOBODY HERE; the test is evaluated, not proved: yes at the 25 plans of each of the library's two
stored full-size sets of files and at the small configuration's five. A stand holds that all that
the run has seen has its words below the prime (`SaidOk`): that the coordinate is among what was
seen is not shown. NOTHING AT THE HEAD's SEGMENT. NO MEMBER: that the premises can hold together is
not shown; where there is no stand all is idle. IN SCOPE ALONE. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.K8BehindTop
import Johnson.Desc.K8.Honest.WeightsAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

variable (Lk p T b) in
/-- A named premise between. -/
def LeftHeardAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∃ (tl : HTailF2) (F : Fork) (funs : Array HFun), s.tl? = some tl ∧ s.fork? = some F ∧
      s.funs? = some funs ∧ (∀ g, tl.heard = some g → FrontLeftHeard tl F g) ∧
      ∀ a0, Desc.K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size

variable (Lk p T b) in
/-- **The named premise that stays.** -/
def LeftBelowAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∃ (tl : HTailF2) (F : Fork) (funs : Array HFun), s.tl? = some tl ∧ s.fork? = some F ∧
      s.funs? = some funs ∧
      (∀ g, tl.heard = some g → OnBytes.okE (g.zy.getD 0 zeroE) = true ∧
        (F.trees.getD tl.ix.ZZ {}).name = "ZZ") ∧
      ∀ a0, Desc.K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE 24 SEGMENTS IN FRONT OF THE HEAD's.** -/
theorem leftOverAtStand_of_heard (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hP : heldPubB Xl.tl = true)
    (hL : LeftHeardAtStand Lk p T b) : LeftOverAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨tl, Fk, funs, ht, hF, hf, L, hT⟩ := hL κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt C.len hq C.stored
  rw [C.ft, C.bs, C.border] at r
  have r9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (q, s) := by
    rw [if_neg (by omega)] at r
    exact r
  obtain ⟨g, hg, h1, h2⟩ := forms_at_batch hS hR O hOk hl r9 ht
  exact ⟨tl, Fk, funs, g, ht, hF, hf, hg,
    leftOver_of_six hS hR O (by omega) e3 r ht
      (six_of_heard hS hR O (by omega) e3 r ht hP (L g hg)) h1 h2, hT⟩

/-- **From the two sentences.** -/
theorem leftHeardAtStand_of_below (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hP : heldPubB Xl.tl = true)
    (hL : LeftBelowAtStand Lk p T b) : LeftHeardAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨tl, Fk, funs, ht, hF, hf, L, hT⟩ := hL κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt C.len hq C.stored
  rw [C.ft, C.bs, C.border, if_neg (by omega)] at r
  obtain ⟨g, hg, hZ, b0, b1⟩ := heardSizes_at_batch hS hR O hOk hl e3 r ht hP
  obtain ⟨g', hg', pt⟩ := pointsHeld_at_batch hS hR O hOk hl e3 r ht hP
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  refine ⟨tl, Fk, funs, ht, hF, hf, fun g₂ hg₂ => ?_, hT⟩
  obtain rfl : g = g₂ := Option.some.inj (hg.symm.trans hg₂)
  exact ⟨b0, b1, hZ, pt (L g hg).1, (L g hg).2⟩

/-- **And so the premise of the three sentences.** -/
theorem leftOverAtStand_of_below (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hP : heldPubB Xl.tl = true)
    (hL : LeftBelowAtStand Lk p T b) : LeftOverAtStand Lk p T b :=
  leftOverAtStand_of_heard hS hR O hOk hl e3 C hP
    (leftHeardAtStand_of_below hS hR O hOk hl e3 C hP hL)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.leftOverAtStand_of_heard
#print axioms ProofFile.Honest.K8.leftHeardAtStand_of_below
#print axioms ProofFile.Honest.K8.leftOverAtStand_of_below
