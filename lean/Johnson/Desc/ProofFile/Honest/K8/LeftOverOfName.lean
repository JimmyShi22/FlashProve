-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/LeftOverOfName.lean: THE SMALLNESS TEST: THE NAMED PREMISE
`LeftOverAtStand` (Johnson/Desc/ProofFile/Honest/K8/FrontOfReach.lean), AT THE 24 SEGMENTS IN FRONT
OF THE HEAD's, WHERE THE THREAD's BLOCKS ARE THE FIRST CHAIN's OWN, IN THE GOALS' SCOPE: THE
SENTENCE ON WORDS OF `LeftBelowAtStand` (LeftOverOfHeard.lean) IS PAID AT EVERY STAND: what stays
has a name of its own. A definition and two joinings; none of the library's goals.

  `LeftNameAtStand` the named premise that stays: `LeftBelowAtStand` less its sentence on words, to
                   the sign: at every stand the state in front shows tl, F and funs; where the
                   lookup has heard, the digits' array has the name "ZZ"; the link's list has a
                   member for each array
  **`leftBelowAtStand_of_name`** the scope · the files read · an opening of the description · its
                   test on its plan · l < 24 · ChainThread · LeftNameAtStand ⊢ LeftBelowAtStand
  **`leftOverAtStand_of_name`** so, with the built segment: LeftOverAtStand
By: `reach_below` (Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean): each stand's state in front is
reached by the wrapped blocks, since what the thread has said has its words below the prime ·
`zy0_below_at_wrap` (Johnson/Desc/K8/Honest/ZyBelowAtWrap.lean) · `leftOverAtStand_of_two`
(LeftOverOfTwo.lean).
Limits. IMPLICATIONS STILL: `LeftNameAtStand` AND `ChainThread` (K8BehindTop.lean) ARE PAID BY
NOBODY HERE. NOTHING AT THE HEAD's SEGMENT. NO MEMBER: that the premises can hold together is not
shown; where there is no stand all is idle. IN SCOPE ALONE. No prover stands in it. Nothing is
claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LeftOverOfTwo
import Johnson.Desc.K8.Honest.ZyBelowAtWrap

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
/-- **The named premise that stays.** -/
def LeftNameAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∃ (tl : HTailF2) (F : Fork) (funs : Array HFun), s.tl? = some tl ∧ s.fork? = some F ∧
      s.funs? = some funs ∧ (∀ g, tl.heard = some g → (F.trees.getD tl.ix.ZZ {}).name = "ZZ") ∧
      ∀ a0, Desc.K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The sentence on words is paid at every stand.** -/
theorem leftBelowAtStand_of_name (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) (C : ChainThread T b c Z l) (hL : LeftNameAtStand Lk p T b) :
    LeftBelowAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨tl, Fk, funs, ht, hF, hf, hn, hT⟩ := hL κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_below T (ProofFile.startS Z) q C.len hq C.stored hSt.thr
  rw [C.ft, C.bs, C.border, if_neg (by omega)] at r
  exact ⟨tl, Fk, funs, ht, hF, hf,
    fun g hg => ⟨zy0_below_at_wrap hS hR O hOk hl r ht hg 0, hn g hg⟩, hT⟩

/-- **And so the premise of the three sentences.** -/
theorem leftOverAtStand_of_name (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftNameAtStand Lk p T b) : LeftOverAtStand Lk p T b :=
  leftOverAtStand_of_two hS hR O hOk hl e3 C (leftBelowAtStand_of_name hS hR O hOk hl C hL)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.leftBelowAtStand_of_name
#print axioms ProofFile.Honest.K8.leftOverAtStand_of_name
