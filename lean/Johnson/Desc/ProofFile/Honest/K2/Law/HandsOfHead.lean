-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/HandsOfHead.lean: the kind "the code switch" (K2): UNDER THE
HEAD ALONE, AT EVERY PLACE OF THE KIND ON THE FIRST CHAIN: THE PROMISE's SIX TESTS AT THE BORDER
BEHIND THE PLACE's BLOCK FOLLOW FROM THE SIX IN FRONT, at a reached state, a yes of the block, and
no mark on either side. The six (`IM.XK` at `P1K2.EQ`): where the chain stands; the open rows'
lists; the groups' members; where the book stands; "in order"; every open public item's test. Four
statements with their proofs; no definition. A joining of the library's theorems.

  `k2_hands_of_head`   `IM.HandsR` (Johnson/IMR/HandsFence.lean) at the library's fence "reached"
                    (`Meaning.K2.FkR`), at the description's own block at a place of the kind: the
                    library's `hHands_at` (Johnson/P1K2R/LastJoin3.lean) with each of its eight
                    named tests paid from the head, as Johnson/P1K2R/LastLineHead.lean,
                    LastLinePlan.lean, LastLineTests.lean and LastLineOfHead.lean pay them
  `k2_xk_behind`    so `IM.XK` at the border k + 1 behind, from `IM.XK` at k in front
  `k2_hands_at`, `k2_xk_behind_at`   the same two at the letters `P5J.At.N`, `P5J.At.links`,
                    `P5J.At.ps`, `P5J.mgAtAll`: they unfold to the letters above

Limits. THE HEAD IS A LONG CONDITION OF ITS OWN. No example of the head is shown here; the library's
`head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one under four
premises on the three public files. The proofs call theorems of Johnson/P1K2R/ (which stand over
Johnson/Top/H0/K2Ties/) and of other files (Johnson/IMR/, Johnson/P5J/ and more).
The statements speak at the letters of
these files (the head's numbers, links, places and meaning): that another file's letters are these
is not shown here. THAT THE SAMPLES ARE STILL HELD BEHIND, AND WHAT THE OPEN PUBLIC ITEMS SAY BESIDE
THEIR TESTS, ARE NOT HERE: they stand in Honest/K2/Law/HeldBehind.lean and
Honest/K2/Law/PubPBehind.lean; "no mark behind" in Honest/K2/Law/NoMarkBehind.lean. The line that
strikes an instance below stands in the imported file too. Nothing on any property.
-/
import Johnson.P1K2R.LastLineOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.Desc.First.K2Caller
open ProofFile (Cl)
open IM (HandsR)
open P1K2 (EQ)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head alone, at every place of the kind.** -/
theorem k2_hands_of_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {B : Block VerifiableInference.Desc.First.S Cl}
    (hB : cF.blocksInOrder[k]? = some B) (ft : Nat) :
    ∀ z, HandsR (Meaning.K2.FkR Zp cF z) (dC Hd).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (dC Hd) mgBase) P5J.fullLinks P5J.At.ps z) ft k B := by
  have hp := P5J.pins_of_laid Hd.toAtMg.scope Hd.toAtMg.laid
  have hm := P5J.madeRow_at_head Hd.toAtMg
  have hSB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ →
      sendsAreB Zp.made.proof.1 358 (snAt Zp G₀ IM.placesW) = true := by
    intro G₀ hG
    have h0 := P5J.sendsB_of_madeRow Hd.toAtMg hm G₀ hG
    rw [← P5J.placesW_at] at h0
    exact h0
  exact hHands_at Hd hp.1 hp.2 hSB (hLP_head Hd) (hK5_head Hd 0 (by omega) rfl) (hK5_head Hd)
    (hHP_head Hd) (Fo.ZPlan.public_heard Hd.toAtMg.pubOne).2.2 ha hk hB ft

/-- **The six tests behind, from the six in front.** -/
theorem k2_xk_behind (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {B : Block VerifiableInference.Desc.First.S Cl}
    (hB : cF.blocksInOrder[k]? = some B) {ft : Nat}
    {z : ProofFile.InstPub} {s s' : VerifiableInference.Desc.First.S} (hf : Meaning.K2.FkR Zp cF z k s)
    (hy : IM.Yes ft B s s')
    (h₀ : s.failed = none) (h₁ : s'.failed = none)
    (hx : IM.XK (dC Hd).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (dC Hd) mgBase) P5J.fullLinks P5J.At.ps z) k s = true) :
    IM.XK (dC Hd).N P5J.fullLinks P5J.At.ps
      (EQ (mgAll (dC Hd) mgBase) P5J.fullLinks P5J.At.ps z) (k + 1) s' = true :=
  (k2_hands_of_head Hd ha hk hB ft z).step hf hy h₀ h₁ hx

/-- The same at the letters of Johnson/P5J/LettersAt.lean and Johnson/P5J/MgAtAll.lean. -/
theorem k2_hands_at (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {B : Block VerifiableInference.Desc.First.S Cl}
    (hB : cF.blocksInOrder[k]? = some B) (ft : Nat) :
    ∀ z, HandsR (Meaning.K2.FkR Zp cF z) (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (EQ (P5J.mgAtAll Hd) P5J.At.links P5J.At.ps z) ft k B :=
  k2_hands_of_head Hd ha hk hB ft

theorem k2_xk_behind_at (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {B : Block VerifiableInference.Desc.First.S Cl}
    (hB : cF.blocksInOrder[k]? = some B) {ft : Nat}
    {z : ProofFile.InstPub} {s s' : VerifiableInference.Desc.First.S} (hf : Meaning.K2.FkR Zp cF z k s)
    (hy : IM.Yes ft B s s')
    (h₀ : s.failed = none) (h₁ : s'.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (EQ (P5J.mgAtAll Hd) P5J.At.links P5J.At.ps z) k s = true) :
    IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (EQ (P5J.mgAtAll Hd) P5J.At.links P5J.At.ps z) (k + 1) s' = true :=
  (k2_hands_at Hd ha hk hB ft z).step hf hy h₀ h₁ hx

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2_hands_of_head
#print axioms ProofFile.Honest.K2.Law.k2_xk_behind
#print axioms ProofFile.Honest.K2.Law.k2_hands_at
#print axioms ProofFile.Honest.K2.Law.k2_xk_behind_at
