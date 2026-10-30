-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RidesJoinLow.lean: `t5_cut_forms` (RidesJoinForms.lean) WITH ITS
PREMISE hF PAID BY `fence_at_merge_later` (FenceAtMergeLater.lean). A join: nothing new is proved.

  t5_cut_low   **`merge_tiedAtR`'s premise t5** at Mg := mgAll 𝔇 Mg, the written list at the full
               size, k := 346: of the fence there is left "every sampled tenant whose pin is open at
               border 346 sits in a tree below base"

Limits. That premise, hsmp, `Fwd` at each run under the six names, the six public tests in front and
"each of the two sentences worth goes back" stay premises. Shown at no real state. No soundness
statement.

-/
import Johnson.Top.H0.MergeLaw.RidesJoinForms
import Johnson.Top.H0.MergeLaw.FenceAtMergeLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Item Meaning Numbers start flatPlacesOf sampledIn
  openSets)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **THE FIFTH TIE, CUT DOWN TO THE TWO, THE FENCE PAID.** -/
theorem t5_cut_low {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Fr : Frame} (Nn : Numbers) (Pm : HeadMergeP) (base : ℕ) (ds : List RDT)
    (low : ∀ x ∈ sampledIn Nn
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD []),
      x.1 < base)
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = 𝔇.smp (z, s))
    (z : P) (a b : S × Fr.E.Str) (w : Wit (CellsQ rows cols) Tok MsgT) (i : Item)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    (hrel : relQ Nn (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (346 + 1) b w)
    (hf : ∀ x ∈ sixNames, ∀ p ∈ 𝔇.runs 24 x.1 x.2, Fwd (𝔇.Rd 24) p.1 p.2 a.1 b.1)
    (hin : ∀ x ∈ sixNames, (mgAll 𝔇 Mg).pub (.formsIn 24 x.1 x.2) (z, a.1) = true)
    (hW : ∀ j ∈ worthAtMerge, meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j b w →
      meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j a w)
    (hi : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 346 i)
    (hn : ¬ insQ linksFull (flatPlacesOf linksFull true) 346 i) :
    meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) i a w :=
  t5_cut_forms 𝔇 Mg Nn Pm base ds (fence_at_merge_later Nn base low 𝔇.ms) hsmp z a b w i hy hb hrel
    hf hin hW hi hn

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.t5_cut_low
