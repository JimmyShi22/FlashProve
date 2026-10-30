-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RidesJoin.lean: THE MERGE's FIFTH TIE AT THE COMPOSED MEANING,
AT THE WRITTEN LIST AT THE FULL SIZE, AT NUMBER 346: CUT DOWN FROM SIXTEEN ITEMS TO
EIGHT.

  restAtMerge      the eight that are left: the six runs of forms, the two sentences "worth"
  t5_cut           **merge_tiedAtR's premise t5** (TiesReached.lean), at Mg := mgAll 𝔇 Mg₀, links :=
                   linksFull, ps := flatPlacesOf linksFull true, k := 346: from "each of the eight
                   goes back", the fence at the two pins' places, and hsmp

Limits. THE EIGHT ARE A PREMISE (hRest). t5's own premises on the state in front (the table's
condition, Rch, "no mark", the condition behind) are not spent here: whoever pays hRest may want
them. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RidesRows
import Johnson.Top.H0.MergeLaw.RidesPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Item Meaning Numbers start flatPlacesOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- The eight that are left. -/
def restAtMerge : List Item :=
  [.forms 24 3 "objects", .forms 24 3 "planes", .forms 24 4 "join", .forms 24 4 "own",
    .forms 24 6 "small", .forms 24 8 "objects", .worth 24 8 "planes", .worth 24 8 "keys"]

/-- **THE FIFTH TIE, CUT DOWN TO THE EIGHT.** -/
theorem t5_cut {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Fr : Frame} (Nn : Numbers) (Pm : HeadMergeP) (base : ℕ) (ds : List RDT)
    (hF : ∀ t, t = 1 ∨ t = 2 → ∀ p ∈ Nn.sent 24 t, ∀ x ∈ 𝔇.ms, SitsAt x p.1 p.2 →
      Fenced base [x])
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = 𝔇.smp (z, s))
    (z : P) (a b : S × Fr.E.Str) (w : Wit (CellsQ rows cols) Tok MsgT) (i : Item)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    (hrel : relQ Nn (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (346 + 1) b w)
    (hRest : ∀ j ∈ restAtMerge, meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j b w →
      meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j a w)
    (hi : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 346 i)
    (hn : ¬ insQ linksFull (flatPlacesOf linksFull true) 346 i) :
    meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) i a w := by
  refine t5_of_each Nn (mgAll 𝔇 Mg) (fun s => (z, s)) a b w hrel (fun j hj hm => ?_) i hi hn
  unfold ridesAtMerge at hj
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact six_back 𝔇 Mg Nn z a b hy w _ (Or.inl rfl) hm
  · exact six_back 𝔇 Mg Nn z a b hy w _ (Or.inr ⟨_, _, rfl⟩) hm
  · exact six_back 𝔇 Mg Nn z a b hy w _ (Or.inr ⟨_, _, rfl⟩) hm
  · exact six_back 𝔇 Mg Nn z a b hy w _ (Or.inr ⟨_, _, rfl⟩) hm
  · exact six_back 𝔇 Mg Nn z a b hy w _ (Or.inr ⟨_, _, rfl⟩) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact six_back 𝔇 Mg Nn z a b hy w _ (Or.inr ⟨_, _, rfl⟩) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact hRest _ (by simp [restAtMerge]) hm
  · exact pin_back_mgAll 𝔇 Mg Nn 24 2 Pm base ds (hF 2 (Or.inr rfl)) hsmp z a b w hy hb hm
  · exact pin_back_mgAll 𝔇 Mg Nn 24 1 Pm base ds (hF 1 (Or.inl rfl)) hsmp z a b w hy hb hm

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.t5_cut
