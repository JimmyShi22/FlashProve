-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/ShownRidesAll.lean: K11's SECOND TIE: THE PREMISE hSN OF `merge_t2`
(TieOneTwo.lean) AT THE COMPOSED FILLING `mgAll 𝔇 Mg₀` (Johnson/Desc/Sound/MgAll.lean), AT ANY LIST
OF LINKS, LIST OF PLACES AND BORDER k. A theorem: a call of `merge_hSN` (ShownRides.lean): the
filling's "shown" and "no collision" are the library's over 𝔇.ms by rfl (`mgAll_shown`,
`mgAll_noColl`); the fence by `fenced_of_low` (FenceAtMerge.lean) from: every sampled place of the
open set lies in a tree below the merge's base.
Left: low (at the written list at the full size, border 346: the frame's own law on the pieces'
bases) · hsmp (the filling's reader of the samples does not read what the merge writes) · the two
facts on a and b, which the tie's caller holds.
Limits. An implication: shown at no state. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.ShownRides
import Johnson.Top.H0.MergeLaw.FenceAtMerge
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Numbers Meaning sampledIn openSets start)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **hSN OF `merge_t2` AT THE COMPOSED FILLING.** -/
theorem merge_hSN_all {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    {Fr : Frame} (𝔇 : MgData Xi Pp Tok rows cols nR X)
    (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) (Nn : Numbers) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (P : HeadMergeP) (base : ℕ) (ds : List RDT)
    (low : ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []), x.1 < base)
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = 𝔇.smp (z, s))
    (z : Pp) (a b : S × Fr.E.Str) (hy : ∃ rs, headMergeDecide P a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ) :
    ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []),
      (mgAll 𝔇 Mg₀).shown x.1 x.2 (strsOf Fr a.2) ∧
          (mgAll 𝔇 Mg₀).noColl x.1 x.2 (z, a.1) (strsOf Fr a.2) →
        (mgAll 𝔇 Mg₀).shown x.1 x.2 (strsOf Fr b.2) ∧
          (mgAll 𝔇 Mg₀).noColl x.1 x.2 (z, b.1) (strsOf Fr b.2) :=
  merge_hSN 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms (mgAll 𝔇 Mg₀) _ P base ds (fun _ _ _ => Iff.rfl)
    (fun _ _ _ _ => Iff.rfl) (fenced_of_low low 𝔇.ms) hsmp z a b hy hb

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hSN_all
