-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/DecodesAtMerge.lean: "THE COMMITTED TABLE DECODES" RIDES PAST AN ACCEPTING
STEP OF THE MERGE OF THE CLAIMS ON THE COMMITTED TABLE (kind K11), AT THE COMPOSED MEANING
`mgAll D Mg` (Johnson/Desc/Sound/MgAll.lean): the premise hD of `merge_tiedAtR`
(Johnson/Top/H0/MergeLaw/TiesReached.lean), to the letter.

  DecKeeps decT      THE ONE PREMISE, ON THE PARAMETER D.decT: where the decoder of the committed
                     table answers at a state, it answers at that state with "no linear claim is
                     owed" and another content of the output head's own part: which is all that an
                     accepting step of the merge turns (`isLocal`, MergeLaw/Law.lean)
  decKeeps_of_hdec   it follows from hdec, the premise that `merge_hcb` and `merge_tiedAtR` bear
                     already ("the decoder gives one thing at both")
  decKeeps_blind     IT CAN BE MET: at every decoder that reads nothing of the verifier's state
  not_decKeeps       IT CAN FAIL: at a decoder that answers only while a linear claim is owed
  merge_hD           THE ROW: by `mgAll_decodes`, `isLocal` and `decodes_rides`
                     (Johnson/Desc/Sound/DecodesRides.lean): the table's cells stay behind a stretch
  merge_hD_of_hdec   the same from hdec

Limits. D, Mg, P, base and ds are letters. DecKeeps is shown at no real filling here. That the merge
accepts at any state is not shown. No soundness statement.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.DecodesRides
import Johnson.Top.H0.MergeLaw.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Meaning)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

section
variable {Pp Cells : Type}

/-- **The one premise**: the decoder does not fall silent over what the merge turns. -/
def DecKeeps (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) : Prop :=
  ∀ z c (s : S) (a' : HeadOwn), (decT c (z, s)).isSome = true →
    (decT c (z, { s with rowsOwed := none, here := .head a' })).isSome = true

theorem decKeeps_of_hdec (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      decT c (z, { s with rowsOwed := none, here := .head a' }) = decT c (z, s)) :
    DecKeeps decT := fun z c s a' h => by
  rw [hdec]
  exact h

/-- **It can be met**: at every decoder that reads nothing of the verifier's state. -/
theorem decKeeps_blind (f : (ℕ → Option (ℕ × List UInt64)) → Pp → Option Cells) :
    DecKeeps (fun c (x : Pp × S) => f c x.1) := fun _ _ _ _ h => h

/-- **It can fail**: at a decoder that answers only while a linear claim is owed. -/
theorem not_decKeeps (z : Pp) (M : Cells) (s : S) (a' : HeadOwn) :
    ¬ DecKeeps (fun _ (x : Pp × S) => if x.2.rowsOwed = some 0 then some M else none) := fun H => by
  have h := H z (fun _ => none) { s with rowsOwed := some 0 } a' (by simp)
  simp at h

end

section
variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi Pp Tok rows cols nR X) (Mg : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame}

/-- **"decodes" rides past the merge's accepting step**: `merge_tiedAtR`'s hD, to the letter. -/
theorem merge_hD (P : HeadMergeP) (base : ℕ) (ds : List RDT) (hk : DecKeeps D.decT) :
    ∀ (z : Pp) (a b : S × Fr.E.Str), (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ) →
      (mgAll D Mg).decodes (z, a.1) (strsOf Fr a.2) →
      (mgAll D Mg).decodes (z, b.1) (strsOf Fr b.2) := by
  rintro z a b ⟨rs, hy⟩ ⟨τ, hb⟩ h
  obtain ⟨_, a', _, _, e, _⟩ := isLocal P a.1 rs b.1 hy
  rw [mgAll_decodes] at h ⊢
  rw [hb, e]
  exact decodes_rides D.decT (ckP .two) Fr base ds a.2 τ (z, a.1) _ (hk z _ a.1 a') h

theorem merge_hD_of_hdec (P : HeadMergeP) (base : ℕ) (ds : List RDT)
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      D.decT c (z, { s with rowsOwed := none, here := .head a' }) = D.decT c (z, s)) :
    ∀ (z : Pp) (a b : S × Fr.E.Str), (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ) →
      (mgAll D Mg).decodes (z, a.1) (strsOf Fr a.2) →
      (mgAll D Mg).decodes (z, b.1) (strsOf Fr b.2) :=
  merge_hD D Mg P base ds (decKeeps_of_hdec D.decT hdec)

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.decKeeps_of_hdec
#print axioms VerifiableInference.Desc.First.MergeLaw.decKeeps_blind
#print axioms VerifiableInference.Desc.First.MergeLaw.not_decKeeps
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hD
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hD_of_hdec
