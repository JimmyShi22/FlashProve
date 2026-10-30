-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Guard.lean: the kind "lookup" (K3), the lookup on the calls at the head's
link: THE TWO FIELDS THAT THE GUARD ON worth BROUGHT INTO `HeadAtTable`
(Johnson/Desc/First/Look/K3HeadAtTable.lean), AT THE COMPOSED MEANING `mgAll 𝔇 Mg`
(Johnson/Desc/Sound/MgAll.lean), at the guard gd w := "the witness's cells hold an index"
(`Flat.InRange w.cells`).

Main names:
  `constr_free`: KIND-FREE: where the witness's cells hold no index and the stored table's pin
    holds, every part of the model's relation but "small" and the digits' holds of itself, at every
    segment: its own guard ("whatever index the decoded table holds") is empty there, for the pin
    says that the decoded table IS the witness's cells.
  `headMg_free`: the field free, to the letter.
  `k3Mg_pinW_back`, `k3Mg_pinW_back_yes`: the stored table's pin goes back past any piece's yes;
    the second is the field pinWBack, to the letter. Kind-free too.

Limits: hS (the decoder does not read the first chain's verifier's state) is a premise on 𝔇, as in
Johnson/Desc/Sound/MgAt/K3Decodes.lean. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3Decodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker Run
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Wit Strs)

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  {C : Run.PQ.CK}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **Where the cells hold no index, a guarded part holds of itself.** -/
theorem constr_free (k : ℕ) (p : Desc.First.Part) (h1 : p ≠ .lookDigits) (h2 : p ≠ .small)
    (a : P × Desc.First.S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hg : ¬ Flat.InRange w.cells) (hw : (mgAll 𝔇 Mg).pinW a y w) :
    (mgAll 𝔇 Mg).constr k p a y w := by
  rw [mgAll_constr]
  unfold P5J.constrQAt
  rw [if_neg h1]
  refine ⟨fun h => absurd h h2, fun M i hM hH => ?_⟩
  have e : M = w.cells := dec_is_cells 𝔇.decT 𝔇.H a y w M hM hw
  subst e
  exact absurd ⟨i, hH⟩ hg

/-- **free.** -/
theorem headMg_free (m : ℕ) (z : P) (a : Desc.First.S × Fr.E.Str)
    (w : Wit (CellsQ rows cols) Tok MsgT) (hg : ¬ Flat.InRange w.cells)
    (hw : (mgAll 𝔇 Mg).pinW (z, a.1) (strsOf Fr a.2) w) :
    (mgAll 𝔇 Mg).constr m .lookCallsHeard (z, a.1) (strsOf Fr a.2) w ∧
      (mgAll 𝔇 Mg).constr m .rider (z, a.1) (strsOf Fr a.2) w :=
  ⟨constr_free 𝔇 Mg m _ (by decide) (by decide) _ _ w hg hw,
    constr_free 𝔇 Mg m _ (by decide) (by decide) _ _ w hg hw⟩

/-- **The stored table's pin goes back past any piece's yes.** -/
theorem k3Mg_pinW_back (hS : ∀ c z s s', 𝔇.decT c (z, s) = 𝔇.decT c (z, s')) (z : P)
    (p : Piece C Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT))
    (a b : Desc.First.S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h : (mgAll 𝔇 Mg).pinW (z, b.1) (strsOf Fr b.2) w) :
    (mgAll 𝔇 Mg).pinW (z, a.1) (strsOf Fr a.2) w :=
  pinW_at_piece 𝔇.decT (fun s => (z, s)) p a b τ hb w (hS _ z b.1 a.1) h

/-- **pinWBack.** -/
theorem k3Mg_pinW_back_yes (hS : ∀ c z s s', 𝔇.decT c (z, s) = 𝔇.decT c (z, s')) (z : P)
    (p : Piece C Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT)) :
    ∀ (a b : Desc.First.S × Fr.E.Str) w, (∃ τ, p.ior.red.out a τ = some b) → SameBut a.1 b.1 →
      (mgAll 𝔇 Mg).pinW (z, b.1) (strsOf Fr b.2) w →
      (mgAll 𝔇 Mg).pinW (z, a.1) (strsOf Fr a.2) w :=
  fun a b w ⟨τ, hb⟩ _ h => k3Mg_pinW_back 𝔇 Mg hS z p a b τ hb w h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.constr_free
#print axioms VerifiableInference.OnPublicFiles.headMg_free
#print axioms VerifiableInference.OnPublicFiles.k3Mg_pinW_back
#print axioms VerifiableInference.OnPublicFiles.k3Mg_pinW_back_yes
