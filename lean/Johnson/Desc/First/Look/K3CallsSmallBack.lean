-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsSmallBack.lean: the lookup on a link's CALLS: THE FIELD "smallBack"
OF THE TABLES' TIES (AttTiesR, LayTiesR, Johnson/Desc/First/Look/K3CallsMeanR.lean) WHERE THE
MEANING's LETTER constr IS constrQAt (Johnson/P5J/MeansQ.lean): the part "small" of a
segment that is not the head's goes back past an accept of ANY piece over the verifier's state. Why:
at such a segment the part reads the statement and the strings through the decoder's guard alone;
the decoder does not read the state, and the committed table's string passes every sub-protocol
unturned. An unfolding: no new mathematics. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' item constr m .small.
USER: Johnson/Desc/Sound/MgAt/K3Calls.lean.
  Meant: the premise smallBack of attTies_ofR, layTies_ofR at the composed meaning.
LETTERS: constrQAt's own; decT: the one decoder of the committed table; p: any piece.

THE PREMISES, BY NAME: hc (constr is constrQAt) · hdec (H.dec is decT at the strings' cells) · hS
  (decT does not read the state) · hm (the segment is not the head's).

Main name: `small_back`.

Limits. Not at the head's segment (there the part is the letter headPart).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsModel
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Desc.Sound.DecodesAtPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker Run
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)

section
variable {P Cl Cells Tok : Type} {rows cols : ℕ} {X : Verify.Public} {Fr : Frame} {C : Run.PQ.CK}
  {m hd : ℕ} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
  {put : P5J.TReq → Fin ppref.V → P5J.TReq}
  {H : P5J.HidAt X P (Desc.Wit Cells Tok MsgT) rows cols}
  {headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {digitsPart : ℕ → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {decT : (ℕ → Option (ℕ × List UInt64)) → P × P5J.TS → Option (Fin rows → Fin cols → Flat.GE)}

/-- **smallBack.** -/
theorem small_back (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hdec : H.dec = fun a y => decT y.cell a)
    (hS : ∀ c z s s', decT c (z, s) = decT c (z, s')) (hm : m ≠ hd) (z : P)
    (p : Piece C Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) :
    ∀ (a b : Desc.First.S × Fr.E.Str) w, (∃ τ, p.ior.red.out a τ = some b) → SameBut a.1 b.1 →
      Mg.constr m .small (z, b.1) (strsOf Fr b.2) w →
      Mg.constr m .small (z, a.1) (strsOf Fr a.2) w := by
  rintro a b w ⟨τ, hb⟩ - h
  have e : (strsOf Fr b.2).cell = (strsOf Fr a.2).cell := by
    rw [out_behind p a b τ hb]
    rfl
  rw [hc] at h ⊢
  unfold P5J.constrQAt at h ⊢
  rw [if_neg (show ¬ ((.small : P5J.TPart) = .lookDigits) by decide)] at h ⊢
  refine ⟨h.1, fun M i hM hi => ?_⟩
  have hM' : H.dec (z, b.1) (strsOf Fr b.2) = some M := by
    rw [hdec] at hM ⊢
    show decT (strsOf Fr b.2).cell (z, b.1) = some M
    rw [e, hS _ z b.1 a.1]
    exact hM
  have h2 := h.2 M i hM' hi
  rw [if_neg hm] at h2 ⊢
  by_cases he : m % 2 = 0
  · rw [if_pos he] at h2 ⊢
    exact h2
  · rw [if_neg he] at h2 ⊢
    exact h2

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.small_back
