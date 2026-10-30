-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3HeadSmallBack.lean: THE FIELD "smallBack" AT THE OUTPUT HEAD's SEGMENT:
the head's twin of the lookups' `small_back` (Johnson/Desc/First/Look/K3CallsSmallBack.lean, which
has hm : m ≠ hd): where the meaning's letter constr is `P5J.constrQAt`
(Johnson/P5J/MeansQ.lean), the part "small" of the head's segment goes back past an accept of ANY
piece over the verifier's state, UNDER ONE PREMISE MORE: hHead: the letter headPart at the part
"small" goes back over `SameBut`. An unfolding: that file's proof, line for line, up to the arm of
the head. NO SOUNDNESS IS CLAIMED.

  `small_back_head`: general in the meaning.
  `headMg_smallBack`: at the composed meaning `mgAll 𝔇 Mg` (Johnson/Desc/Sound/MgAll.lean), where
    `headLink X = 24`: its end is the field `HeadLeftR.smallBack`
    (Johnson/Desc/First/Look/K3HeadRestR.lean) at m := 24.

OBJECT: no text that runs: the table of joints' item constr hd .small.
USER: Johnson/P5J/K03HeadAt.lean. LETTERS: `constrQAt`'s own; decT: the one decoder of the committed
table; p: any piece.
THE PREMISES, BY NAME: hc · hdec · hS (as in `small_back`) · hHead.
Limits. AT THE PART "small" ALONE: at the part lookCallsHeard hHead is false without "the heard
reply is the same". hHead is not paid here (`headPartK6_goesBack` is meant).
Not claimed: anything on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Look.K3CallsModel
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Desc.Sound.DecodesAtPiece
import Johnson.Desc.Sound.MgAll

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
  {hd : ℕ} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
  {put : P5J.TReq → Fin ppref.V → P5J.TReq}
  {H : P5J.HidAt X P (Desc.Wit Cells Tok MsgT) rows cols}
  {headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {digitsPart : ℕ → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {decT : (ℕ → Option (ℕ × List UInt64)) → P × P5J.TS → Option (Fin rows → Fin cols → Flat.GE)}

/-- **smallBack at the head's segment**: the head's twin of `small_back`. -/
theorem small_back_head (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hdec : H.dec = fun a y => decT y.cell a)
    (hS : ∀ c z s s', decT c (z, s) = decT c (z, s')) (z : P)
    (hHead : ∀ (s s' : Desc.First.S) i y y' w, SameBut s s' →
      headPart .small i (z, s') y' w → headPart .small i (z, s) y w)
    (p : Piece C Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) :
    ∀ (a b : Desc.First.S × Fr.E.Str) w, (∃ τ, p.ior.red.out a τ = some b) → SameBut a.1 b.1 →
      Mg.constr hd .small (z, b.1) (strsOf Fr b.2) w →
      Mg.constr hd .small (z, a.1) (strsOf Fr a.2) w := by
  rintro a b w ⟨τ, hb⟩ hs h
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
  rw [if_pos rfl] at h2 ⊢
  exact hHead a.1 b.1 i _ _ w hs h2

end

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame} {C : Run.PQ.CK}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **At the composed meaning.** -/
theorem headMg_smallBack (hS : ∀ c z s s', 𝔇.decT c (z, s) = 𝔇.decT c (z, s'))
    (h24 : headLink X = 24) (z : P)
    (hHead : ∀ (s s' : Desc.First.S) i y y' w, SameBut s s' →
      𝔇.headPart .small i (z, s') y' w → 𝔇.headPart .small i (z, s) y w)
    (p : Piece C Fr Desc.First.S Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)) :
    ∀ (a b : Desc.First.S × Fr.E.Str) w, (∃ τ, p.ior.red.out a τ = some b) → SameBut a.1 b.1 →
      (mgAll 𝔇 Mg).constr 24 .small (z, b.1) (strsOf Fr b.2) w →
      (mgAll 𝔇 Mg).constr 24 .small (z, a.1) (strsOf Fr a.2) w := by
  have h := small_back_head (hd := headLink X) (mgAll_constr 𝔇 Mg) (decT := 𝔇.decT) rfl hS z hHead
    p
  rw [h24] at h
  exact h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.small_back_head
#print axioms VerifiableInference.OnPublicFiles.headMg_smallBack
