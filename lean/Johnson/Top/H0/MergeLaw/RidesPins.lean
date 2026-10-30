-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RidesPins.lean: THE THIRD CUT: OF THE SIXTEEN ITEMS OF THE
MERGE's FIFTH TIE (RidesAtMerge.lean) THE TWO PINS RIDE BACK: "pin m t", at every m and t, at every
filling whose pins are the library's (pinJT over a list of members), and so at the composed meaning.
After merge_hcb (CtxBack.lean), which pays "pin m 0".

  pin_back         **"pin m t" goes back over the merge's accepting step**
  pin_back_mgAll   at mgAll 𝔇 Mg: the premise on the filling's pins is paid (mgAll_pin)

Limits. TWO PREMISES STAY: hF: every member of the list that sits at a place of Nn.sent m t was sent
in front of the merge's stretch of rounds (Fenced base [x]); hsmp: the reader of the OOD samples
does not read what the merge writes. Both are merge_hcb's own, at other places. AT ckP .two, as
merge_tiedAtR's t5 has it (pinJT_rides is general in it). Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.CtxBack
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Item Meaning Numbers)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **"pin m t" goes back over the merge's accepting step.** -/
theorem pin_back (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    {Fr : Frame} (ms : List Mem) (Nn : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT)) (m t : ℕ)
    (P : HeadMergeP) (base : ℕ) (ds : List RDT)
    (hpin : ∀ j t a y w, Mg.pin j t a y w ↔ pinJT cs G arr smp ms j t a y w)
    (hF : ∀ p ∈ Nn.sent m t, ∀ x ∈ ms, SitsAt x p.1 p.2 → Fenced base [x])
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      smp (z, { s with rowsOwed := none, here := .head a' }) = smp (z, s))
    (z : Pp) (a b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hy : ∃ rs, headMergeDecide P a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    (h : meansQ Nn Mg (fun s => (z, s)) (.pin m t) b w) :
    meansQ Nn Mg (fun s => (z, s)) (.pin m t) a w := by
  obtain ⟨rs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  obtain ⟨_, a', _, _, e, _⟩ := isLocal P a.1 rs b.1 hy
  have es : smp (z, b.1) = smp (z, a.1) := by rw [e, hsmp]
  have h' : ∀ x ∈ Nn.sent m t, Mg.pin x.1 x.2 (z, b.1) (strsOf Fr b.2) w := h
  show ∀ x ∈ Nn.sent m t, Mg.pin x.1 x.2 (z, a.1) (strsOf Fr a.2) w
  intro p hp
  have g := h' p hp
  rw [hpin] at g ⊢
  rw [hb] at g
  exact pinJT_rides cs G arr smp ms base ds p.1 p.2 (hF p hp) (z, a.1) (z, b.1) a.2 τ
    (fun x _ _ => by rw [es]) w g

/-- **At the composed meaning.** -/
theorem pin_back_mgAll {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Fr : Frame} (Nn : Numbers) (m t : ℕ) (Pm : HeadMergeP) (base : ℕ) (ds : List RDT)
    (hF : ∀ p ∈ Nn.sent m t, ∀ x ∈ 𝔇.ms, SitsAt x p.1 p.2 → Fenced base [x])
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = 𝔇.smp (z, s))
    (z : P) (a b : S × Fr.E.Str) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    (h : meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) (.pin m t) b w) :
    meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) (.pin m t) a w :=
  pin_back 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms Nn (mgAll 𝔇 Mg) m t Pm base ds
    (fun _ _ _ _ _ => by rw [mgAll_pin]) hF hsmp z a b w hy hb h

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.pin_back
#print axioms VerifiableInference.Desc.First.MergeLaw.pin_back_mgAll
