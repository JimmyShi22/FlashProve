-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatText.lean: the code switch: WHAT AN ACCEPTANCE OF THE SEATED PIECE IS
MADE OF, WITH THE DECISION's OWN ACCEPTANCE HANDED ON: beside `seated_atYes` (SeatYes.lean), which
hands on `AtYes` alone: for a law that asks the decision's acceptance itself (the library has «every
drawn position is in range» from it).

Main names:
  `seated_text`: where the piece at the seated sub-protocol (SeatedAt.lean) accepts: the way in lets
    a state t in · at t the kind's decision accepts at the two written rounds' real views and the
    columns that the step shows · the way out gives the state behind · the second round draws as
    many positions as the typed structure counts. By `seated_out`, `piece_is_lawOut`, `outT_inv`,
    `len_at`.
  `seated_both`: the decision's acceptance and `AtYes` (Johnson/Top/H0/K2Hears/Whole.lean) at the
    same two states.
Limits. They say what an acceptance gives; nothing on when there is one. Nothing on soundness. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.SeatYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)

variable {F : Frame} {W W' Cl Cl₀ : Type}
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) (base : ℕ)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)

set_option maxHeartbeats 1000000 in
/-- **WHAT AN ACCEPTANCE OF THE SEATED PIECE IS MADE OF, WITH THE DECISION's OWN ACCEPTANCE HANDED
    ON**: the
way in lets a state t in · at t the kind's own decision accepts at the two written rounds' real
    views
and the columns that the step shows · the way out gives the state behind · the second round draws as
many positions as the typed structure counts. -/
theorem seated_text (w : K2Wr r d₁ d₂) (B : Block Rec Cl) (enter : Rec → Except String Rec)
    (leave : Rec → Rec → Except String Rec) (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)
    (a b : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (ho : (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.out a τ =
      some b) :
    ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
      (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g ∧
      K2.decideWith _root_.Tw.K2.sendByL8 p t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
        (shownP X iJ iQ d₁ d₂ ρ p base ext (t, a.2) τ) = .ok t' := by
  have hs' : SeatStep B (K2.codeSwitchKind (Cl := Claim) p) enter leave := hs
  obtain ⟨t, t', e1, e2, e3⟩ := seated_out (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext)
    (K2.codeSwitchKind (Cl := Claim) p) rfl rfl B enter leave hr hs' ext' a b τ ho
  obtain ⟨b₂, hl⟩ := piece_is_lawOut X iJ iQ d₁ d₂ ρ p base ext strs inX w (t, a.2) (t', b.2) τ e2
  obtain ⟨-, -, ht, -⟩ := outT_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl
  exact ⟨t, t', e1, e3, len_at d₁ d₂ w _ _, ht⟩

/-- **Both at once**: the decision's acceptance and `AtYes` at the same two states. -/
theorem seated_both (w : K2Wr r d₁ d₂) (B : Block Rec Cl) (enter : Rec → Except String Rec)
    (leave : Rec → Rec → Except String Rec) (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)
    (a b : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (ho : (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.out a τ =
      some b) :
    ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
      (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g ∧
      K2.decideWith _root_.Tw.K2.sendByL8 p t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
        (shownP X iJ iQ d₁ d₂ ρ p base ext (t, a.2) τ) = .ok t' ∧
      ∃ x y S3 Y rows G c, K2.AtYes p t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1 τ.2.2.2.1)
        (shownP X iJ iQ d₁ d₂ ρ p base ext (t, a.2) τ) x y S3 Y rows G c := by
  obtain ⟨t, t', e1, e3, hl, ht⟩ := seated_text X iJ iQ d₁ d₂ ρ p base ext w B enter leave hr hs
      ext'
    strs inX a b τ ho
  exact ⟨t, t', e1, e3, hl, ht, K2.yes_whole p t _ _ _ t' ht⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seated_text
#print axioms VerifiableInference.Desc.First.K2Caller.seated_both
