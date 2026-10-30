-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/NoMarkSeat.lean: THE SEATED CODE SWITCH ACCEPTS AT NO MARKED STATE, where its
    way out ends without a mark. One theorem. A law file: no sub-protocol imports it.

Why. The rule that makes a tie of the structure of ties (`tiedAtR_of_ties`,
    Johnson/Top/H0/Tw/K2C/TiedFormR.lean) asks: no accept at a marked state. The kind's own decision
    does not look at the mark; the door's way out does.

What is said. `unmarked_of_seat`: under `left_of_seat`'s premises (Doors.lean) and "whatever the way
    out hands on bears no mark": where the seated piece accepts, the state IN FRONT bears no mark:
    the accept leaves the mark as it is (the field failed of `Left`), and behind there is none.

Limits. That the description's five doors end without a mark is said in
    Johnson/P1K2R/SitsNoMark.lean. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Ties.Doors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.First.K2Caller (SeatStep seatedAt seated_out)
open _root_.Run (ckP)

/-- **No accept at a marked state.** -/
theorem unmarked_of_seat {F : Frame} {Cl Cl' W W' : Type} (q : Piece (ckP .two) F S Cl' W) (p : P2)
    (hq : q.b = below (K2.codeSwitchKind p)) (hback : q.back = []) (B : Block S Cl) (enter : S → Except String
                S) (leave : S → S → Except String S) (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl') p).rounds) (h :
                            SeatStep B (K2.codeSwitchKind (Cl := Cl') p) enter leave) (hin : ∀ s t, enter s = .ok t → Left s t) (hout :
                                        ∀ s t s', leave s t = .ok s' → Left t s') (hend : ∀ s t s', leave s t = .ok s' → s'.failed =
                                        none) (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) q.ds) → W' → W') :
    ∀ a τ b, (seatedAt q B ext).ior.red.out a τ = some b → a.1.failed = none := by
  intro a τ b ho
  obtain ⟨t, t', _, _, e3⟩ := seated_out q _ hq hback B enter leave hr h ext a b τ ho
  rw [← (left_of_seat q p hq hback B enter leave hr h hin hout ext a τ b ho).failed]
  exact hend _ _ _ e3

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.unmarked_of_seat
