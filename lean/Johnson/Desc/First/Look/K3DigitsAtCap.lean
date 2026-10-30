-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsAtCap.lean: the lookup on the digits of a link's smallness test: THE
END THEOREM AT A PIECE WHOSE ERRORS ARE THE CAP (Err.cap 128, Iop/ErrCap.lean): the errors that the
pieces of a file's real rows carry. One theorem. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Why. k3_digits_goodIn_same (K3DigitsRounds.lean) asks that the piece's errors be the least that bear
the proved block's (bearT). k3_rounds_at_digits (K3RoundsAt.lean) shows that these exist and lie
below the cap, round by round. What a piece owes at its errors it owes at all greater errors
(goodIn_atCap, Johnson/Desc/Sound/GoodInErr.lean).

Main name.
  k3_digits_goodIn_atCap: k3_digits_goodIn_same with «p.err = Err.cap 128 (uLT (ckP .two) p.ds)» IN
    THE PLACE OF the premise on bearT.
Limits. Those of K3DigitsRounds.lean and K3RoundsAt.lean. The cap is taken round by round: no sum
over the rounds is bounded here. At a round with fewer than 2 ^ 128 written challenge values the cap
is 0.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsRounds
import Johnson.Desc.First.Look.K3RoundsAt
import Johnson.Desc.Sound.GoodInErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- A piece whose errors are c is the piece with any errors laid and then c laid. -/
private theorem piece_back {S Cl W : Type} {C : Run.PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (ε c : Err (uLT C p.ds)) (h : p.err = c) :
    ({ ({ p with err := ε } : Piece C F S Cl W) with err := c } : Piece C F S Cl W) = p := by
  cases p
  subst h
  rfl

section
variable {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {set : Params.Setting} {pp : ℕ}

variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)

/-- **THE END THEOREM AT THE CAP.** -/
theorem k3_digits_goodIn_atCap (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : DigOK set x tl D rad pp)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (digSg x D rad).Smp) :
    p.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) := by
  obtain ⟨-, ε', e, -, -, hle⟩ := k3_rounds_at_digits H p.ds hR
  have g := k3_digits_goodIn_same G seatT arr smp claim piece laid before guests
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hb hback hext H hR e hsmp hseat σ₀
  have g2 := goodIn_atCap
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hle _ _ _ _ g
  rw [piece_back p ε' _ hcap] at g2
  exact g2

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_goodIn_atCap
