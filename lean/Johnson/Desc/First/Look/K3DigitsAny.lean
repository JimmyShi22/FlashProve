-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsAny.lean: the lookup on the digits of a link's smallness test: THE
END THEOREM AT ANY BLOCK WHOSE decide SAYS YES ONLY WHERE K3.block's DOES, at the least errors and
at the cap. Two theorems. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Why. What a description seats at the digits' place is not the bare K3.block: it bears a name, a
guard on the mark, or is another text with the same yes (K3.Law.blockVia). The end theorem reads of
the block its decide's yes alone.

Main names.
  k3_digits_goodIn_any: k3_digits_goodIn_same (K3DigitsRounds.lean) at p.b = below b, for every
    block b with: b.decide's yes gives the yes of K3.block at seatDigits (hyes).
  k3_digits_goodIn_anyCap: the same with «p.err = Err.cap 128 (uLT (ckP .two) p.ds)» in the place of
    the premise on bearT.
OBJECT. Desc.K3.block at Desc.K3.seatDigits (Johnson/Desc/First/Look/K3Lookup.lean, K3Seat.lean), through
hyes: K3.theOwn (Johnson/Desc/First/Look/K3Own.lean) lays it where digits = true.
USER. k3_digits_row_any (K3DigitsRow.lean); k3_digits_seated (K3DigitsSeated.lean).
LETTERS. b; claim, piece, laid, before, guests; G, seatT, arr, smp; the place x and tl, D, rad under
DigOK.
Limits. Those of K3DigitsRounds.lean, K3RoundsAt.lean and K3DigitsAtCap.lean. hyes is shown of no
block here. A block that never says yes meets hyes, and the GoodIn then holds idly.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsAtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {set : Params.Setting} {pp : ℕ}

variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)

local notation "theR" => noRider (digCaller x tl D rad extNone Unit)

/-- **THE END THEOREM AT ANY BLOCK WHOSE decide SAYS YES ONLY WHERE K3.block's DOES.** -/
theorem k3_digits_goodIn_any (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
        (Desc.First.Look.P.ofPlace set true x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : DigOK set x tl D rad pp)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (digSg x D rad).Smp) :
    p.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) :=
  k3_digits_goodIn_of G seatT arr smp _ _ _ p H b.decide
    hext (dig_rounds H p.ds hR).1 (dig_rounds H p.ds hR).2.1 (dig_rounds H p.ds hR).2.2 hε
    (fun a τ a' h => piece_hears_below p _ hb hback a τ a' h)
    (fun K _ ρ lm s s' rs cols hw h =>
      k3DecideHears_digits claim piece laid before _ guests K ρ lm s s' rs cols hw
        (hyes s rs cols s' h))
    hsmp
    (fun s rs cols s' h hO => by
      obtain ⟨F, y, -, -, -, rfl⟩ :=
        decide_ok _ piece laid before _ guests s s' rs cols (hyes s rs cols s' h)
      exact (ownOf_put claim s y.1 y.2).trans hO)
    (fun s rs cols s' Fk h hF =>
      decide_first _ piece laid before _ guests s s' rs cols Fk hF (hyes s rs cols s' h))
    hseat σ₀

/-- A piece whose errors are c is the piece with any errors laid and then c laid. -/
private theorem piece_back' {S Cl W : Type} {C : Run.PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (ε c : Err (uLT C p.ds)) (h : p.err = c) :
    ({ ({ p with err := ε } : Piece C F S Cl W) with err := c } : Piece C F S Cl W) = p := by
  cases p
  subst h
  rfl

/-- **The same at the cap.** -/
theorem k3_digits_goodIn_anyCap (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
        (Desc.First.Look.P.ofPlace set true x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : DigOK set x tl D rad pp)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (digSg x D rad).Smp) :
    p.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) := by
  obtain ⟨-, ε', e, -, -, hle⟩ := k3_rounds_at_digits H p.ds hR
  have g := k3_digits_goodIn_any G seatT arr smp claim piece laid before guests b hyes
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hb hback hext H hR e hsmp hseat σ₀
  have g2 := goodIn_atCap
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hle _ _ _ _ g
  rw [piece_back' p ε' _ hcap] at g2
  exact g2

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_goodIn_any
#print axioms VerifiableInference.OnPublicFiles.k3_digits_goodIn_anyCap
