-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsRounds.lean: the lookup on the digits of a link's smallness test:
THE END THEOREM WITH ONE PREMISE ON THE WRITTEN ROUNDS, its errors as a number, and its instance at
a link of a public record. Statements and proofs. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Why. k3_digits_goodIn (K3DigitsAt.lean) asks three things of the piece's written rounds. dig_rounds
(K3DigRounds.lean) gives the three from one: each written round is the declared one (SameAs).

Main names.
  k3_digits_goodIn_same: the end theorem with that one premise in the place of the three.
  k3_digits_err: the end theorem's errors as a number: Err.Below p.err 2^-157, under its own
    premises.
  k3_digits_goodIn_at: THE INSTANCE: at link i of a public record X: the place and the plan's record
    are digAt X i's, and DigOK is the one Bool digB's yes.
Limits. That a piece's written rounds are the cut of the file's written rounds at the block's offset
is a premise of the rule on a file, with a cut of lists: not here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsAt
import Johnson.Desc.First.Look.K3DigRounds

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

local notation "𝐫" => noRider (digCaller x tl D rad extNone Unit)

/-- **The end theorem, with one premise on the written rounds.** -/
theorem k3_digits_goodIn_same (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : DigOK set x tl D rad pp)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (digSg x D rad).Smp) :
    p.GoodIn
      (DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link))
      (DigOn' G x tl D rad seatT smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D x.link))
      (DigFront G x tl D rad seatT arr smp)
      (DigBehind G x tl D rad seatT arr smp (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) :=
  k3_digits_goodIn G seatT arr smp claim piece laid before guests p hb hback hext H
    (dig_rounds H p.ds hR).1 (dig_rounds H p.ds hR).2.1 (dig_rounds H p.ds hR).2.2 hε hsmp hseat σ₀

/-- **The end theorem's errors, as a number**: under the end theorem's own premises on the piece's
rounds and errors each written round's error is at most 2^-157 of that round's challenge values. -/
theorem k3_digits_err (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (H : DigOK set x tl D rad pp)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err) :
    Iop.Err.Below p.err ((2 : ENNReal)⁻¹ ^ 157) :=
  dig_written extNone Unit H p.ds (dig_rounds H p.ds hR).1 (dig_rounds H p.ds hR).2.2 p.err hε

/-- **THE INSTANCE: at link i of a public record X**: the place and the plan's record are digAt's,
and the five tests are the one Bool. -/
theorem k3_digits_goodIn_at {X : Verify.Public} {i : ℕ} {x₀ : Desc.First.Look.Place}
    {tl₀ : HTailF2} {D₀ : Desc.First.Look.Sent} {rad₀ : OracleShape → ℕ} {pp₀ : ℕ}
    (hx : digAt X i = some (x₀, tl₀))
    (hB : digB (Params.settingOf X.P.frame) x₀ tl₀ D₀ rad₀ pp₀ = true)
    (seatT₀ : Fin (digList x₀ D₀ rad₀).length → ℕ × ℕ) (arr₀ : ℕ → ℕ → ℕ)
    (smp₀ : Desc.First.S → (i : Fin (digList x₀ D₀ rad₀).length) →
      Option ((digSg x₀ D₀ rad₀).om i).Smp)
    (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x₀) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hR : List.Forall₂ SameAs p.ds
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x₀).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [noRider (digCaller x₀ tl₀ D₀ rad₀ extNone Unit)]).ε
      (noRider (digCaller x₀ tl₀ D₀ rad₀ extNone Unit))) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x₀) guests).decide s rs cols =
        .ok s' → smp₀ s' = smp₀ s)
    (hseat : ∀ i, (seatT₀ i).1 < p.base) (σ₀ : (digSg x₀ D₀ rad₀).Smp) :
    p.GoodIn
      (DigOn G x₀ D₀ rad₀ seatT₀ smp₀ (Desc.K3.seatDigits claim).fork (OwnIs D₀ x₀.link))
      (DigOn' G x₀ tl₀ D₀ rad₀ seatT₀ smp₀ (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard (OwnIs D₀ x₀.link))
      (DigFront G x₀ tl₀ D₀ rad₀ seatT₀ arr₀ smp₀)
      (DigBehind G x₀ tl₀ D₀ rad₀ seatT₀ arr₀ smp₀ (Desc.K3.seatDigits claim).fork
        (Desc.K3.seatDigits claim).heard) :=
  k3_digits_goodIn_same G seatT₀ arr₀ smp₀ claim piece laid before guests p hb hback hext
    (digOK_at hx hB) hR hε hsmp hseat σ₀

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_goodIn_same
#print axioms VerifiableInference.OnPublicFiles.k3_digits_err
#print axioms VerifiableInference.OnPublicFiles.k3_digits_goodIn_at
