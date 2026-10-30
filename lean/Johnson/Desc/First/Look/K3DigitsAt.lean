-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsAt.lean: the lookup on the digits of a link's smallness test: THE
END THEOREM AT K3.block's OWN TEXT: k3_digits_goodIn_of (K3DigitsGoodIn.lean) with its letters for
the kind's decide and the record's two readers set to K3.block's own at seatDigits, over the record
that the proof's first file carries (Johnson/Desc/First/State.lean), and Own set to «the record's
own codes, shape, layout, link number and arrayOf are D's» (OwnIs, K3CallerOwn.lean). Small lemmas
and one theorem. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Main names.
  (decide_first, Johnson/Top/H/K3DecideMore.lean: K3.block's decide says yes only where the ledger
    stands at the place's first slot.)
  ownOf_put: what seatDigits lays behind a hearing turns none of the record's own five.
  k3_digits_goodIn: at a piece p that holds «below (K3.block (seatDigits claim) …)» at the digits'
    place of a link, with no round behind its own and the identity as its extractor: Piece.GoodIn
    between DigOn, DigOn', DigFront, DigBehind.
  PAID HERE, beyond K3DigitsGoodIn.lean: PieceHears (piece_hears_below) · K3DecideHears
    (k3DecideHears_digits) · hOwn · hnext.
  LEFT AS PREMISES: DigOK (tests on public data; digOK_at gives it from one Bool) · the written
    rounds hold elements alone, hold no answers, and have the entries of the block's declared rounds
    · the piece's errors are bearT's · decide's yes does not turn smp · every tree of seatT is
    sent in front of the stretch · σ₀.
Limits. Those of K3DigitsGoodIn.lean. «below b» is a device of the rule's proof: b behind the test
that every word is below the prime; FoldBelow (Johnson/Desc/Sound/ChainRule.lean) ties the fold of
such blocks to the fold with that test in front.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.Look.K3CallerOwn
import Johnson.Top.H.K3PieceHears
import Johnson.Top.H.K3DecideMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- What the digits' seat lays behind a hearing turns none of the record's own five. -/
theorem ownOf_put {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard) (Gk : Fork) :
    ownOf ((Desc.K3.seatDigits claim).put s g Gk) = ownOf s := by
  simp only [Desc.K3.seatDigits]
  cases hh : s.here with
  | between => simp [ownOf, Desc.First.S.tl?, Desc.First.S.link?, Desc.K3.mark_here, hh]
  | fin _ => simp [ownOf, Desc.First.S.tl?, Desc.First.S.link?, Desc.K3.mark_here, hh]
  | mem _ => simp [ownOf, Desc.First.S.tl?, Desc.First.S.link?, Desc.K3.mark_here, hh]
  | lay a =>
    simp [ownOf, Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
      Desc.First.S.link?, Desc.First.S.live, hh]
  | att a =>
    simp [ownOf, Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
      Desc.First.S.link?, Desc.First.S.live, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [ownOf, Desc.First.S.tl?, Desc.First.S.link?, Desc.K3.mark_here, hh, ho]
    | true =>
      simp [ownOf, Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl,
        Desc.First.S.putFork, Desc.First.S.link?, Desc.First.S.live, hh, ho]

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)

local notation "𝐫" => noRider (digCaller x tl D rad extNone Unit)

/-- **THE END THEOREM OF THE DIGITS' CHAIN, at K3.block's own text.** -/
theorem k3_digits_goodIn {set : Params.Setting} {pp : ℕ} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : DigOK set x tl D rad pp)
    (hd : ∀ d ∈ p.ds, Fo.Peel.Plain (toRD d)) (hA : ∀ d ∈ p.ds, NoAns d.items)
    (he : p.ds.map (·.entry) = (Desc.First.Look.P.ofPlace set true x).rounds.map (·.entry))
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
  k3_digits_goodIn_of G seatT arr smp _ _ _ p H
    (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before
      (Desc.First.Look.P.ofPlace set true x) guests).decide
    hext hd hA he hε (fun a τ a' h => piece_hears_below p _ hb hback a τ a' h)
    (k3DecideHears_digits claim piece laid before _ guests)
    hsmp
    (fun s rs cols s' h hO => by
      obtain ⟨F, y, -, -, -, rfl⟩ := decide_ok _ piece laid before _ guests s s' rs cols h
      exact (ownOf_put claim s y.1 y.2).trans hO)
    (fun s rs cols s' Fk h hF => decide_first _ piece laid before _ guests s s' rs cols Fk hF h)
    hseat σ₀

end

#print axioms ownOf_put
#print axioms k3_digits_goodIn

end VerifiableInference.OnPublicFiles
