-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AttAt.lean: THE END THEOREM OF THE CALLS' CHAIN AT AN ATTENTION LINK, AT
K3.block's OWN TEXT: k3_att_goodIn_of (Johnson/Desc/First/Look/K3AttGoodIn.lean) with its letters
decide, fork, heard and Own set to the kind's block at the seat on a link's calls
(Johnson/Desc/First/Look/K3Seat.lean: seatCalls) and to "the record's own five are D's". After the
pattern of Johnson/Desc/First/Look/K3DigitsAt.lean. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Main names:
  `ownOf_putCalls`: what the calls' seat lays behind a hearing turns none of the record's own five,
    where nothing was heard in front.
  `k3_att_goodIn`: at a piece p of the rule of composition that holds "below (K3.block (seatCalls
    claim) piece laid before (P.ofPlace set false x) guests)": p.GoodIn AttOn AttOn' AttFront
    AttBehind.

THE RIDER IS IN THE CHAIN ON THE PROVED BLOCK's SIDE, AND NOWHERE ON THE TEXT's: "guests" is a
letter: the theorem holds at every list, and none of the four relations names it: the text's decide,
the library's rider. The block's test on the plan (planOk) does read the list.

What is paid inside: link 6 (piece_hears_below); (L2a) at the calls (k3DecideHears_calls); decide's
unfolding (decide_ok); the ledger stands at the place's first slot (decide_first).

Limits. Those of K3AttGoodIn.lean. The premises that are no theorems: hb, hback, hext, hε (choices
of whoever lays the piece); H (tests on public data); hr, hd, hA, he (the road from declared to
written rounds); hsmp, hseat (the samples' and the seats' readings).
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AttGoodIn
import Johnson.Desc.First.Look.K3DigitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- What the calls' seat lays behind a hearing turns none of the record's own five, where nothing
was heard in front (which a yes of decide says). -/
theorem ownOf_putCalls {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (Gk : Fork) (hn : (Desc.K3.seatCalls claim).heard s = none) :
    ownOf ((Desc.K3.seatCalls claim).put s g Gk) = ownOf s := by
  simp only [Desc.K3.seatCalls] at hn ⊢
  cases hh : s.here with
  | between =>
    simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
      Desc.First.S.live, Desc.K3.mark_here, hh]
  | fin _ =>
    simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
      Desc.First.S.live, Desc.K3.mark_here, hh]
  | mem _ =>
    simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
      Desc.First.S.live, Desc.K3.mark_here, hh]
  | lay a =>
    have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
    simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
      Desc.First.S.live, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
    simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
      Desc.First.S.live, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false =>
      simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
        Desc.First.S.live, Desc.K3.mark_here, hh, ho]
    | true =>
      have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh, ho] using hn
      simp [ownOf, Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?,
        Desc.First.S.live, hh, ho, hn']

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

local notation "𝐫" => attRider x A tl D rad extNone Unit

/-- **THE END THEOREM OF THE CALLS' CHAIN AT AN ATTENTION LINK, at K3.block's own text.** -/
theorem k3_att_goodIn {set : Params.Setting} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hd : ∀ d ∈ p.ds, Fo.Peel.Plain (toRD d)) (hA : ∀ d ∈ p.ds, NoAns d.items)
    (he : p.ds.map (·.entry) = (Desc.First.Look.P.ofPlace set false x).rounds.map (·.entry))
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_att_goodIn_of G seatT arr smp _ _ _ p H
    (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide
    hext hr hd hA he hε (fun a τ a' h => piece_hears_below p _ hb hback a τ a' h)
    (k3DecideHears_calls claim piece laid before _ guests)
    hsmp
    (fun s rs cols s' h hO => by
      obtain ⟨F, y, -, hn, -, rfl⟩ := decide_ok _ piece laid before _ guests s s' rs cols h
      exact (ownOf_putCalls claim s y.1 y.2 hn).trans hO)
    (fun s rs cols s' Fk h hF => decide_first _ piece laid before _ guests s s' rs cols Fk hF h)
    hseat σ₀

end

#print axioms ownOf_putCalls
#print axioms k3_att_goodIn

end VerifiableInference.OnPublicFiles
