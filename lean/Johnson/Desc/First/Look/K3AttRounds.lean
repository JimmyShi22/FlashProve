-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AttRounds.lean: THE CALLS' END THEOREM AT AN ATTENTION LINK WITH ONE
PREMISE ON THE WRITTEN ROUNDS, AND ITS ERRORS AS A NUMBER. After the pattern of
Johnson/Desc/First/Look/K3DigitsRounds.lean, whose general half (SameAs, same_all, same_entries,
entPlain_forEnts) is spent as it lies. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Main names:
  `att_rounds`: if each written round is the declared one (SameAs: the same entry, the kind of its
    name, the same items), then the three premises of k3_att_goodIn on the written rounds hold:
    elements alone; no answers; the entries are the declared rounds'.
  `k3_att_goodIn_any`: THE END THEOREM AT ANY BLOCK b WHOSE decide SAYS YES ONLY WHERE K3.block's
    DOES: at a piece that holds "below b". All premises on decide's yes are asked at b's yes alone.
  `k3_att_goodIn_same`: at b := K3.block itself.
  `k3_att_err`: under the same premises on the rounds and the errors each written round's error is
    at most 2^-157 of that round's challenge values. The rider adds nothing.

Limits. Those of K3AttGoodIn.lean and K3AttAt.lean. hr (the planner makes the place's entries) stays
a premise on public data.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AttAt
import Johnson.Desc.First.Look.K3DigitsRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {set : Params.Setting}

/-- The entries of the place's declared rounds are the library's list. -/
theorem att_entries (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true) :
    (Desc.First.Look.P.ofPlace set false x).rounds.map (·.entry) =
      Cb.Fo.forEnts ((Desc.First.Look.P.ofPlace set false x).set.workOf .field .request) x.fs :=
  entries_forEnts H.shape (att_foOk H)
    (by
      rw [H.four]
      decide) hr

/-- **The three premises on the written rounds, from one.** -/
theorem att_rounds (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true) (ds : List RDT)
    (hR : List.Forall₂ SameAs ds (Desc.First.Look.P.ofPlace set false x).rounds) :
    (∀ d ∈ ds, Plain (toRD d)) ∧ (∀ d ∈ ds, NoAns d.items) ∧
      ds.map (·.entry) = (Desc.First.Look.P.ofPlace set false x).rounds.map (·.entry) := by
  have hE := att_entries H hr
  have hok : ∀ r ∈ (Desc.First.Look.P.ofPlace set false x).rounds, EntPlain r.entry := fun r hr' =>
    entPlain_forEnts _ _ _ (by
      rw [← hE]
      exact List.mem_map.2 ⟨r, hr', rfl⟩)
  exact ⟨same_all hR hok, fun d hd => (same_all hR hok d hd).noAns, same_entries hR⟩

variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

local notation "𝐫" => attRider x A tl D rad extNone Unit

/-- **THE END THEOREM AT ANY BLOCK WHOSE decide SAYS YES ONLY WHERE K3.block's DOES.** -/
theorem k3_att_goodIn_any (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_att_goodIn_of G seatT arr smp _ _ _ p H b.decide
    hext hr (att_rounds H hr p.ds hR).1 (att_rounds H hr p.ds hR).2.1 (att_rounds H hr p.ds hR).2.2
    hε (fun a τ a' h => piece_hears_below p _ hb hback a τ a' h)
    (fun K _ ρ lm s s' rs cols hw h =>
      k3DecideHears_calls claim piece laid before _ guests K ρ lm s s' rs cols hw
        (hyes s rs cols s' h))
    hsmp
    (fun s rs cols s' h hO => by
      obtain ⟨F, y, -, hn, -, rfl⟩ :=
        decide_ok _ piece laid before _ guests s s' rs cols (hyes s rs cols s' h)
      exact (ownOf_putCalls claim s y.1 y.2 hn).trans hO)
    (fun s rs cols s' Fk h hF =>
      decide_first _ piece laid before _ guests s s' rs cols Fk hF (hyes s rs cols s' h))
    hseat σ₀

/-- **The end theorem at K3.block's own text, with one premise on the written rounds.** -/
theorem k3_att_goodIn_same (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
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
  k3_att_goodIn_any G seatT arr smp claim piece laid before guests _ (fun _ _ _ _ h => h) p hb
    hback hext H hr hR hε hsmp hseat σ₀

/-- **The end theorem's errors, as a number.** -/
theorem k3_att_err (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err) :
    Iop.Err.Below p.err ((2 : ENNReal)⁻¹ ^ 157) :=
  lookupC_written (callersCR [𝐫]) (att_ok extNone Unit H) (attCaller x A tl D rad extNone Unit)
    (List.mem_singleton.2 rfl) _ p.ds (att_rounds H hr p.ds hR).1
    ((att_rounds H hr p.ds hR).2.2.trans (att_entries H hr)) p.err hε

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.att_rounds
#print axioms VerifiableInference.OnPublicFiles.k3_att_goodIn_any
#print axioms VerifiableInference.OnPublicFiles.k3_att_goodIn_same
#print axioms VerifiableInference.OnPublicFiles.k3_att_err
