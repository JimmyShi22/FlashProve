-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AttVia.lean: THE CALLS' END THEOREM AT AN ATTENTION LINK AT THE LOOKUP's
BLOCK WITH THE HEARING EXCHANGED (K3.Law.blockVia, Johnson/Desc/First/Look/Via/Via.lean). One
theorem, a corollary of k3_att_goodIn_any (Johnson/Desc/First/Look/K3AttRounds.lean). NO SOUNDNESS
OF THE PROTOCOL IS CLAIMED.

How it goes. Where blockVia's own test on the plan says yes, its decide says .ok s' only where
K3.block's decide says .ok s' (blockVia_decide, Johnson/Top/H/K3Via/Blocks.lean).

Main name.
  k3_att_goodIn_via: at a piece p with p.b = below (K3.Law.blockVia (seatCalls claim) piece laid
    before (P.ofPlace set false x) guests): p.GoodIn AttOn AttOn' AttFront AttBehind, under the
    premises of k3_att_goodIn_same and ONE PUBLIC PREMISE MORE: blockVia's planOk says yes. The
    premise on the samples is asked at blockVia's own yes alone.
Limits. Those of K3AttGoodIn.lean, K3AttAt.lean, K3AttRounds.lean. One way: nothing is said on where
blockVia says yes. THAT THE PLANES' CELLS LIE IN THE LIST's MATRIX (planesAtB,
Johnson/Desc/First/Look/K3CallerCellsIn.lean) IS ASKED BY NO PREMISE HERE: it stands beside AttOK's
four tests; at a record that publicOf returns it is had by planesAtB_att
(Johnson/Desc/First/Look/K3CallerCellsLaw.lean), spent in Johnson/Desc/First/Look/K3AttPublic.lean.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AttRounds
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

local notation "𝐫" => attRider x A tl D rad extNone Unit

/-- **THE END THEOREM AT THE BLOCK WITH THE HEARING EXCHANGED.** -/
theorem k3_att_goodIn_via (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).planOk = true)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : AttOK set x A tl D rad)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_att_goodIn_any G seatT arr smp claim piece laid before guests _
    (fun _ _ _ _ h => Desc.K3.Law.blockVia_decide hplan h) p hb hback hext H hr hR hε hsmp hseat σ₀

end

#print axioms k3_att_goodIn_via

end VerifiableInference.OnPublicFiles
