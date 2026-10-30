-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LayVia.lean: THE CALLS' END THEOREM AT A LAYERS' LINK AT THE LOOKUP's
BLOCK WITH THE HEARING EXCHANGED (K3.Law.blockVia, Johnson/Desc/First/Look/Via/Via.lean). One
theorem, a corollary of k3_lay_goodIn_any (Johnson/Desc/First/Look/K3LayGoodIn.lean); the layers'
like of Johnson/Desc/First/Look/K3AttVia.lean. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

OBJECT: Desc.K3.Law.blockVia's decide, at the calls' seat (K3.theOwn lays blockVia:
  Johnson/Desc/First/Look/K3Own.lean).
Used by K3CallsStated.lean (Johnson/Desc/First/Look/).
LETTERS: seat := seatCalls claim; piece, laid, before, guests free; p := P.ofPlace set false x.
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

How it goes. Where blockVia's own test on the plan says yes, its decide says .ok s' only where
K3.block's decide says .ok s' (blockVia_decide, Johnson/Top/H/K3Via/Blocks.lean).

Limits. Those of K3LayGoodIn.lean. One way: nothing is said on where blockVia says yes. ONE PUBLIC
PREMISE MORE than k3_lay_goodIn_any: blockVia's planOk says yes.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {q : LayPub} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)

local notation "theR" => layRider x q tl D rad oW wOf nr nc extNone Unit

/-- **THE END THEOREM AT THE BLOCK WITH THE HEARING EXCHANGED, at a layers' link.** -/
theorem k3_lay_goodIn_via (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).planOk = true)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : LayOK set x)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW)
      (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) :=
  k3_lay_goodIn_any G seatT arr smp smpW strW msgW claim piece laid before guests _
    (fun _ _ _ _ h => Desc.K3.Law.blockVia_decide hplan h) p hb hback hext H hp hr hR hε hsmp
    hsmpW hstrW hseat σ₀ σW₀

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lay_goodIn_via
