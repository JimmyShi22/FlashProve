-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ExchangeOfFoot.lean: CONDITIONAL.

Not shown here. EVERY HYPOTHESIS OF `k4_own_share_of_foot` (Law/W/FootAtStand.lean: its head lists
the eleven and says what each rests on); no example is known of K4FootRest. K4Plan's FIELD sw BARS
EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES: at every other shape the statement says
nothing. AT A THREAD NONE OF WHOSE STEPS ACCEPTS THE CONCLUSION HOLDS EMPTILY. The import closure
holds what Law/W/FootAtStand.lean's and Law/SharesIs.lean's hold. Nothing on soundness, on
completeness or on any other property. No property is claimed.

The share of the debt `Exchange` at the member's own item in the form in which the threads ask it at
Thr with what is said (Honest/Thread/SharesS.lean): `ExchangeAtS T Said b iOwn`. It is one call of
`k4_own_share_of_foot`: so that statement and the threads' definition have stood in one environment.

  `k4_exchangeAtS_own_of_foot`   ExchangeAtS T Said b iOwn.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FootAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SharesIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated matsOfData)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
  {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
  {h : Layer.Shape} {pc : List (List String)} {D : Dim} {iOwn iPl iJo : T.ι} {rest : List T.ι}
  {names : Array (Nat × String)}

/-- **At Thr with what is said.** CONDITIONAL: as k4_own_share_of_foot at At := ThrS T Said b. -/
theorem k4_exchangeAtS_own_of_foot
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, ThrS T Said b k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, ThrS T Said b k s m E → K4LookTieAt look Q s m)
    (hCells : ∀ k s m E, ThrS T Said b k s m E →
      K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    (hM : ∀ t Dt, M t Dt = matsOfData tl names Dt)
    (hF : K4Front T (ThrS T Said b) b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4FootRest T (ThrS T Said b) b cells weights tokens look Q M own rdOf tl p h D) :
    ExchangeAtS T Said b iOwn :=
  (shareAt_said T Said b iOwn).1
    (k4_own_share_of_foot Tb (fun _ _ _ _ hT => hT.1) hSeat hSit hMask hLook hCells hM hF A
      hR)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_exchangeAtS_own_of_foot
