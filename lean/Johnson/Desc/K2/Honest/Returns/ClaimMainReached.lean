-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ClaimMainReached.lean: `TablesFit.claimMain` (Returns/BehindAt.lean):
THE CARRIED CLAIM's FORM FITS THE OLD MAIN CODE's PLACE BITS: AT A STATE THAT IS REACHED IN FRONT OF
A SWITCH, AT ALL THREE SORTS OF PLACE, IN THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC PART. It is
the second of the law's two clauses that compare field elements with (1, 1); the first, `claimKept`:
Returns/MembersReached.lean. It holds whoever plays: every closing that says yes has asked that the
batched row's form fits (the first clause of `Own.FoldRowFit`), and lays that form with its lowest
variables fixed at the fold's challenges. Statements with their proofs: calls.

  `closeFrame_claim` a yes of the frame's closing: the carried claim's form is a row's form, fixed
                    at as many challenges as the layout has row variables; the row passed the test
                    on rows at the closing's own statement
  `claimMain_of_close` `claimMain` for what a closing returns, at every statement grown out of its
                    own: no state of the walk
  `link_claimMain_reached`, `head_claimMain_reached`, `fin_claimMain_reached` at `frontAt s L Q`,
                    `headFrontOf s a T`, `finFrontOf t a Q`, in the structure's own letters

By: `formFits_fixLow` (Returns/FixLowFits.lean) · the bridge: `link_closed_reached`
(Returns/ClosedReached.lean), `head_closed_reached`, `fin_closed_reached` (Returns/ClosedArms.lean)
· `layFits_of_close` (Returns/ClosedReached.lean) · the library's `closeFrame_iff`
(Johnson/Desc/First/Close/Law/CloseMeans.lean), `foldRowFits_iff` (Johnson/Desc/Own/FoldMean.lean).
A near relative, not called: the library's `out_vars`
(Johnson/Desc/First/Close/Law/CarriedRows.lean): the number of variables alone, by
`Form.fixLow_shape`.

Limits. At the arms `here` is a premise, and the quiet front's yes at the place behind the last
segment. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN
MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.ClosedArms
import Johnson.Desc.K2.Honest.Returns.FixLowFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (finishFrontQ headFrontOf finFrontOf)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_iff)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

theorem closeFrame_claim {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) :
    ∃ (F : FoldShape) (row : GroupRow) (gamma : List E) (eps : E), Own.FoldRowFit x.2 F row ∧
      x.1.rows.c = row.c.fixLow gamma eps ∧ gamma.length = F.layout.k ∧
      x.1.rows.code = F.code := by
  have hch := (layFits_of_close h (Grows.refl x.2)).challenges
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (closeFrame_iff owed f S₀ es rs x.1 x.2).1 h
  obtain ⟨eB, es', rB, rs', -, -, m, -, row, L, S₁, -, -, hF⟩ := hc
  obtain ⟨eE, eR, rE, rR, -, -, -, -, -, -, -, d2, -, sum, eps, -, hrow, gamma, claim, -, hout,
    hS'⟩ := hF
  have hR := (Own.foldRowFits_iff _ _ _).1 hrow
  rw [← hS'] at hR
  rw [e] at hch
  have hch' : rows.gamma.length = rows.layout.k := hch
  rw [hout] at hch'
  refine ⟨_, row, gamma, eps, hR, ?_, hch', ?_⟩
  · rw [e]
    show rows.c = _
    rw [hout]
    rfl
  · rw [e]
    show rows.code = _
    rw [hout]
    rfl

/-- **`TablesFit.claimMain` for what a closing returns.** -/
theorem claimMain_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    Own.formFits x.1.rows.c (T.codes.base.getD x.1.rows.code default).logEll = true := by
  obtain ⟨F, row, gamma, eps, R, ec, el, ecode⟩ := closeFrame_claim h
  have H := formFits_fixLow R.1 gamma eps (by omega)
  rw [el, Nat.add_sub_cancel_left] at H
  rw [ec, hg.1, ecode]
  exact H

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

theorem link_claimMain_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) :
    Own.formFits (frontAt s L Q).f.rows.c
      ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logEll = true := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  show Own.formFits s.check.frame.rows.c
    (s.st.codes.base.getD s.check.frame.rows.code default).logEll = true
  rw [hf]
  exact claimMain_of_close hx hg

theorem head_claimMain_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget) :
    Own.formFits (headFrontOf s a T).f.rows.c
      ((headFrontOf s a T).st.codes.base.getD (headFrontOf s a T).f.rows.code default).logEll =
      true := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  show Own.formFits a.fr.rows.c (s.st.codes.base.getD a.fr.rows.code default).logEll = true
  rw [hf]
  exact claimMain_of_close hx hg

theorem fin_claimMain_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) :
    Own.formFits (finFrontOf t a Q).f.rows.c
      ((finFrontOf t a Q).st.codes.base.getD (finFrontOf t a Q).f.rows.code default).logEll =
      true := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
  show Own.formFits a.fr.rows.c (t.st.codes.base.getD a.fr.rows.code default).logEll = true
  rw [hf]
  exact claimMain_of_close hx hg

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.closeFrame_claim
#print axioms VerifiableInference.Desc.K2.Honest.Returns.claimMain_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_claimMain_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_claimMain_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_claimMain_reached
