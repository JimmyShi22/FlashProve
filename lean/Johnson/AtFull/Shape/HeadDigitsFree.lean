-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/HeadDigitsFree.lean: THE FIFTIETH LOOKUP (the one on the digits of the head's
link, member 345 of the first chain) IN THE FRAME's OWN FORM, WITH ITS PUBLIC PREMISES PAID:
`Carries` with no premise but the head; `Returns` under hv alone. Under the head `P5J.AtMgA`;
GENERAL IN THE THREE PUBLIC FILES (in the goals' scope); a joining of laws; nothing is evaluated.

What was left (LookFree.lean: `look_head_frame_face`), and who pays.
* hN, the head's plan counts one claim on the weights: the routine lays the literal
  (`LT28.K11Tests.public_H_ncl`, Johnson/Desc/Sound/K11Tests/NclHeadInScope.lean).
* hL, `layoutOk` (the lookups' Honest/K3/Law/Thread/ClaimSizes.lean), three clauses. That the head's
  layout has a call with the segment "HD0": `callNo_in_scope`
  (Johnson/Goal/Meaning/HeadCallsScope.lean) and `callNo`'s own text. That the last unit of the
  layout of the committed matrix is of kind 13, with just the two groups "x" and "kk": that layout
  is what `wsLayOf` returns (`Lk6.AtPlan.publicOf_wsLay`), its units are those of the written list
  of asks (`wsLayOf_units`, `allAsks`, Johnson/Road/FormsKeysWLay.lean), whose last is the head's.

Main names.
* `unitsFrom_append`: the units for two lists of asks, one behind the other.
* `ncl_at`, `layoutOk_at`: under the head the two tests accept.
* `look_head_frame_vals`: at EVERY site s in `lookSites Zp` at link 24 on the digits: a member
  stands at 345; and for every ft, g and vals with g 345 = `liftQ (headDigitsG s.shape s.p.first
  Zp.p.X)`: `Carries` at 345; and `Returns` at 345 under hv.

WHAT STAYS. hv: THE LETTER vals AT 345 GIVES `headVals` (ClaimReturns.lean): A TEST ON WHAT THE HEAD
HEARD, NOT ON ITS SHAPE: whoever lays vals lays it so.

Limits. Of the step `headDigitsG` and its two laws the Limits of their own file stand
(Honest/K3/Law/Thread/CarriesHeadDigits.lean). The site's shape and first slot are a letter's. g and
vals are letters: no table of steps is laid here. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LookFree
import Johnson.Desc.Sound.K11Tests.NclHeadInScope
import Johnson.Goal.Meaning.HeadCallsScope
import Johnson.Goal.PlanValues.ScopeAtPlan
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open OnBytes.Road (unitsFrom endFrom unitP allAsks wsLayOf_units AskW placeP)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Carries Returns)
open ProofFile.Honest.K3 (Site lookSites)
open ProofFile.Honest.K3.Law.AtThr (headDigitsG layoutOk headVals)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The units for two lists of asks, one behind the other. -/
theorem unitsFrom_append (lk : Nat) : ∀ (as bs : List AskW) (o : Nat),
    unitsFrom lk o (as ++ bs) = unitsFrom lk o as ++ unitsFrom lk (endFrom lk o as) bs
  | [], _, _ => rfl
  | a :: as, bs, o => by
    show unitP lk o a :: unitsFrom lk _ (as ++ bs) = unitP lk o a :: (unitsFrom lk _ as ++ _)
    rw [unitsFrom_append lk as bs]
    rfl

/-- Under the head the head's plan counts one claim on the weights. -/
theorem ncl_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : (Zp.p.X.H.NCL == 1) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := LT28.K11Tests.public_H_ncl O.public
  rw [O.W] at e
  rw [e]
  rfl

/-- **Under the head the public points at which the claim's routine can refuse are in order.** -/
theorem layoutOk_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    layoutOk Zp.p.X.HLy Zp.p.X.layers.wsLay = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  obtain ⟨-, hc⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.callNo_in_scope h.scope h.reads hX
  obtain ⟨y, -, hw⟩ := Lk6.AtPlan.publicOf_wsLay hX
  obtain ⟨-, hU, -⟩ := wsLayOf_units hw
  rw [O.W] at hc hU
  -- the first clause
  have c1 : ((Head.callNo Zp.p.X.HLy "HD0").any fun q =>
      ((Zp.p.X.HLy.calls.getD q default).seg? "HD0").isSome) = true := by
    rw [hc]
    unfold Head.callNo at hc
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hc
    show ((Zp.p.X.HLy.calls.getD 0 default).seg? "HD0").isSome = true
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    exact hp
  -- the last unit
  unfold allAsks at hU
  rw [unitsFrom_append] at hU
  generalize hpre : unitsFrom _ 0 ((List.range _).flatMap _) = pre at hU
  generalize endFrom _ 0 ((List.range _).flatMap _) = o at hU
  obtain ⟨u12, u13, hu, hX13, gx, gk, hg, hx, hk⟩ : ∃ u12 u13 : WsUnit,
      Zp.p.X.layers.wsLay.U.toList = pre ++ [u12, u13] ∧ u13.X = 13 ∧
        ∃ gx gk, u13.g = [gx, gk] ∧ gx.name = "x" ∧ gk.name = "kk" :=
    ⟨_, _, hU, rfl, _, _, rfl, rfl, rfl⟩
  have hA : Zp.p.X.layers.wsLay.U = (pre ++ [u12, u13]).toArray := by
    rw [← hu, Array.toArray_toList]
  have b1 : ((pre ++ [u12, u13]).toArray.back?.map (·.X)) = some 13 := by
    simp [hX13]
  have b2 : (pre ++ [u12, u13]).toArray.getD ((pre ++ [u12, u13]).toArray.size - 1) default =
      u13 := by
    simp
  unfold layoutOk
  rw [c1, hA, b1, b2, hg]
  show (true && some 13 == some 13 && (gx.name == "x" && gk.name == "kk")) = true
  rw [hx, hk]
  rfl

/-- **THE FIFTIETH LOOKUP, ITS PUBLIC PREMISES PAID.** -/
theorem look_head_frame_vals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link = 24) (hd : s.digits = true) :
    (cF.blocksInOrder[345]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g 345 = liftQ (headDigitsG s.shape s.p.first Zp.p.X) →
        Carries cF.blocksInOrder ft (firstZA g vals) 345 ∧
        ((∀ st rs cols, vals 345 st rs cols = true → headVals Zp.p.X st = true) →
          Returns cF.blocksInOrder ft (firstZA g vals) 345) := by
  obtain ⟨k, F⟩ := look_head_frame_face h s hs hl hd
  exact ⟨k, fun ft g vals hg =>
    ⟨(F ft g vals hg).1 (layoutOk_at h), (F ft g vals hg).2 (ncl_at h)⟩⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.unitsFrom_append
#print axioms Johnson.AtFull.Shape.ncl_at
#print axioms Johnson.AtFull.Shape.layoutOk_at
#print axioms Johnson.AtFull.Shape.look_head_frame_vals
