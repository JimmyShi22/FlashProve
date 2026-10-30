-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/DrawMade.lean: THE ONE TIE OF THE PLAN's NUMBERS THAT `call_draws`
(Returns/DrawTies.lean) STILL ASKS, p.seeds = seeds * (coordinates + 1), HOLDS WHERE THE PLAN's TWO
COUNTS FOLLOW THE RULE BY WHICH THE LIBRARY MAKES THEM (`numsAt`,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean; `p2Of`, Johnson/Top/H0/K2Caller/P2At.lean): nonZero :=
samples; seeds := samples * (the greatest cube among the sampled announced messages + 1). Statements
and proofs.

  `fold_cube`, `coordinates_cube` the sending letter's number of coordinates is the greatest cube
                    among its own sampled announced messages: message by message by the library's
                    `cube_bits` (Johnson/Desc/K1/Law/FormEq.lean); the list under the library's name
                    `sampledOf` (Johnson/Top/H0/K2Caller/NumsAt.lean)
  `tie_of_rule` the rule's two equations and the first entry's test on the plan give the tie
  `call_draws_made` SO, AT A FRONT: rounds that fit the kind's rounds, the entry's test and the
                    rule's two equations give the five ends of `call_draws`

Limits. THE RULE's TWO EQUATIONS ARE PREMISES, AND THEY ARE ASKED AT WHAT THE SWITCH ANNOUNCES AT
THE FRONT AND AT THE FRONT's CODES: that a made plan's list of announced messages and its codes ARE
these is a further tie of the plan to the state, not shown here: the library has a name for it
(`Fence`, Johnson/Top/H0/Tw/K2C/SendsOn.lean), and for the list a statement at a frame with the
plan's shape and groups (`notices_sent`, Johnson/Top/H0/K2Hands/NoticesSent.lean): neither is
called. The library asks the rule's two equations as premises in this very form, AT THE PLAN's OWN
LIST AND CODES, not at the front's (`p2At_frame`, Johnson/Top/H0/K2Caller/NumsAt.lean). It has the
sentence of `coordinates_cube` at other letters (`coordinates_bMax`,
Johnson/Desc/K1/Law/LitPow.lean): not called. That a lot's numbers are made by the rule is by
unfolding the lot's own text, not here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.DrawTies
import Johnson.Desc.K1.Law.FormEq
import Johnson.Top.H0.K2Caller.NumsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Params (cubeBitsOf)
open VerifiableInference.Desc (roundsFit)
open VerifiableInference.Desc.First.K2 (P2 rounds par9)
open VerifiableInference.Desc.First.K2Caller (sampledOf)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Tw.K2 (Front switchNotices)

theorem fold_cube (codes : Codes) : ∀ (l : List OracleNotice) (a : Nat),
    ((l.map (·.shape)).filter (·.answers != 0)).foldl (fun b s => max b (K1.Msg.of codes s).v) a =
      (sampledOf l).foldl (fun c n => max c (cubeBitsOf codes n.shape)) a
  | [], _ => rfl
  | n :: l, a => by
    by_cases h : n.shape.answers = 0
    · have hf : ((n :: l).map (·.shape)).filter (·.answers != 0) =
          (l.map (·.shape)).filter (·.answers != 0) := by
        rw [List.map_cons, List.filter_cons_of_neg (by simp [h])]
      have hg : sampledOf (n :: l) = sampledOf l := by
        unfold sampledOf
        rw [List.filter_cons_of_neg (by simp [h])]
      rw [hf, hg]
      exact fold_cube codes l a
    · have hf : ((n :: l).map (·.shape)).filter (·.answers != 0) =
          n.shape :: (l.map (·.shape)).filter (·.answers != 0) := by
        rw [List.map_cons, List.filter_cons_of_pos (by simp [h])]
      have hg : sampledOf (n :: l) = n :: sampledOf l := by
        unfold sampledOf
        rw [List.filter_cons_of_pos (by simp [Nat.pos_iff_ne_zero, h])]
      have hc : cubeBitsOf codes n.shape = (K1.Msg.of codes n.shape).v := K1.cube_bits codes n.shape
      rw [hf, hg, List.foldl_cons, List.foldl_cons, hc]
      exact fold_cube codes l _

theorem coordinates_cube (Z : K1.Par) :
    Z.coordinates =
      (sampledOf Z.sent.toList).foldl (fun c n => max c (cubeBitsOf Z.codes n.shape)) 0 := by
  unfold K1.Par.coordinates K1.Par.tuple
  exact fold_cube Z.codes Z.sent.toList 0

/-- **The rule's two equations and the entry's test give the tie.** -/
theorem tie_of_rule (p : P2) (Z : K1.Par) (samples : Nat)
    (hN : p.nonZero = samples)
    (hS : p.seeds = samples *
      ((sampledOf Z.sent.toList).foldl (fun c n => max c (cubeBitsOf Z.codes n.shape)) 0 + 1))
    (he : planOk1 none Z.sent (par9 p).eSeed = true) :
    p.seeds = Z.seeds * (Z.coordinates + 1) := by
  rw [hS, ← coordinates_cube, ← hN, nonZero_of_entry p Z Z.sent rfl he]

/-- **At a front: rounds that fit, the entry's test and the rule's two equations give what the law
asks of the draws.** -/
theorem call_draws_made (p : P2) (x : Front) (r₁ r₂ : Fmt.RoundView) (samples : Nat)
    (hN : p.nonZero = samples)
    (hS : p.seeds = samples * ((sampledOf (switchNotices x.T x.others).toList).foldl
      (fun c n => max c (cubeBitsOf x.st.codes n.shape)) 0 + 1))
    (he : planOk1 none (switchNotices x.T x.others) (par9 p).eSeed = true)
    (h : roundsFit (rounds p) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length =
        (sendingAt p x).seeds * ((sendingAt p x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ z ∈ K1.seedsOf (sendingAt p x) r₁, isZeroE z.2 = false :=
  call_draws p x r₁ r₂
    (tie_of_rule p (sendingAt p x) samples hN (by rw [sendingAt_sent]; exact hS)
      (by rw [sendingAt_sent]; exact he)) he h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.fold_cube
#print axioms VerifiableInference.Desc.K2.Honest.Returns.coordinates_cube
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tie_of_rule
#print axioms VerifiableInference.Desc.K2.Honest.Returns.call_draws_made
