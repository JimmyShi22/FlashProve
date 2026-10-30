-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/PlanMember.lean: THE MEMBER OF THE LAW "behind K4's hearing its two runs of
claims return" (Johnson/Road/K4/Total/Returns.lean), MADE BY CODE OFF THE PLAN: so that the law's
premise "there is a value of this skeleton at which the listing front returns" becomes ONE PUBLIC
TEST WITH CODE. Statements and proofs; the definitions: Johnson/Road/K4/Total/PlanMemberDefs.lean.

THE THOUGHT. The listing's return hangs on the skeleton alone of what was heard (front_skel,
Johnson/Road/K4/Total/FrontOfParts.lean). Behind a return of the hearing the skeleton is a function
of public things: the layout, the list of tables and the number of columns of the array of the reads
(hear_public, OnBytes/Desc/First/K4/HearPublic.lean); that the second token sumcheck is there, and
the lengths of three layers' points (hear_sizes, Johnson/Road/K4/Total/HearSkel.lean); the lookup's
shape. So a value of that skeleton can be written down with 0 for every element.

  `skel_plan`: behind a return of the hearing planOwn is there, and what was heard has its skeleton.
  **`front_returns_of_plan`**: a return of the hearing and a yes of the test: the listing returns at
    what was heard, at any two own claims.
  `frontB_of_return`: THE CONVERSE: where the listing returns behind a hearing, the test says yes:
    the test asks no more than the truth.
  `member_of_plan`: the two clauses skel and member of the law's structure Asks, at P₀ := P.
  `frontB_tokv`: the test does not read the tokens.
  **`front_returns_at_block`**: THE FORM FOR K4's BLOCK, which hears at its own public parameters
    with the request's tokens laid in: the test AT THE BLOCK's OWN PUBLIC PARAMETERS AND THE
    LAYOUT's OWN SHAPE P.y.fo. `member_at_block`: the clauses skel and member in that form.
New: the value by code. The rest: front_skel, hear_public, hear_sizes.
**Limits.** frontB IS A PREMISE: NOTHING HERE SAYS THAT IT IS TRUE AT ANY PLAN. NO RUN OF IT IS
CITED HERE. It is one evaluation of the listing at zeros, no line of arithmetic on the layout. AN
EVALUATION OUTSIDE THE KERNEL IS A RUN, NO THEOREM: the law then stands on a run still, though one
that needs no proof file; in Lean the test is paid by the kernel's own evaluation at a plan that is
a term, by closed forms of the listings, or by a block's test on its plan that asks it: none is done
here. In skel_plan, front_returns_of_plan and frontB_of_return P IS THE PUBLIC PARAMETERS AT WHICH
THE HEARING RAN, and sh IS READ OFF WHAT THE LOOKUP HAS HEARD (fo.shape): at the hearing's level
that is any value: the hearing's own test pins seven of the shape's fields to the layout, not all.
front_returns_at_block takes the plan's own letters, under hsh: fo.shape = P.y.fo: A PREMISE: the
lookup's law's to give: nobody's by name here. It says that the listing returns, not what a form is
worth. The law's other premises stay. Nothing on soundness. K04_law, the law of K4's block itself,
IS NOT PROVED. Met through Lean at no member.


-/
import Johnson.Road.K4.Total.PlanMemberDefs
import Johnson.Road.K4.Total.FrontOfParts
import Johnson.Road.K4.Total.PubOnly
import Johnson.Road.K4.Total.HearSkel
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard Env)

variable {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
  {rows : Bool}

/-- Behind a return of the hearing the plan's value is there, and what was heard has its skeleton.
-/
theorem skel_plan (h : hear engFl P hp g fo F t = some (o, G, u)) :
    ∃ o₀, planOwn P hp g fo.shape = some o₀ ∧ Skel o o₀ := by
  obtain ⟨_, _, iU3, tab, laid, nU3, _, _, _, _, e1, _, e3, _, ev, _⟩ := hear_public h
  obtain ⟨a1, a2, a3, a4, a5⟩ := hear_sizes h
  have v1 : o.v.y = P.y := by rw [ev]
  have v2 : o.v.tab = tab := by rw [ev]
  have v3 : o.v.K3 = ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 := by rw [ev]
  have v4 : o.H.fo.shape = fo.shape := by rw [a5]
  refine ⟨planOwnAt P hp g fo.shape iU3 tab, ?_, ?_⟩
  · unfold planOwn
    rw [e1, e3]
    rfl
  · exact
      { v := ⟨v1, v2, v3⟩
        tT := a1
        wpl := a2.trans (by
          show _ = (Array.replicate P.rd.muV zeroE).size
          rw [Array.size_replicate])
        hd := a3.trans (by
          show _ = (Array.replicate P.rd.muH zeroE).size
          rw [Array.size_replicate])
        hd2 := a4.trans (by
          show _ = some (Array.replicate P.rd.muH2 zeroE).size
          rw [Array.size_replicate])
        shape := v4 }

/-- **A return of the hearing and a yes of the test: the listing returns at what was heard.** -/
theorem front_returns_of_plan (h : hear engFl P hp g fo F t = some (o, G, u))
    (hB : frontB rows P hp g fo.shape = true) (a b : Aff) :
    (front rows P g o a b).isSome = true := by
  obtain ⟨o₀, e, S⟩ := skel_plan h
  unfold frontB at hB
  rw [e] at hB
  exact (front_skel rows P g o o₀ a b {} {} S).trans hB

/-- **The converse: the test asks no more than the truth.** -/
theorem frontB_of_return (h : hear engFl P hp g fo F t = some (o, G, u)) {a b : Aff}
    (hr : (front rows P g o a b).isSome = true) : frontB rows P hp g fo.shape = true := by
  obtain ⟨o₀, e, S⟩ := skel_plan h
  unfold frontB
  rw [e]
  exact (front_skel rows P g o o₀ a b {} {} S).symm.trans hr

/-- The clauses skel and member of the law's structure of premises. -/
theorem member_of_plan (h : hear engFl P hp g fo F t = some (o, G, u))
    (hB : frontB rows P hp g fo.shape = true) :
    ∃ o₀, Skel o o₀ ∧ ∃ a b, (front rows P g o₀ a b).isSome = true := by
  obtain ⟨o₀, e, S⟩ := skel_plan h
  unfold frontB at hB
  rw [e] at hB
  exact ⟨o₀, S, {}, {}, hB⟩

/-- The test does not read the tokens. -/
theorem frontB_tokv (rows : Bool) (P : Pub) (x : Array Nat) (hp : HPlan2) (g : Nat)
    (sh : Forest.Shape) : frontB rows { P with tokv := x } hp g sh = frontB rows P hp g sh := by
  have f : (fun o₀ => front rows { P with tokv := x } g o₀ {} {}) =
      fun o₀ => front rows P g o₀ {} {} :=
    funext fun o₀ => front_pub rows P { P with tokv := x } g o₀ {} {} rfl rfl
  show ((planOwn P hp g sh).bind fun o₀ => front rows { P with tokv := x } g o₀ {} {}).isSome = _
  rw [f]
  rfl

/-- **The form for K4's block**: the hearing at the block's public parameters with tokens laid in;
the test and the listing at the block's own public parameters; the shape the layout's own. -/
theorem front_returns_at_block {x : Array Nat}
    (h : hear engFl { P with tokv := x } hp g fo F t = some (o, G, u)) (hsh : fo.shape = P.y.fo)
    (hB : frontB rows P hp g P.y.fo = true) (a b : Aff) :
    (front rows P g o a b).isSome = true := by
  have k := front_returns_of_plan h (rows := rows) (by rw [frontB_tokv, hsh]; exact hB) a b
  rw [front_pub rows P { P with tokv := x } g o a b rfl rfl] at k
  exact k

/-- The clauses skel and member of the law's structures of premises, in the form for K4's block: the
member's public parameters are the block's own. -/
theorem member_at_block {x : Array Nat}
    (h : hear engFl { P with tokv := x } hp g fo F t = some (o, G, u)) (hsh : fo.shape = P.y.fo)
    (hB : frontB rows P hp g P.y.fo = true) :
    ∃ o₀, Skel o o₀ ∧ ∃ a b, (front rows P g o₀ a b).isSome = true := by
  obtain ⟨o₀, S, a, b, hm⟩ := member_of_plan h (rows := rows) (by rw [frontB_tokv, hsh]; exact hB)
  refine ⟨o₀, S, a, b, ?_⟩
  rw [← front_pub rows P { P with tokv := x } g o₀ a b rfl rfl]
  exact hm

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.member_at_block
#print axioms OnBytes.Desc.First.K4.Total.frontB_tokv
#print axioms OnBytes.Desc.First.K4.Total.front_returns_at_block
#print axioms OnBytes.Desc.First.K4.Total.skel_plan
#print axioms OnBytes.Desc.First.K4.Total.front_returns_of_plan
#print axioms OnBytes.Desc.First.K4.Total.frontB_of_return
#print axioms OnBytes.Desc.First.K4.Total.member_of_plan
