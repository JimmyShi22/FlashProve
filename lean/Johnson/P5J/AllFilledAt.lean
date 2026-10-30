-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/AllFilledAt.lean: AN ATTACK ON THE COMPOSED MEANING: DOES ANYTHING THAT THE TABLE's
PROMISE ASKS AT THE FULL SIZE FALL TO THE CLOSED MEANING BENEATH (`mgBase`,
Johnson/Desc/Sound/MgBase.lean), WHICH SAYS "false" AT EVERY STATE? NO. WHAT THIS DOES NOT SAY
STANDS FIRST: THAT THE LAYERS' OWN ANSWERS CAN BE TRUE TOGETHER AT A STATE: a layer may itself say
false at an item that it claims: on that only runs are out (an honest proof's walk: evaluated, no
theorem).
Why it matters. The promise stands in front of every tie of every kind's law. Were one of its
parts false at every state from some border on, every law from that border on would hold for
nothing.
The promise (`onAt`, Johnson/Desc/First/Borders.lean) reads seven fields of the
meaning: decodes, inOrder, pub, held, shown, noColl, pubP. The base says False or false at five of
them.
  `allFilledBy_full`: BY THE KERNEL: every public item that is asked at any border is claimed by a
    layer of the composed meaning (`allFilledBy`, Johnson/Desc/First/AllFilledBy.lean).
    `unfilledBy_full`: the list of the unclaimed is empty.
  `asked_lists`, `sets_lengths`, `asked_items`, `asked_none_empty`: SO THAT "EVERY" IS NOT OVER
    NOTHING: 359 lists, one a border; the two lists that are zipped have 359 members each, so that
    the zip drops none; 3,298 items in all; no list is empty.
  `bend_hd`, `bend_mH`, `bend_links5`, `bend_linksD`: NEGATIVE TESTS, one for each letter of the
    test: each says false: each letter bites.
  `worthFilledBy_full`, `allSaid_full`: the like for the field worth at the open items and for the
    sentences pubP.
  `allFilled_at`: THE THEOREM THAT COUNTS: from the head: `allFilled` at the composed meaning's
    OWN data (`MgData.pubD`) at the closed constant: by `allFilled_by` and four equations.
  `asked_covers`: what `onQ` (Johnson/Desc/Sound/BordersQ.lean :65-67) hands to the promise at
    border k, in its own terms, is the k-th list. `asked_not_base`: SO: at every border, at every
    public item that the promise asks there, at every state: the composed meaning's answer is the
    same over ANY meaning beneath (`mgAll_pub_base`): the base's "false" is never read.
  `mgAll_decodes_any`, `mgAll_held_any`, `mgAll_shown_any`, `mgAll_noColl_any`: these four fields
    do not feel the meaning beneath: equations by unfolding. (inOrder over the base:
    `mgAll_inOrder_base`, landed.)
Limits. `whoFills` is a table of names beside `pubAll`; what ties the two is the landed
`pubAll_some`. NOT WEIGHED HERE, BUT FOR worth: THE FIELDS ON THE SIDE OF THE RELATIONS (pin,
pinW, constr, tie, forms, formsT, wo, total, row, carry, pile …), at which the base says False
too: whether each layer gives its field whole or hands cases down is a line of attack of its own,
open. (A reading, no theorem: an item that is False at every witness makes idle each step behind
which it is open, since that step's clause begins "every witness behind"; and it makes unprovable
the step that must show it in front. Which of the two wins along the chain is held by no file.)
The head h is a premise of `allFilled_at` and `asked_not_base`: a member of it is proved at `storedPublicFiles`
and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone.
No soundness is claimed.

-/
import Johnson.P5J.AllFilledFull
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Pub allFilled allFilledBy askedAt allFilled_by
  allFilled_mem pubSets openSets pubOfItems start hdOf)

/-! ## 1 Four fields of the promise do not feel the meaning beneath -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg Mg' : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

theorem mgAll_decodes_any : (mgAll 𝔇 Mg).decodes = (mgAll 𝔇 Mg').decodes := rfl

theorem mgAll_held_any : (mgAll 𝔇 Mg).held = (mgAll 𝔇 Mg').held := rfl

theorem mgAll_shown_any : (mgAll 𝔇 Mg).shown = (mgAll 𝔇 Mg').shown := rfl

theorem mgAll_noColl_any : (mgAll 𝔇 Mg).noColl = (mgAll 𝔇 Mg').noColl := rfl

end

/-! ## 2 At the closed constant -/

/-- What `onQ` hands to the promise at border k is the k-th list. -/
theorem asked_covers {k : ℕ} {q : Pub}
    (hq : q ∈ (pubSets mgMore fullLinks At.ps)[k]?.getD [] ++
      pubOfItems ((openSets fullLinks At.ps (start fullLinks))[k]?.getD [])) :
    ∃ Q, (askedAt mgMore fullLinks At.ps)[k]? = some Q ∧ q ∈ Q := by
  obtain ⟨l1, l2⟩ := sets_lengths
  by_cases hk : k < 359
  · have h1 : k < (pubSets mgMore fullLinks At.ps).length := by rw [l1]; exact hk
    have h2 : k < (openSets fullLinks At.ps (start fullLinks)).length := by rw [l2]; exact hk
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hq
    refine ⟨_, ?_, hq⟩
    unfold askedAt
    rw [List.getElem?_zipWith, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
    rfl
  · have h1 : (pubSets mgMore fullLinks At.ps)[k]? = none :=
      List.getElem?_eq_none (by rw [l1]; omega)
    have h2 : (openSets fullLinks At.ps (start fullLinks))[k]? = none :=
      List.getElem?_eq_none (by rw [l2]; omega)
    rw [h1, h2] at hq
    exact absurd (show q ∈ ([] : List Pub) from hq) List.not_mem_nil

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE THEOREM THAT COUNTS: AT THE COMPOSED MEANING's OWN DATA, FROM THE HEAD.** -/
theorem allFilled_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    allFilled (h.toAtMg.𝔇 h.𝔇).pubD mgMore fullLinks At.ps = true := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have e1 : hdOf (h.toAtMg.𝔇 h.𝔇).pubD.d3.X = 24 := by
    show (if (At.X Zp).p4 then 2 else 1) * (At.X Zp).NGr = 24
    rw [p4, ng]
    rfl
  have e2 : (h.toAtMg.𝔇 h.𝔇).pubD.mH = 24 := headLink_in_scope h.scope h.reads h.pubOne
  rw [allFilled_by, e1, e2]
  exact allFilledBy_full

/-- The same in the letters of the constant's own name: `mgAtAll h`, its data and its door. -/
theorem allFilled_at_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    allFilled h.𝔇.pubD (mgAtAll h).more fullLinks At.ps = true := by
  have e : (mgAtAll h).more = mgMore := mgAll_more_base h.𝔇
  rw [e]
  exact allFilled_at h

/-- **THE BASE's "false" IS NEVER READ**: at every border, at every public item that the promise
asks there, at every state. -/
theorem asked_not_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {k : ℕ} {q : Pub}
    (hq : q ∈ (pubSets mgMore fullLinks At.ps)[k]?.getD [] ++
      pubOfItems ((openSets fullLinks At.ps (start fullLinks))[k]?.getD []))
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    (a : ProofFile.InstPub × VerifiableInference.Desc.First.S) :
    (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub q a = (mgAll (h.toAtMg.𝔇 h.𝔇) Mg).pub q a := by
  obtain ⟨Q, hQ, hm⟩ := asked_covers hq
  exact mgAll_pub_base _ Mg q a
    (allFilled_mem _ _ _ _ (allFilled_at h) Q (List.mem_of_getElem? hQ) q hm)

end P5J

#print axioms P5J.mgAll_decodes_any
#print axioms P5J.mgAll_held_any
#print axioms P5J.mgAll_shown_any
#print axioms P5J.mgAll_noColl_any
#print axioms P5J.asked_covers
#print axioms P5J.allFilled_at
#print axioms P5J.allFilled_at_all
#print axioms P5J.asked_not_base
