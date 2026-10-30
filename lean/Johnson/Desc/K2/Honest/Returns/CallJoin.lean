-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/CallJoin.lean: THE CALL OF THE SWITCH AT ANY FRONT (`CallCore`,
Returns/ArmsBehind.lean: fifteen fields, 50 clauses laid open) FROM TWO BUNDLES: WHAT THIS FOLDER's
FILES PAY AT A REACHED STATE (`CallPaid`) AND WHAT IS LEFT (`CallRest`: eleven clauses). No state,
no plan: a join at a front x, a book B and two rounds, for the two arms' places to call. A statement
with its proof: fields laid through.

  `callIn p x B roots r₁ r₂ cols` what the reading of the old rows is handed, as `CallCore.reads`
                    spells it: a short name
  `CallPaid p x B r₁ r₂ c` the entry's test at the front's notices · `step` · four on the draws ·
                    `oldCode` · `FrontCore.keptPos` · the carried rows have two masks · `LayFits` ·
                    each message that the reading names is in the statement · the stored sample rows
                    are good (`SampleGoodS`) · `ShapeFits` · `PublicFits` · `OldFits.rows`, `named`,
                    `stored` · `TablesFit.claimKept`, `claimMain`
  `CallRest p x B roots r₁ r₂ cols c code` WHAT IS LEFT, each field in the letters of the structure
                    that asks it: five on the two rounds and the columns (fits₁ · vals · answers ·
                    loc · `ReadFits.opens`) · `ReadFits.own` · four on what the front holds of the
                    plan (plan · trees · `FrontCore.groupCode` · copiesCode) · `FrontCore.inRange`
  `callCore_join` the two give `CallCore`

By, this folder's: `LayFits.reads` (Returns/ClosedReached.lean) · `ShapeFits.reads`,
`ShapeFits.tables` (Returns/PinReached.lean).

Limits. Neither bundle is shown met here: the arms' files meet the first. `OldFits.mainVars`, `d0`,
`d1` are laid from `ShapeFits`, which the arms' files have under three tests on the public part,
though Returns/ArmsFree.lean has the three with no test. This file's imports are heavy. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.ArmsBehind
import Johnson.Desc.K2.Honest.Returns.ClosedReached
import Johnson.Desc.K2.Honest.Returns.PinPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.First.K2 (P2 par9 locOk behindArgs SampleGoodS)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Tw.K2 (Front Col SwIn switchNotices)

/-- What the reading of the old rows is handed, as `CallCore.reads` spells it. -/
abbrev callIn (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) : SwIn :=
  inFront (par9 p) x B (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols

/-- **What this folder's files pay of the call at a reached state.** c: the old main code. -/
structure CallPaid (p : P2) (x : Front) (B : TreeBook) (r₁ r₂ : Fmt.RoundView) (c : Code) : Prop where
  entry : planOk1 none (switchNotices x.T x.others) (par9 p).eSeed = true
  step : x.st.oracles.size = B.place.size
  draw : (r₁.drawn.elems.map E.ofTriple).length =
    (sendingAt p x).seeds * ((sendingAt p x).coordinates + 1)
  poss : r₁.drawn.poss = []
  trits : r₁.drawn.trits = []
  factor : ∀ z ∈ K1.seedsOf (sendingAt p x) r₁, isZeroE z.2 = false
  oldCode : x.st.codes.base[x.f.rows.code]? = some c
  keptPos : ∀ k ∈ x.T.kept.toList, 0 < k.shape.mainRows
  masks : x.f.rows.masks = 2
  lay : LayFits x.st x.f.rows
  stated : ∀ o ∈ (singleRowsOracles x.f.rows).toList, o < x.st.oracles.size
  good : SampleGoodS x.st
  shape : ShapeFits x
  pub : PublicFits x
  rows : x.f.rows.keptRows =
    ((switchKept x.f.rows).toList.map fun o => (x.st.oracles.getD o default).shape.mainRows).sum
  named : ∀ k ∈ x.f.rows.kept.toList, k.oracle ∈ (switchKept x.f.rows).toList
  stored : ∀ o ∈ (switchKept x.f.rows).toList,
    ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList, r.runs.size = 0 ∧ r.forms.size = 0
  claimKept : ∀ k ∈ x.f.rows.kept.toList,
    Own.formFits k.c (x.st.tableBits k.oracle .main) = true
  claimMain : Own.formFits x.f.rows.c (x.st.codes.base.getD x.f.rows.code default).logEll = true

/-- **What is left of the call.** c: the old main code; code: the new group's main code. -/
structure CallRest (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (c : Code) (code : Nat) : Prop where
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  plan : K1.planOkOwn (sendingAt p x) = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p x) r₂)).length = (sendingAt p x).answers
  trees : ((layTrees (sendingAt p x).codes (sendingAt p x).sent).getD {}).shapes.size =
    (par9 p).eSeed.roots
  loc : locOk (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols) c.logN =
    true
  readsOwn : ∀ t ∈ treesOf (callIn p x B roots r₁ r₂ cols), ∀ tree,
    (callIn p x B roots r₁ r₂ cols).book.trees[t]? = some tree →
    ∀ q ∈ tree.parts.toList, q ∈ (idsOf (callIn p x B roots r₁ r₂ cols)).toList
  readsOpens : AllOpen (callIn p x B roots r₁ r₂ cols).st (callIn p x B roots r₁ r₂ cols).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (callIn p x B roots r₁ r₂ cols).book
    (treesOf (callIn p x B roots r₁ r₂ cols)) (callIn p x B roots r₁ r₂ cols).opened
  inRange : ∀ v ∈ (Positions.ofDraws c.logN r₂.drawn.poss).all.toList,
    v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN
  groupCode : x.T.shape.code = code
  copiesCode : ∀ k ∈ x.T.kept.toList, k.shape.code = code

/-- **The two bundles give the call.** -/
theorem callCore_join {p : P2} {x : Front} {B : TreeBook} {roots : Nat} {r₁ r₂ : Fmt.RoundView}
    {cols : List OpenedColumn} {c : Code} {code : Nat} (H : CallPaid p x B r₁ r₂ c)
    (E : CallRest p x B roots r₁ r₂ cols c code) : CallCore p x B roots r₁ r₂ cols c code := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    H.lay.reads (i := callIn p x B roots r₁ r₂ cols) rfl rfl
  exact
    { entry := H.entry, fits₁ := E.fits₁, plan := E.plan, step := H.step, draw := H.draw
      vals := E.vals, poss := H.poss, trits := H.trits, factor := H.factor, answers := E.answers
      trees := E.trees, oldCode := H.oldCode, loc := E.loc
      reads :=
        { masks := H.masks, challenges := l1, maskVars := l2, keptSize := l3, mainSize := l4
          maskSize := l5
          placed := fun o ho => by
            show o < B.place.size
            rw [← H.step]
            exact H.stated o ho
          stated := H.stated, own := E.readsOwn, opens := E.readsOpens, fits := l6, keptRows := l7
          fresh := l8 }
      front :=
        { check := H.shape.check, restMain := H.pub.restMain
          fits :=
            { mainVars := H.shape.mainVars, d0 := H.shape.d0, d1 := H.shape.d1, rows := H.rows
              named := H.named, once := H.shape.once, keptCode := H.shape.keptCode
              stored := H.stored }
          keptPos := H.keptPos, keptAnswers := H.pub.keptAnswers, lengths := H.pub.lengths
          logC := H.pub.logC, logZ := H.pub.logZ, inRange := E.inRange, groupCode := E.groupCode
          copiesCode := E.copiesCode
          tables :=
            { bitsG := H.pub.bitsG, bitsKept := H.shape.bitsKept, claimMain := H.claimMain
              claimKept := H.claimKept, stored := H.shape.tables H.good H.keptPos }
          reads := H.shape.reads H.good } }

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.callCore_join
