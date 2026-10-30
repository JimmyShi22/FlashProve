-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/FrontMore.lean: FOUR MORE SENTENCES ON THE VERIFIER's STATE IN FRONT OF
THE OUTPUT HEAD's OWN ROUNDS, out of the structure `K6FrontItems`
(Johnson/Desc/K6/Honest/Law/FrontItems.lean). Statements with their proofs.

What it is not. Nothing here shows the structure of any state: every statement is CONDITIONAL on it.
It speaks of the full chain alone. The two premises of the last two are paid under `P5J.AtMgA`: the
first is its field pubOne, the second the library's `trees_at_const`
(Johnson/Desc/Kinds/Law/K6BuiltAtConst.lean); they are not called here;
Johnson/Desc/K6/Honest/Law/BehindAtHead.lean pays both where it calls `four_of_front` (the second
through the field treesB of `paid_at_const`, Johnson/Desc/Kinds/Law/K06AtConst.lean). Nothing on any
property.

  `K6FrontItems.link`      a segment is open, and its number is 24
  `K6FrontItems.linkArr`   its list of arrays is the public one; nothing is heard yet of the lookup
                           argument on the digits
  `K6FrontItems.oneRow`    CONDITIONAL on two premises on public data: the array of the reads has
                           one row and the planned number of columns
  `K6FrontItems.wide`      CONDITIONAL on the same two: it is wide enough

WHAT IS TYPED ANEW, AND WHY: the four have the conclusions of the library's `link_front`,
`linkArr_front`, `oneRow_front` (Johnson/Desc/Kinds/Law/K6FrontShape.lean) and `wide_front`
(K6WideFront.lean), whose premise is the library's promise at the composed meaning, with its clauses
on the oracles' strings: on the honest side that premise is not to be had. The proofs of the first
three are those lemmas' own lines behind the structure's fields; the fourth follows from the third.

-/
import Johnson.Desc.K6.Honest.Law.FrontItems
import Johnson.Desc.Kinds.Law.K6FrontShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.First.FillSent (treesAt looksOf treeLook)
open VerifiableInference.Desc.Sound (MgData MsgT CellsQ)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (placeK6 any_some)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  {D : MgData Xi P Tok rows cols nR Wp} {Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)}
  {a : P × S}

/-- **A segment is open, and its number is 24.** -/
theorem K6FrontItems.link (R : K6FrontItems D Mg a) : ∃ L, a.2.link? = some L ∧ L.link = 24 := by
  obtain ⟨L, hL, _⟩ := any_some R.sentIs
  have h := R.shape
  unfold First.shapeAt at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  rw [hL] at h2
  have h3 : (placeK6.link == some L.link) = true := h2
  have h4 : (some 24 : Option ℕ) = some L.link := eq_of_beq h3
  exact ⟨L, hL, (Option.some.inj h4).symm⟩

/-- **The open segment's number and its list of arrays; and nothing is heard yet of the lookup
argument on the digits.** -/
theorem K6FrontItems.linkArr (R : K6FrontItems D Mg a) :
    (∃ L, a.2.link? = some L ∧ L.link = 24 ∧ L.arrayOf = D.sent.arrayOf.getD 24 #[]) ∧
      (a.2.tl?.bind (·.heard)).isNone = true := by
  obtain ⟨L, hL, h24⟩ := R.link
  have hfr := R.linkFresh
  unfold VerifiableInference.OnPublicFiles.linkFreshB at hfr
  rw [Bool.and_eq_true, hL] at hfr
  exact ⟨⟨L, hL, h24, eq_of_beq hfr.2⟩, hfr.1⟩

/-- **The array of the reads: one row, and the planned number of columns.** CONDITIONAL: the public
parameters are made of public files; the built segment's trees have the planned looks. -/
theorem K6FrontItems.oneRow (R : K6FrontItems D Mg a) {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hB : treesAt D.built 24 = looksOf Wp.H.Fp) :
    ∃ G tr, a.2.fork? = some G ∧ G.trees[readsOf Wp]? = some tr ∧ tr.R = 1 ∧
      tr.K = Wp.H.nU.getD 2 0 := by
  obtain ⟨G, hG, e⟩ := any_some R.treesAre
  have e1 : G.trees.toList.map treeLook = looksOf Wp.H.Fp :=
    (of_decide_eq_true e).trans hB
  obtain ⟨hpos, hK, hR, _⟩ := ReadsArray.public_array hX
  have h0 : readsOf Wp = 0 := by
    have h3 : Wp.H.tl.ix.U.getD 2 none = some 0 := ReadsNamed.public_third hX
    unfold readsOf
    rw [h3]
    rfl
  have hT : Wp.H.Fp.trees[0]? = some (Wp.H.Fp.trees.getD 0 {}) := by
    rw [Array.getElem?_eq_getElem hpos, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hpos]
    rfl
  have e0 : (G.trees[0]?).map treeLook =
      (Wp.H.Fp.trees[0]?).map fun T => (T.R, T.K, T.rows.toList.map fun r => (r.L0, T.K)) := by
    have e2 := congrArg (fun l => l[0]?) e1
    unfold looksOf at e2
    simpa only [List.getElem?_map, Array.getElem?_toList] using e2
  rw [hT] at e0
  rw [h0]
  cases hg : G.trees[0]? with
  | none =>
    rw [hg] at e0
    cases e0
  | some tr =>
    rw [hg] at e0
    have e3 := Option.some.inj e0
    exact ⟨G, tr, hG, hg, (congrArg (fun x => x.1) e3).trans hR,
      (congrArg (fun x => x.2.1) e3).trans hK⟩

/-- **The array of the reads is wide enough.** CONDITIONAL on the same two. -/
theorem K6FrontItems.wide (R : K6FrontItems D Mg a) {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hB : treesAt D.built 24 = looksOf Wp.H.Fp) :
    readsWideB (readsOf Wp) (Wp.H.nU.getD 2 0) a.2 = true := by
  obtain ⟨G, tr, hG, hg, _, hK⟩ := R.oneRow hX hB
  unfold readsWideB
  rw [hG]
  dsimp only
  rw [hg]
  show Decidable.decide (Wp.H.nU.getD 2 0 ≤ tr.K) = true
  rw [hK]
  exact decide_eq_true (Nat.le_refl _)

/-- The same in the writing of a caller. -/
example (R : K6FrontItems D Mg a) {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hB : treesAt D.built 24 = looksOf Wp.H.Fp) :
    readsWideB (readsOf Wp) ((p8K6 Wp 24).hp.nU.getD 2 0) a.2 = true := R.wide hX hB

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.link
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.linkArr
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.oneRow
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6FrontItems.wide
