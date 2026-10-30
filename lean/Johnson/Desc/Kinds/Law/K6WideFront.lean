-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6WideFront.lean: ONE PREMISE OF THE LAW OF THE OUTPUT HEAD'S OWN ROUNDS AT
THE COMPOSED MEANING (Law/K6LawAtMgAll.lean: the field wide of K6DueMg: in front of these rounds the
array of the reads is as wide as planned), IN THAT FIELD'S OWN WORDS, FROM THE TABLE'S PROMISE IN
FRONT. Statements and proofs.

How. The list of extra public tests asks, at this sub-protocol's own place, the name (some 24,
"ledger.treesAre") (Johnson/Desc/First/FillSent.lean): the open ledger's arrays have the public
looks (rows, columns). Law/ReadsArray.lean has, wherever the maker of the public
parameters returns: the planned ledger's array number 0 has just Wp.H.nU.getD 2 0 columns; and
Law/ReadsNamed.lean: the array of the reads is number 0.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold).
  trees_asked        the name is asked at this sub-protocol's place, at every Mg.
  treesAre_front     so: FillSent.treesAreB D.pubD.dS 24 a.1.2 = true inside the promise at 341.
  **wide_front**     the field wide.
WHAT IS LEFT IN FRONT OF IT, beside what the law holds already (the maker's return hX, the place at
341, the table's test pubFit): hB: ONE EQUATION OF TWO LISTS OF NUMBERS ON PARAMETERS: the looks of
the built segment 24's planned ledger are those of the head's plan's.

Every letter under "there is": none. Rch is read by nothing here: it stands in the field's binder.
What it does not say. That any statement is inside the promise. Who makes or keeps the name: its
authors' laws. hB is no theorem: evaluated once, at one stored set of public files of the full size,
it is true there, and three negative tests are false. The full chain alone. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.K6SeatsTest
import Johnson.Desc.Kinds.Law.K6FrontSays
import Johnson.Desc.Kinds.Law.ReadsArray
import Johnson.Desc.First.SentTerms
import Johnson.Stored.HeadRidesB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning pubFit moreItem)
open VerifiableInference.Desc.First.FillSent (treesName treesAreB treesAt looksOf treeLook)
open VerifiableInference.Desc.Sound (Frame MsgT onQ linksFull MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (Fr : Frame)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- The name is asked at this sub-protocol's place, whatever Mg adds. -/
theorem trees_asked : treesName 24 ∈ ((MGA).more.rows linksFull placeK6).asks := by
  rw [Sound.mgAll_more_merges]
  refine List.mem_filter.2 ⟨?_, by decide⟩
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  decide

/-- **The open ledger's arrays have the public looks.** -/
theorem treesAre_front (hfit : pubFit (MGA).more linksFull PS = true)
    (hp : PS[341]? = some placeK6) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none) :
    treesAreB D.pubD.dS 24 a.1.2 = true := by
  have h : (MGA).pub (moreItem (treesName 24)) a.1 = true :=
    asked_more Fr D.N MGA linksFull PS (fun a => a) hfit 341 placeK6 hp a ha hm (treesName 24)
      (trees_asked D Mg)
  rw [Sound.mgAll_pub] at h
  exact (First.pubAll_more_treesAre D.pubD Mg.pub 24 a.1).symm.trans h

/-- **The field wide of K6DueMg.** -/
theorem wide_front {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hB : treesAt D.built 24 = looksOf Wp.H.Fp)
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop)
    (hfit : pubFit (MGA).more linksFull PS = true)
    (hp : PS[341]? = some { chain := 1, link := some 24, piece := 4, kind := .K6 }) :
    ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → readsWideB (readsOf Wp) (Wp.H.nU.getD 2 0) a.1.2 = true := by
  intro a ha _ hm
  obtain ⟨G, hG, e⟩ := any_some (treesAre_front D Mg Fr hfit hp a ha hm)
  have e1 : G.trees.toList.map treeLook = looksOf Wp.H.Fp :=
    (of_decide_eq_true e).trans hB
  obtain ⟨hpos, hK, _, _⟩ := ReadsArray.public_array hX
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
  unfold readsWideB
  rw [hG, h0]
  dsimp only
  cases hg : G.trees[0]? with
  | none =>
    rw [hg] at e0
    cases e0
  | some tr =>
    rw [hg] at e0
    have e3 : tr.K = (Wp.H.Fp.trees.getD 0 {}).K :=
      congrArg (fun x => x.2.1) (Option.some.inj e0)
    show Decidable.decide (Wp.H.nU.getD 2 0 ≤ tr.K) = true
    rw [e3, hK]
    exact decide_eq_true (Nat.le_refl _)

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.treesAre_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.wide_front
