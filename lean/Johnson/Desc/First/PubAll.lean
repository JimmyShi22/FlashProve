-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/PubAll.lean: the public tests on the verifier's state of all authors' parts of
the meaning of the open claims, composed: one function with code. No Mathlib.
Between two sub-protocols of a request's own rounds the table (Johnson/Desc/First/Borders.lean)
asks public items (`Pub`) of the verifier's state. Each kind of sub-protocol's authors give the
Boolean tests for their items as a function "over whatever answers the other items".
ELEVEN SUCH FUNCTIONS, from the innermost:
  the table's own (`pubKeeper`, Johnson/Desc/First/FillKeeper.lean): ledger, freeAbove, unheard;
  the feed-forward sub-protocol's two names (`FillBare.pubLeft`,
    Johnson/Desc/First/FillBare.lean);
  what has been sent, behind the second sending (`FillSent.pubSent1`,
    Johnson/Desc/First/FillSentLater.lean): one name a segment;
  what has been sent (`FillSent.pubSent`, Johnson/Desc/First/FillSent.lean): two names a segment;
  attention's (`H2K5.Door.pubK5`, Johnson/Desc/First/Att/Door/PubK5.lean): look, callerIn and four
    names at an attention segment;
  the pending claim on the weights (`FillP1.pubP1`, Johnson/Top/H0/Fill/PubP1.lean): hasRow;
  the feed-forward sub-protocol's (`FillK4.pubK4`, Johnson/Desc/First/FillK4.lean): look, callerIn
    at a feed-forward segment;
  the output head's (`Kinds.Head.pubK6K7`, Johnson/Stored/FillK6K7.lean): tokenSmall; look at its
    segment;
  the lookup arguments' (`Look.pubK3`, Johnson/Desc/First/Look/K3FillCode.lean): lookIn, lookOut
    at their two places in a segment; linkFresh; left, leftOn (true: their sentences stand in
    pubP);
  the last sub-protocols' (`K13.pubK13C`, Johnson/Desc/K13/PubK13.lean): noneSent, indexIs,
    indexThere, frontOk, evalLaid, one name;
  the claims on linear forms (`K9.pubForms`, Johnson/Desc/First/Batch/FormsPub.lean): formsIn,
    formsInT, totalIn.
A test that says a fact which holds at every state
that the verifier reaches is not asked by the table
(Johnson/Desc/First/SmallDoor.lean).
  `PubData0`, `PubData`: the functions' parameters, in one structure; the second adds what the
    composed meaning makes from its other parameters.
  `pubAll D base`: the functions, one over the other; base answers at an item that none claims.
  `formsItem`, `whoFills D q`: which part answers at the public item q, by the parts' own tests
    "is the item mine", the outermost first; none: no part.
  `pubAll_else`: where each of the eleven functions' own tests "is the item mine" says no, `pubAll`
    is base (eleven premises; the statement does not name `whoFills`).
Limits: definitions. look is answered by three parts, at other segments. No soundness is claimed.

-/
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.FillK4
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.First.Batch.FormsPub
import Johnson.Desc.K13.PubK13
import Johnson.Stored.FillK6K7
import Johnson.Top.H0.Fill.PubP1
import Johnson.Desc.First.Att.Door.PubK5
import Johnson.Desc.First.FillSentLater
import Johnson.Desc.First.FillBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc.K9 (Readers pubForms)
open VerifiableInference.Desc.K13 (Where pubK13C k13ItemC pubK13C_else)
open VerifiableInference.Desc.First.FillK4 (pubK4 k4Item isLay)
open VerifiableInference.Desc.Kinds.Head (pubK6K7 k6k7Item)
open VerifiableInference.Desc.First.Look (K3Data pubK3 k3Item k3SortAt lookInC lookOutC)
open VerifiableInference.Desc.First.FillP1 (pubP1 p1Item pubP1_else)
open H2K5.Door (K5Data pubK5 k5Item)
open VerifiableInference.Desc.First.FillSent (SentData pubSent sentItem pubSent1 sent1Item)
open VerifiableInference.Desc.First.FillBare (pubLeft leftItem)

/-- The functions' parameters, but for what the composed meaning makes. -/
structure PubData0 where
  /-- public numbers for the pending claim on the weights and the approximate range proof's names -/
  d1 : FillP1.PubData
  /-- the sorts of the chain's segments -/
  links : List ModelPart
  /-- the built segments of the public parameters -/
  built : Array OnBytes.Model.Stages.LinkH
  /-- the last sub-protocols' numbers; the codes -/
  P13 : Where
  cs : OnBytes.Codes
  /-- the table's numbers: ONE for every part that reads them -/
  N : Numbers

/-- The functions' parameters. -/
structure PubData extends PubData0 where
  /-- the head's segment's number; its shape; the number of its array of the reads -/
  mH : Nat
  hShape : OnBytes.Model.Head.Shape
  iU3 : Nat
  /-- the feed-forward caller's number at a segment -/
  nextOf : Nat → Option Nat
  /-- the segments' readers, the map of names, of which runs the forms may name what is ahead -/
  Rd : Nat → Readers
  runs : Nat → Nat → String → List (Nat × String)
  ah : Nat → String → Bool
  /-- the number of slots of a segment's ledger -/
  nsOf : Nat → Option Nat
  /-- what has been sent behind a segment's first and second sending; the look of its arrays -/
  dS : SentData
  dS1 : SentData
  /-- the lookups' data -/
  d3 : K3Data
  /-- the attention caller's data -/
  d5 : K5Data

/-- **All parts' public tests, composed.** -/
def pubAll {P : Type} (D : PubData) (base : Pub → P × S → Bool) : Pub → P × S → Bool :=
  pubForms D.Rd D.runs D.ah D.N (pubK13C D.P13 D.cs D.N (pubK3 D.d3
    (pubK6K7 D.hShape D.iU3 D.mH (pubK4 D.links D.nextOf (pubP1 D.d1 (pubK5 D.d5 (pubSent D.dS
      (pubSent1 D.dS1 (pubLeft D.links (pubKeeper D.nsOf base))))))))))

/-- Is the item one of the claims on linear forms' part's? -/
def formsItem : Pub → Bool
  | .formsIn _ _ _ => true
  | .formsInT _ _ _ => true
  | .totalIn _ => true
  | _ => false

/-- Which part answers at a public item. -/
def whoFills (D : PubData) (q : Pub) : Option String :=
  if formsItem q then some "the runs' forms"
  else if k13ItemC q then some "the index's and the last blocks'"
  else if k3Item D.d3 q then some "the lookups'"
  else if k6k7Item D.mH q then some "the head's"
  else if k4Item D.links q then some "the feed-forward caller's"
  else if p1Item q then some "the row on the weights' and the smallness test's names'"
  else if k5Item D.d5 q then some "the attention caller's"
  else if sentItem q then some "what stands sent"
  else if sent1Item q then some "what stands sent, later"
  else if leftItem D.links q then some "the feed-forward caller's two names"
  else if keeperItem q then some "the table's own"
  else none

/-- Where no part answers, the composed function is base. -/
theorem pubAll_else {P : Type} (D : PubData) (base : Pub → P × S → Bool) (q : Pub)
    (h1 : formsItem q = false) (h2 : k13ItemC q = false) (h8 : k3Item D.d3 q = false)
    (h3 : k6k7Item D.mH q = false)
    (h4 : k4Item D.links q = false)
    (h9 : p1Item q = false) (h10 : k5Item D.d5 q = false)
    (h11 : sentItem q = false) (h13 : sent1Item q = false) (h12 : leftItem D.links q = false)
    (h7 : keeperItem q = false) (a : P × S) : pubAll D base q a = base q a := by
  have e1 : ∀ f : Pub → P × S → Bool, pubForms D.Rd D.runs D.ah D.N f q a = f q a := by
    intro f
    cases q <;> first | rfl | (simp [formsItem] at h1)
  have e8 : ∀ f : Pub → P × S → Bool, pubK3 D.d3 f q a = f q a := by
    intro f
    cases q with
    | lookIn m pc =>
      have e : k3SortAt D.d3.X m pc = none := by simpa [k3Item] using h8
      show (match k3SortAt D.d3.X m pc with
        | some dg => lookInC D.d3 m dg a.2
        | none => f (.lookIn m pc) a) = _
      rw [e]
    | lookOut m pc =>
      have e : k3SortAt D.d3.X m pc = none := by simpa [k3Item] using h8
      show (match k3SortAt D.d3.X m pc with
        | some dg => lookOutC D.d3 m dg a.2
        | none => f (.lookOut m pc) a) = _
      rw [e]
    | linkFresh m => simp [k3Item] at h8
    | left m => simp [k3Item] at h8
    | leftOn m => simp [k3Item] at h8
    | _ => rfl
  have e3 : ∀ f : Pub → P × S → Bool, pubK6K7 D.hShape D.iU3 D.mH f q a = f q a := by
    intro f
    cases q with
    | tokenSmall => simp [k6k7Item] at h3
    | look m =>
      show (if m == D.mH then _ else f (.look m) a) = _
      have h' : (m == D.mH) = false := h3
      rw [h']
      rfl
    | _ => rfl
  have e4 : ∀ f : Pub → P × S → Bool, pubK4 D.links D.nextOf f q a = f q a := by
    intro f
    cases q with
    | look m =>
      show (if isLay D.links m then _ else f (.look m) a) = _
      rw [if_neg (by simpa [k4Item] using h4)]
    | callerIn m =>
      show (if isLay D.links m then _ else f (.callerIn m) a) = _
      rw [if_neg (by simpa [k4Item] using h4)]
    | _ => rfl
  have e10 : ∀ f : Pub → P × S → Bool, pubK5 D.d5 f q a = f q a := by
    intro f
    cases q with
    | callerIn m =>
      show (if D.d5.isAtt m then _ else _) = _
      rw [if_neg (by simpa [k5Item] using h10)]
    | look m =>
      show (if D.d5.isAtt m then _ else _) = _
      rw [if_neg (by simpa [k5Item] using h10)]
    | more sg n =>
      cases sg with
      | none => rfl
      | some m =>
        have h' : (D.d5.isAtt m && n == "K5.readsThere") = false ∧
            (D.d5.isAtt m && n == "K5.okAt") = false ∧
            (D.d5.isAtt m && n == "K5.liveReq") = false ∧
            (D.d5.isAtt m && n == "K5.plain") = false := by
          simp only [k5Item, Bool.and_eq_false_iff, Bool.or_eq_false_iff] at h10
          rcases h10 with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          · simp [h]
          · simp [h1, h2, h3, h4]
        show (if (D.d5.isAtt m && n == "K5.readsThere") = true then _
          else if (D.d5.isAtt m && n == "K5.okAt") = true then _
          else if (D.d5.isAtt m && n == "K5.liveReq") = true then _
          else if (D.d5.isAtt m && n == "K5.plain") = true then _ else _) = _
        rw [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2]
        rfl
    | _ => rfl
  have e11 : ∀ f : Pub → P × S → Bool, pubSent D.dS f q a = f q a := by
    intro f
    unfold pubSent
    split
    · rename_i m name
      simp only [sentItem, Bool.or_eq_false_iff] at h11
      rw [if_neg (by simp [h11.1]), if_neg (by simp [h11.2])]
    · rfl
  have e13 : ∀ f : Pub → P × S → Bool, pubSent1 D.dS1 f q a = f q a := by
    intro f
    unfold pubSent1
    split
    · rename_i m name
      simp only [sent1Item] at h13
      rw [if_neg (by simp [h13])]
    · rfl
  have e12 : ∀ f : Pub → P × S → Bool, pubLeft D.links f q a = f q a := by
    intro f
    cases q with
    | more sg name =>
      cases sg with
      | none => rfl
      | some m =>
        have e : (D.links[m]? == some .layers &&
            (name == "K4.rowsBare" || name == "K4.lookLeft")) = false := h12
        unfold pubLeft
        cases h1 : (D.links[m]? == some .layers) with
        | false =>
          have h1' : D.links[m]? ≠ some .layers := by simpa using h1
          simp [h1']
        | true =>
          rw [h1, Bool.true_and, Bool.or_eq_false_iff] at e
          simp [e.1, e.2]
    | _ => rfl
  have e7 : pubKeeper D.nsOf base q a = base q a := by
    cases q <;> first | rfl | (simp [keeperItem] at h7)
  unfold pubAll
  rw [e1, pubK13C_else D.P13 D.cs D.N _ q h2 a, e8, e3, e4, pubP1_else D.d1 _ q h9 a, e10, e11, e13,
    e12, e7]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.pubAll_else
