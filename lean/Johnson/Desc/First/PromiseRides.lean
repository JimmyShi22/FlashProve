-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/PromiseRides.lean: HOW THE TABLE OF JOINTS' PROMISE RIDES PAST A BLOCK, CLAUSE BY
CLAUSE: the promise's twin of "what rides" for the items. Small lemmas; no Mathlib. A file BESIDE
the table: it turns nothing of it.

Why. Behind every block the WHOLE promise is owed (Johnson/Desc/First/Borders.lean, `onAt`), though
a kind's law speaks of a clause or two. The items have a rule for what a block does not touch
(`Piece.Frames`); the promise had none: so every kind would pay every clause anew at every block.
Here the debt is cut by SORT OF CLAUSE: each premise beneath is a sentence on one clause, and most
are paid once for a kind, or once for all kinds, by what the block's text leaves of the record.

What is said. `rowsHeld_of_groups`, `membersHeld_of_groups`: the two clauses read of the record the
statement's groups (and the book's places) alone. `pubHeld_of`: the public items behind, from "kept"
and "made". `onAt_step_held`: AT A ROW THAT CLOSES AND OPENS NO CLASS OF ROWS AND NO PIN the promise
behind follows from the promise in front and: a mark stays; "decodes" rides; the book-keeping behind
(the block's own); `rowsHeld` and `membersHeld` AT THE OPEN SET IN FRONT ride; "in order" rides; the
public items (kept or made), their Bools and what they say beside; where the book stands behind; of
the open pins' tenants: held rides; shown and no collision ride as a pair. `onAt_step_quiet`: the
same under stronger premises: the statement's groups and the book's places are as they were, whole;
shown and no collision ride each alone.

Limits. (1) A rule over letters: it pays nothing by itself. (2) At a row that closes or opens a
class of rows or a pin (a sending, a switch, the one equation, a closing, the last proximity test)
`rowsHeld`, `membersHeld` and the samples' clauses are the block's own to pay: nothing here. (3) The
premises on `Mg`'s letters (in order; a public item; held; shown; no collision; decodes) can be paid
only at a filling: "the filling reads none of the fields that the block turns".

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.BordersKeep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

section
variable {P W : Type} (N : Numbers)

/-- `rowsHeld` reads of the record the statement's groups alone. -/
theorem rowsHeld_of_groups (O : List Item) (s s' : S) (h : s'.st.groups = s.st.groups) :
    rowsHeld N O s' = rowsHeld N O s := by
  unfold rowsHeld
  rw [h]

/-- `membersHeld` reads of the record the statement's groups and the book's places alone. -/
theorem membersHeld_of_groups (O : List Item) (s s' : S) (h : s'.st.groups = s.st.groups)
    (hb : s'.book.place = s.book.place) : membersHeld N O s' = membersHeld N O s := by
  unfold membersHeld
  rw [h, hb]

/-- The public items behind a block: each is kept, or made. -/
theorem pubHeld_of (Mg : Meaning P W) (O O' : List Item) (Q Q' : List Pub) (a b : P × S)
    (h : pubHeld Mg O Q a = true)
    (hk : ∀ q ∈ Q' ++ pubOfItems O', q ∈ Q ++ pubOfItems O → Mg.pub q a = true →
      Mg.pub q b = true)
    (hm : ∀ q ∈ Q' ++ pubOfItems O', ¬ q ∈ Q ++ pubOfItems O → Mg.pub q b = true) :
    pubHeld Mg O' Q' b = true := by
  unfold pubHeld at h ⊢
  apply List.all_eq_true.2
  intro q hq
  by_cases hin : q ∈ Q ++ pubOfItems O
  · exact hk q hq hin (List.all_eq_true.1 h q hin)
  · exact hm q hq hin

/-- **THE PROMISE RIDES PAST A BLOCK WHOSE ROW CLOSES AND OPENS NO CLASS OF ROWS AND NO PIN**,
clause by clause: THE LEAST THAT THE PROOF SPENDS. p, O, Q: the place, the open items and the open
public items at the border in front; p', Q': behind. `rowsHeld` and `membersHeld` are asked to ride
AT THE OPEN SET O (a block may turn groups or places that O does not read); "shown" and "no
collision" ride as a pair; EVERY PREMISE BUT THE FIRST TWO HAS "no mark in front, no mark behind" IN
HAND: at a marked record behind the promise asks "decodes" alone. -/
theorem onAt_step_held (Mg : Meaning P W) (links : List ModelPart) (p p' : Option Place)
    (O : List Item) (Q Q' : List Pub) (r : BlockRow) (a b : P × S) (y y' : Strs)
    (hq : quietRow r = true) (ha : onAt N Mg links p O Q a y)
    (hMark : a.2.failed ≠ none → b.2.failed ≠ none)
    (hDec : Mg.decodes a y → Mg.decodes b y')
    (hShape : a.2.failed = none → b.2.failed = none → shapeAt links p' b.2 = true)
    (hR : a.2.failed = none → b.2.failed = none → rowsHeld N O a.2 = true →
      rowsHeld N O b.2 = true)
    (hM : a.2.failed = none → b.2.failed = none → membersHeld N O a.2 = true →
      membersHeld N O b.2 = true)
    (hIn : a.2.failed = none → b.2.failed = none → Mg.inOrder a = true → Mg.inOrder b = true)
    (hPub : a.2.failed = none → b.2.failed = none → pubHeld Mg O Q a = true →
      pubHeld Mg (stepOpen O r) Q' b = true)
    (hBook : a.2.failed = none → b.2.failed = none → bookAt N p a.2 = true →
      bookAt N p' b.2 = true)
    (hPP : a.2.failed = none → b.2.failed = none → (∀ q ∈ Q, Mg.pubP q a) →
      ∀ q ∈ Q', Mg.pubP q b)
    (hHeld : a.2.failed = none → b.2.failed = none → ∀ x ∈ sampledIn N O,
      Mg.held x.1 x.2 a = true → Mg.held x.1 x.2 b = true)
    (hSN : a.2.failed = none → b.2.failed = none → ∀ x ∈ sampledIn N O,
      Mg.shown x.1 x.2 y ∧ Mg.noColl x.1 x.2 a y → Mg.shown x.1 x.2 y' ∧ Mg.noColl x.1 x.2 b y') :
    onAt N Mg links p' (stepOpen O r) Q' b y' := by
  refine ⟨hDec ha.1, ?_⟩
  by_cases hb : b.2.failed = none
  · have hm : a.2.failed = none := Classical.byContradiction fun h => hMark h hb
    rcases ha.2 with hx | ⟨hB, hs, hall, hpp⟩
    · exact absurd hm hx
    · right
      simp only [Bool.and_eq_true] at hB
      obtain ⟨⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hB
      refine ⟨?_, ?_, ?_, hPP hm hb hpp⟩
      · rw [hShape hm hb, rowsHeld_step N O r hq, membersHeld_step N O r hq, hR hm hb h2,
          hM hm hb h3, hIn hm hb h4, hPub hm hb h5, hBook hm hb h6]
        rfl
      · rw [samplesHeld_step N Mg O r hq]
        unfold samplesHeld at hs ⊢
        apply List.all_eq_true.2
        intro x hx
        exact hHeld hm hb x hx (List.all_eq_true.1 hs x hx)
      · intro x hx
        rw [sampledIn_step N O r hq] at hx
        exact hSN hm hb x hx (hall x hx)
  · left
    exact hb

/-- The same, where the block leaves the statement's groups and the book's places whole, and "shown"
and "no collision" ride each alone. -/
theorem onAt_step_quiet (Mg : Meaning P W) (links : List ModelPart) (p p' : Option Place)
    (O : List Item) (Q Q' : List Pub) (r : BlockRow) (a b : P × S) (y y' : Strs)
    (hq : quietRow r = true) (ha : onAt N Mg links p O Q a y)
    (hMark : a.2.failed ≠ none → b.2.failed ≠ none)
    (hDec : Mg.decodes a y → Mg.decodes b y')
    (hShape : a.2.failed = none → shapeAt links p' b.2 = true)
    (hG : b.2.st.groups = a.2.st.groups) (hB : b.2.book.place = a.2.book.place)
    (hIn : Mg.inOrder a = true → Mg.inOrder b = true)
    (hPub : a.2.failed = none → pubHeld Mg O Q a = true →
      pubHeld Mg (stepOpen O r) Q' b = true)
    (hBook : a.2.failed = none → bookAt N p a.2 = true → bookAt N p' b.2 = true)
    (hPP : a.2.failed = none → (∀ q ∈ Q, Mg.pubP q a) → ∀ q ∈ Q', Mg.pubP q b)
    (hHeld : ∀ x ∈ sampledIn N O, Mg.held x.1 x.2 a = true → Mg.held x.1 x.2 b = true)
    (hSh : ∀ x ∈ sampledIn N O, Mg.shown x.1 x.2 y → Mg.shown x.1 x.2 y')
    (hNc : ∀ x ∈ sampledIn N O, Mg.noColl x.1 x.2 a y → Mg.noColl x.1 x.2 b y') :
    onAt N Mg links p' (stepOpen O r) Q' b y' :=
  onAt_step_held N Mg links p p' O Q Q' r a b y y' hq ha hMark hDec (fun hm _ => hShape hm)
    (fun _ _ h => by rw [rowsHeld_of_groups N O a.2 b.2 hG]; exact h)
    (fun _ _ h => by rw [membersHeld_of_groups N O a.2 b.2 hG hB]; exact h) (fun _ _ => hIn)
    (fun hm _ => hPub hm) (fun hm _ => hBook hm) (fun hm _ => hPP hm) (fun _ _ => hHeld)
    (fun _ _ x hx h => ⟨hSh x hx h.1, hNc x hx h.2⟩)

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.pubHeld_of
#print axioms VerifiableInference.Desc.First.onAt_step_held
#print axioms VerifiableInference.Desc.First.onAt_step_quiet
