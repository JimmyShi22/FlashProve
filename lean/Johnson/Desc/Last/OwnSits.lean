-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/OwnSits.lean: A TEST WITH CODE ON THE FIRST CHAIN'S STATE: the own group that is
handed to the last chain has just two members: the index masks' message and W, each at the plan's
place in the book and with the plan's shape. Definitions, and one statement with its proof. THIN: it
imports Johnson/Desc/Third/Border.lean alone.

Why. The last chain's laws ask WHICH messages the own group holds that the first chain hands on, and
where they sit. At the first chain's last border nothing in the first table's promise says so: its
clause on groups' members speaks of the segments of which a class of rows is open, and there none
is. `ownTwoB` (Johnson/Desc/Last/OwnTwo.lean) says how many members there are. This test says which,
so that it can ride as one named item of the promise and be run at a chain's borders.

Main names (namespace `VerifiableInference.Desc.Last`).
  `OwnSeats`: four public values: the two places (tree's place in the book, part), the two shapes.
  **`ownSitsB V s`**: where `firstOfS s` hands something: the group at the number that is handed as
    the own group's is there and its members are two, in the order of their numbers: the first has
    the place `V.index` in the handed book and the shape `V.indexShape`, the second `V.w` and
    `V.wShape`. Where nothing is handed: yes.
  `OwnSits V f`: the same as a sentence on what is handed. **`ownSitsB_iff`**.

Limits. IT HAS RUN AT NO STATE. Idle at every border in front of the block that lays W's number. The
place is the book's own pair (tree's place, part): that the tree there bears a given number is
another item's ("K12.bookInOrder"). It asks that the index masks' message is the elder of the two.
Who earns and keeps it: nobody yet. Nothing on soundness or on hiding.

-/
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third

/-- The plan's four values: where the index masks' message and W sit in the first chain's book, and
their shapes. -/
structure OwnSeats where
  index : Nat × Nat
  w : Nat × Nat
  indexShape : OracleShape
  wShape : OracleShape

/-- **What is handed holds the own group with just these two members.** -/
def OwnSits (V : OwnSeats) (f : FirstEnd₃) : Prop :=
  ∃ (G : Group) (i₁ i₂ : Nat), f.st.groups[f.own]? = some G ∧ G.members.toList = [i₁, i₂] ∧
    f.book.place[i₁]? = some V.index ∧ f.book.place[i₂]? = some V.w ∧
    (f.st.oracles[i₁]?).map (·.shape) = some V.indexShape ∧
    (f.st.oracles[i₂]?).map (·.shape) = some V.wShape

/-- The same as a test with code, on what is handed. -/
def ownSitsF (V : OwnSeats) (f : FirstEnd₃) : Bool :=
  match f.st.groups[f.own]? with
  | some G =>
    match G.members.toList with
    | [i₁, i₂] =>
      decide (f.book.place[i₁]? = some V.index) && decide (f.book.place[i₂]? = some V.w) &&
        decide ((f.st.oracles[i₁]?).map (·.shape) = some V.indexShape) &&
        decide ((f.st.oracles[i₂]?).map (·.shape) = some V.wShape)
    | _ => false
  | none => false

/-- **The test on the first chain's state.** -/
def ownSitsB (V : OwnSeats) (s : First.S) : Bool :=
  match firstOfS s with
  | some f => ownSitsF V f
  | none => true

theorem ownSitsF_iff (V : OwnSeats) (f : FirstEnd₃) : ownSitsF V f = true ↔ OwnSits V f := by
  unfold ownSitsF OwnSits
  constructor
  · intro h
    split at h
    · rename_i G hG
      split at h
      · rename_i i₁ i₂ hm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨G, i₁, i₂, hG, hm, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      · cases h
    · cases h
  · rintro ⟨G, i₁, i₂, hG, hm, h1, h2, h3, h4⟩
    rw [hG]
    simp only [hm, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- **It says yes exactly where whatever is handed holds the two.** -/
theorem ownSitsB_iff (V : OwnSeats) (s : First.S) :
    ownSitsB V s = true ↔ ∀ f, firstOfS s = some f → OwnSits V f := by
  unfold ownSitsB
  cases h : firstOfS s with
  | none => exact ⟨fun _ _ hf => (nomatch hf), fun _ => rfl⟩
  | some f =>
    exact ⟨fun hb g hg => (Option.some.inj hg) ▸ (ownSitsF_iff V f).1 hb,
      fun H => (ownSitsF_iff V f).2 (H f rfl)⟩

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.ownSitsF_iff
#print axioms VerifiableInference.Desc.Last.ownSitsB_iff
