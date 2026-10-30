-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawAlike.lean: the one relation on contexts in which both laws on the program's
blocks are said: `Alike G d c c'`.

c and c' (`Ctx`, OnBytes/Iop/Ground.lean) are equal field by field, but for
  (i)   the digest in what a round of the view has drawn (`Fmt.Drawn.digest`), in the rounds still
        to come (`Chan.left`) and in the round that is open (`Chan.cur`): nothing is asked of it;
  (ii)  the two fields (root, start) of a source "given" (`Fmt.Src.given`), in every tree of the
        book and in every opening that a dry run has noted: they are asked to be in the relation G.
        A source "own n" goes with "own n" alone;
  (iii) if d = true: both runs are dry and keep no intermediate values.

Why one relation with two parameters.
  Law 2 ("blind") is `Alike` at G := any two (`AnyGiven`), d := false.
  Law 1 ("the descriptions are constants") is `Alike` at d := true. A second chain's dry run notes
  the sources of the trees that it takes over, and these hold roots and run values that were read.
  So its notes are no constants to the letter. With G := the graph of a renaming (tag ↦ what was
  read) the law says: the notes at the real reading are the constant notes, made at tags, with each
  tag replaced.

Main names. `OptAlike`, `LAlike`, `ArrAlike`: a relation on options, lists, arrays, entry by entry.
`SrcAlike G`, `DrawnAlike`, `RVAlike`, `NoteAlike G`, `TreeAlike G`, `BookAlike G`, `Alike G d`,
`AnyGiven`. Small laws on `ArrAlike`: size_eq, push, modify, refl, get, map_eq.

Not claimed. No block is named here. That a digest is there on both sides or on neither is not
asked. Nothing is asked of G.

-/
import OnBytes.TypedOracleCompiler.Laws.LawKit

namespace OnBytes.TwoLaws

open OnBytes

/-! ## Options, lists, arrays -/

inductive OptAlike {α : Type} (P : α → α → Prop) : Option α → Option α → Prop
  | none : OptAlike P none none
  | some {a b : α} : P a b → OptAlike P (some a) (some b)

theorem OptAlike.map {α : Type} {P : α → α → Prop} {x y : Option α} {f g : α → α}
    (h : OptAlike P x y) (hf : ∀ a b, P a b → P (f a) (g b)) : OptAlike P (x.map f) (y.map g) := by
  cases h with
  | none => exact .none
  | some k => exact .some (hf _ _ k)

theorem OptAlike.map_eq {α β : Type} {P : α → α → Prop} {x y : Option α} (h : OptAlike P x y)
    (f : α → β) (hf : ∀ a b, P a b → f a = f b) : x.map f = y.map f := by
  cases h with
  | none => rfl
  | some k => exact congrArg Option.some (hf _ _ k)

inductive LAlike {α : Type} (P : α → α → Prop) : List α → List α → Prop
  | nil : LAlike P [] []
  | cons {a b : α} {l l' : List α} : P a b → LAlike P l l' → LAlike P (a :: l) (b :: l')

theorem LAlike.refl {α : Type} {P : α → α → Prop} (h : ∀ a, P a a) : ∀ l, LAlike P l l
  | [] => .nil
  | a :: l => .cons (h a) (LAlike.refl h l)

theorem LAlike.append {α : Type} {P : α → α → Prop} {l l' m m' : List α} (h : LAlike P l l')
    (k : LAlike P m m') : LAlike P (l ++ m) (l' ++ m') := by
  induction h with
  | nil => exact k
  | cons a _ ih => exact .cons a ih

/-- Entry by entry; so the sizes are equal too (ArrAlike.size_eq). -/
def ArrAlike {α : Type} (P : α → α → Prop) (a b : Array α) : Prop :=
  ∀ i : Nat, OptAlike P a[i]? b[i]?

theorem ArrAlike.refl {α : Type} {P : α → α → Prop} (h : ∀ a, P a a) (a : Array α) :
    ArrAlike P a a := by
  intro i
  cases a[i]? with
  | none => exact .none
  | some x => exact .some (h x)

theorem ArrAlike.size_eq {α : Type} {P : α → α → Prop} {a b : Array α} (h : ArrAlike P a b) :
    a.size = b.size := by
  apply Nat.le_antisymm
  · have h1 := h b.size
    have e : b[b.size]? = none := by simp
    rw [e] at h1
    generalize e2 : a[b.size]? = x at h1
    cases h1
    simpa using e2
  · have h1 := h a.size
    have e : a[a.size]? = none := by simp
    rw [e] at h1
    generalize e2 : b[a.size]? = x at h1
    cases h1
    simpa using e2

theorem ArrAlike.push {α : Type} {P : α → α → Prop} {a b : Array α} {x y : α}
    (h : ArrAlike P a b) (hx : P x y) : ArrAlike P (a.push x) (b.push y) := by
  intro i
  rw [Array.getElem?_push, Array.getElem?_push, h.size_eq]
  split
  · exact .some hx
  · exact h i

theorem ArrAlike.modify {α : Type} {P : α → α → Prop} {a b : Array α} {f g : α → α} (j : Nat)
    (h : ArrAlike P a b) (hf : ∀ x y, P x y → P (f x) (g y)) :
    ArrAlike P (a.modify j f) (b.modify j g) := by
  intro i
  rw [Array.getElem?_modify, Array.getElem?_modify]
  split
  · exact (h i).map hf
  · exact h i

/-- What is one on both sides of P is one at each place of two arrays that are alike. -/
theorem ArrAlike.map_eq {α β : Type} {P : α → α → Prop} {a b : Array α} (h : ArrAlike P a b)
    (f : α → β) (hf : ∀ x y, P x y → f x = f y) (i : Nat) : a[i]?.map f = b[i]?.map f :=
  (h i).map_eq f hf

/-! ## The pieces of a context -/

/-- A source "own n" goes with itself alone; two sources "given" go together under G. -/
inductive SrcAlike (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop) :
    Fmt.Src → Fmt.Src → Prop
  | own (n : Nat) : SrcAlike G (.own n) (.own n)
  | given {r s r' s' : ByteArray} : G r s r' s' → SrcAlike G (.given r s) (.given r' s')

/-- Law 2's G: nothing is asked of two given sources. -/
def AnyGiven : ByteArray → ByteArray → ByteArray → ByteArray → Prop := fun _ _ _ _ => True

/-- Equal but for the digest. -/
structure DrawnAlike (a b : Fmt.Drawn) : Prop where
  elems : a.elems = b.elems
  poss : a.poss = b.poss
  trits : a.trits = b.trits

theorem DrawnAlike.refl (a : Fmt.Drawn) : DrawnAlike a a := ⟨rfl, rfl, rfl⟩

/-- A view's round: equal but for the digest drawn. -/
structure RVAlike (a b : Fmt.RoundView) : Prop where
  vals : a.vals = b.vals
  drawn : DrawnAlike a.drawn b.drawn

section G
variable (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop)

/-- One noted opening: one shape, sources that go together. -/
def OpenAlike (x y : Fmt.Shape × Fmt.Src) : Prop := x.1 = y.1 ∧ SrcAlike G x.2 y.2

/-- What a dry run has noted of a round: equal but for the given sources of its openings. -/
structure NoteAlike (a b : RoundNote) : Prop where
  entry : a.entry = b.entry
  kind : a.kind = b.kind
  items : a.items = b.items
  opens : LAlike (OpenAlike G) a.opens b.opens
  stored : a.stored = b.stored

/-- A tree of the book: equal but for a given source. -/
structure TreeAlike (a b : Tree) : Prop where
  shape : a.shape = b.shape
  number : a.number = b.number
  src : SrcAlike G a.src b.src
  parts : a.parts = b.parts
  oneList : a.oneList = b.oneList
  lists : a.lists = b.lists

/-- The book: tree by tree; the places are equal. -/
structure BookAlike (A B : TreeBook) : Prop where
  trees : ArrAlike (TreeAlike G) A.trees B.trees
  place : A.place = B.place

/-- The relation. See the file's head. -/
structure Alike (d : Bool) (c c' : Ctx) : Prop where
  dry : c.ch.dry = c'.ch.dry
  firstTree : c.ch.firstTree = c'.ch.firstTree
  samples : c.ch.samples = c'.ch.samples
  entries : c.ch.entries = c'.ch.entries
  left : LAlike RVAlike c.ch.left c'.ch.left
  cur : OptAlike RVAlike c.ch.cur c'.ch.cur
  opened : c.ch.opened = c'.ch.opened
  roots : c.ch.roots = c'.ch.roots
  last : c.ch.last = c'.ch.last
  askedRows : c.ch.askedRows = c'.ch.askedRows
  items : c.ch.items = c'.ch.items
  noted : ArrAlike (NoteAlike G) c.ch.noted c'.ch.noted
  st : c.st = c'.st
  book : BookAlike G c.book c'.book
  notes : c.notes = c'.notes
  keepNotes : c.keepNotes = c'.keepNotes
  failed : c.failed = c'.failed
  isDry : d = true → c.ch.dry = true ∧ c.keepNotes = false

end G

end OnBytes.TwoLaws
