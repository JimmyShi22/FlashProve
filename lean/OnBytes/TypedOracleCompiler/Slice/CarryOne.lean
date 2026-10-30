-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/CarryOne.lean: the maps of shapes of OnBytes/Slice/ShapeMap.lean between the
sibling's rounds and the library's.

"The library" is the Lean library of the soundness road (Iop/, Compile/, Run/); "the sibling" is a
second form of that road under OnBytes/TypedOracleCompiler/. The sibling's rounds' data hold a list of trees a
round, the library's at most one. The two give shapes that are alike and not equal as types. These
maps go from the sibling's shape (new) to the library's (old), so that round-by-round soundness
proved over the library's rounds can pass to a protocol over the sibling's (`ShapeMap.sound`).
 - `rOne C d`: ONE TREE A ROUND: from the sibling's round at the library's data (`ofLib d`) to the
   library's round at d. The sibling's positions are `PosT d.tree.toList` (for a tree s:
   `Fin (2 ^ s.a) ⊕ Empty`), the library's `Fin (posN d.tree)`; plain part and verifier's message
   are one type in both;
 - `sOne C ds`: a list of rounds; `sOneUp C ds`: with the round in front: the shape of the sibling's
   and of the library's `(skeletonOverBothExternalStrings …).up.loc`; `flat_sOne`, `firstZero_sOne`;
 - `plL`, `plR`, `gots_app`: a plain message over two lists of items, cut in two; `old_map`;
 - `Blind C d r`: the kit of verifier's messages does not look at how many roots d's entry counts;
   `blindP`: the kit of hash blocks does not;
 - `firstOf e₁ it₁ s`: the library's data of a first piece: entry e₁, kind "nothing", items it₁,
   tree s, no opening; `roundDataFromBothPieces r it₁ s d`: the sibling's data of the round as one: d's entry with r
   roots, d's kind, the items of both pieces, the tree s in front of d's own, d's openings;
   `joined_eq`: it is the sibling's `joinRD` of the two pieces;
 - `rTwo`: THE ROUND OF TWO ROOTS: from the sibling's one round `roundDataFromBothPieces r it₁ s d` to the library's
   two rounds `firstOf e₁ it₁ s` and d;
 - `sTwoL C B e₁ it₁ s d r bl u A`: a list of rounds with one such round.

Main definitions: `posOne`, `symOne`, `rOne`, `sOne`, `sOneUp`, `plL`, `plR`, `Blind`, `blindP`,
`firstOf`, `roundDataFromBothPieces`, `rTwo`, `sTwoL`.
Main theorems: `flat_sOne`, `firstZero_sOne`, `gots_app`, `old_map`, `joined_eq`.

Not claimed. MAPS ALONE: no protocol is named, and `ShapeMap.sound` is not applied here
(OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean does, for `skeletonOverBothExternalStrings`, where no round sends more than one root). At
the round of two roots its
hypothesis is not to be looked for with one and the same decision on both sides. In the protocols
meant (`Plain3`, `skeletonOverBothExternalStrings`) the decision sees one record for each round of the list; the library's
list has one round more, so every later round stands one place further on, and an opening of the
stored table names its round by its place. A decision that counts the records tells the two apart.
So the hypothesis is to be stated for a pair of decisions and a pair of lists of openings. None of
this is proved here, and none of it is shown in this library. For that hypothesis u has to pass the
first
piece's test of work. That the first piece's count (the number of verifier's messages that may let a
prover that has lost escape) is 0 (`ShapeMap.FirstZero`) is a matter of the counts over the
library's rounds. At most two trees in the round as one (d has at most one). The sibling's `cutRD`
(OnBytes/TypedOracleCompiler/Run/PlanQJoin.lean: no item in the first piece; the round's own entry and all items in
the second) is the case it₁ = [] and r = d.entry.roots; no lemma says so. That the cut whose first
piece has the items up to the first root, with it, is another case is not shown in this library.
Nothing on seams or on
three stretches.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.ShapeMap
import OnBytes.TypedOracleCompiler.Run.PlanQJoin
import Run.PlanPull

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.CarryOne
open _root_.Iop (Err)
open OnBytes.Slice.ShapeMap TypedOracleCompiler.Run

/-- A position of the library's round, as one of the sibling's: the first tree's. -/
def posOne : (t : Option _root_.Fmt.Shape) → Fin (_root_.Run.PQ.posN t) → PQ.PosT t.toList
  | none, x => x.elim0
  | some _, x => .inl x

/-- The symbol at it: a column of the tree's width, as it is. -/
def symOne : (t : Option _root_.Fmt.Shape) → (x : Fin (_root_.Run.PQ.posN t)) →
    PQ.SymT t.toList (posOne t x) → (Fin (_root_.Run.PQ.colW t) → UInt64)
  | none, x, _ => x.elim0
  | some _, _, c => c

/-- One tree a round: from the sibling's round at the library's data to the library's round. The
oracle is read at the first tree's positions; plain part and verifier's message are the same. -/
def rOne (C : _root_.Run.PQ.CK) (d : _root_.Run.PQ.RD) :
    RMap (PQ.roundS C (PQ.ofLib d)).up (_root_.Run.PQ.roundS C d).up where
  msg := fun m => (fun x => symOne d.tree x (m.1 (posOne d.tree x)), m.2)
  chal := Equiv.refl _

/-- A list of rounds. -/
def sOne (C : _root_.Run.PQ.CK) : (ds : List _root_.Run.PQ.RD) →
    SMap (PQ.uL C (ds.map PQ.ofLib)) (_root_.Run.PQ.uL C ds)
  | [] => .nil
  | d :: ds => .one (rOne C d) (sOne C ds)

/-- The same with the round in front, which is one round in both. -/
def sOneUp (C : _root_.Run.PQ.CK) (ds : List _root_.Run.PQ.RD) :
    SMap (_root_.Run.Twin.up (PQ.SOf C (ds.map PQ.ofLib)))
      (_root_.Run.Twin.up (_root_.Run.PQ.SOf C ds)) :=
  .one (RMap.refl _) (sOne C ds)

/-- No new round of `sOne` stands over two old ones. -/
theorem flat_sOne (C : _root_.Run.PQ.CK) : ∀ ds : List _root_.Run.PQ.RD, (sOne C ds).Flat
  | [] => trivial
  | _ :: ds => flat_sOne C ds

/-- So nothing is asked of the counts. -/
theorem firstZero_sOne (C : _root_.Run.PQ.CK) (ds : List _root_.Run.PQ.RD)
    (ε : Err (_root_.Run.PQ.uL C ds)) : FirstZero (sOne C ds) ε :=
  firstZero_of_flat _ (flat_sOne C ds) ε

/-! ## A plain part over two lists of items -/

/-- The part of a plain message over the first of two lists of items. -/
def plL : (l₁ l₂ : List _root_.Fmt.Item) → _root_.Run.PQ.PlainOf (l₁ ++ l₂) →
    _root_.Run.PQ.PlainOf l₁
  | [], _, _ => ()
  | .root :: l₁, l₂, x => plL l₁ l₂ x
  | .f :: l₁, l₂, (x : UInt64 × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => (x.1, plL l₁ l₂ x.2)
  | .word :: l₁, l₂, (x : UInt64 × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => (x.1, plL l₁ l₂ x.2)
  | .e :: l₁, l₂, (x : _root_.Fmt.Ext × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => (x.1, plL l₁ l₂ x.2)
  | .answer :: l₁, l₂, (x : _root_.Fmt.Ext × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) =>
      (x.1, plL l₁ l₂ x.2)

/-- The part over the second list. -/
def plR : (l₁ l₂ : List _root_.Fmt.Item) → _root_.Run.PQ.PlainOf (l₁ ++ l₂) →
    _root_.Run.PQ.PlainOf l₂
  | [], _, x => x
  | .root :: l₁, l₂, x => plR l₁ l₂ x
  | .f :: l₁, l₂, (x : UInt64 × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => plR l₁ l₂ x.2
  | .word :: l₁, l₂, (x : UInt64 × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => plR l₁ l₂ x.2
  | .e :: l₁, l₂, (x : _root_.Fmt.Ext × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => plR l₁ l₂ x.2
  | .answer :: l₁, l₂, (x : _root_.Fmt.Ext × _root_.Run.PQ.PlainOf (l₁ ++ l₂)) => plR l₁ l₂ x.2

/-- The values of a plain message over two lists of items: those of the two parts, in order. -/
theorem gots_app : ∀ (l₁ l₂ : List _root_.Fmt.Item) (x : _root_.Run.PQ.PlainOf (l₁ ++ l₂)),
    _root_.Run.PQ.PlainOf.gots (l₁ ++ l₂) x =
      _root_.Run.PQ.PlainOf.gots l₁ (plL l₁ l₂ x) ++ _root_.Run.PQ.PlainOf.gots l₂ (plR l₁ l₂ x)
  | [], _, _ => rfl
  | .root :: l₁, l₂, x => gots_app l₁ l₂ x
  | .f :: l₁, l₂, x => congrArg (List.cons _) (gots_app l₁ l₂ x.2)
  | .word :: l₁, l₂, x => congrArg (List.cons _) (gots_app l₁ l₂ x.2)
  | .e :: l₁, l₂, x => congrArg (List.cons _) (gots_app l₁ l₂ x.2)
  | .answer :: l₁, l₂, x => congrArg (List.cons _) (gots_app l₁ l₂ x.2)

/-- The old plain part of an image is the image of the old plain part. -/
theorem old_map {W P P' : Type} (f : P → P') : ∀ (b : ℕ) (x : _root_.Iop.GPlain W b P),
    _root_.Iop.GPlain.old (_root_.Iop.GPlain.map f x) = f (_root_.Iop.GPlain.old x)
  | 0, _ => rfl
  | _ + 1, (_, _) => rfl

/-! ## The round of two roots -/

/-- The kit does not look at how many roots d's entry counts: the verifier's messages under d's
entry with r roots and under d's entry are in bijection, with the same test of work and the same
drawn values. -/
structure Blind (C : _root_.Run.PQ.CK) (d : _root_.Run.PQ.RD) (r : ℕ) where
  /-- the bijection -/
  κ : _root_.Iop.GChal d.entry.work (C.Ch { d.entry with roots := r } d.kind) ≃
    _root_.Iop.GChal d.entry.work (C.Ch d.entry d.kind)
  /-- the same test of work -/
  pass : ∀ c, _root_.Iop.GChal.pass (κ c) = _root_.Iop.GChal.pass c
  /-- the same drawn values -/
  dr : ∀ c, C.dr d.entry d.kind (_root_.Iop.GChal.old (κ c)) =
    C.dr { d.entry with roots := r } d.kind (_root_.Iop.GChal.old c)

/-- The kit of hash blocks does not look at it: the two types are one. -/
def blindP (f : _root_.Fmt.Fld) (d : _root_.Run.PQ.RD) (r : ℕ) : Blind (_root_.Run.ckP f) d r :=
  ⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩

/-- The library's data of the first piece of a round that is written as two: under the entry e₁, of
the kind "nothing", with the items it₁, the tree s, no opening. -/
def firstOf (e₁ : _root_.Fmt.Entry) (it₁ : List _root_.Fmt.Item) (s : _root_.Fmt.Shape) :
    _root_.Run.PQ.RD :=
  ⟨e₁, .nothing, it₁, some s, []⟩

/-- The sibling's data of the round as one, from the first piece's items and tree and the second
piece's data d: d's entry with r roots; d's kind; the items of both; the tree s in front of d's own;
d's openings. -/
def roundDataFromBothPieces (r : ℕ) (it₁ : List _root_.Fmt.Item) (s : _root_.Fmt.Shape) (d : _root_.Run.PQ.RD) :
    PQ.RD :=
  ⟨{ d.entry with roots := r }, d.kind, it₁ ++ d.items, s :: d.tree.toList, d.opens⟩

/-- The round of two roots: from the sibling's ONE round to the library's TWO pieces. The oracle
is read tree by tree; the plain part is cut along the two lists of items; the first piece has the
fixed nonce, and its verifier's message is taken at u. For the hypothesis of `ShapeMap.sound` u has
to pass the first piece's test of work (`GChal.pass`; at e₁.work = 0 there is no test bit), and the
record that the view over the library's rounds has for the first piece depends on u. -/
def rTwo (C : _root_.Run.PQ.CK) (e₁ : _root_.Fmt.Entry) (it₁ : List _root_.Fmt.Item)
    (s : _root_.Fmt.Shape) (d : _root_.Run.PQ.RD) (r : ℕ) (bl : Blind C d r)
    (u : (_root_.Run.PQ.roundS C (firstOf e₁ it₁ s)).up.Chal) :
    RMap2 (PQ.roundS C (roundDataFromBothPieces r it₁ s d)).up (_root_.Run.PQ.roundS C (firstOf e₁ it₁ s)).up
      (_root_.Run.PQ.roundS C d).up where
  msg1 := fun m => (fun x => m.1 (.inl x),
    _root_.Iop.GPlain.mk e₁.work
      (plL it₁ d.items (_root_.Iop.GPlain.old (b := d.entry.work) m.2)) default)
  u := u
  msg2 := fun m => (fun x => symOne d.tree x (m.1 (.inr (posOne d.tree x))),
    _root_.Iop.GPlain.map (b := d.entry.work) (plR it₁ d.items) m.2)
  chal := bl.κ

/-- The round as one is the sibling's `joinRD` of the two pieces, under d's entry with r roots. -/
theorem joined_eq (e₁ : _root_.Fmt.Entry) (r : ℕ) (it₁ : List _root_.Fmt.Item)
    (s : _root_.Fmt.Shape) (d : _root_.Run.PQ.RD) :
    roundDataFromBothPieces r it₁ s d =
      PQ.joinRD { d.entry with roots := r } (PQ.ofLib (firstOf e₁ it₁ s)) (PQ.ofLib d) := rfl

/-- A list of rounds with one round of two roots: A, the round as one, B over the sibling; A,
the two pieces, B over the library. By recursion on A, so that both shapes are `uL` OF A LIST, as a
protocol has them. -/
def sTwoL (C : _root_.Run.PQ.CK) (B : List _root_.Run.PQ.RD) (e₁ : _root_.Fmt.Entry)
    (it₁ : List _root_.Fmt.Item) (s : _root_.Fmt.Shape) (d : _root_.Run.PQ.RD) (r : ℕ)
    (bl : Blind C d r) (u : (_root_.Run.PQ.roundS C (firstOf e₁ it₁ s)).up.Chal) :
    (A : List _root_.Run.PQ.RD) →
    SMap (PQ.uL C (A.map PQ.ofLib ++ roundDataFromBothPieces r it₁ s d :: B.map PQ.ofLib))
      (_root_.Run.PQ.uL C (A ++ firstOf e₁ it₁ s :: d :: B))
  | [] => .two (rTwo C e₁ it₁ s d r bl u) (sOne C B)
  | a :: A => .one (rOne C a) (sTwoL C B e₁ it₁ s d r bl u A)

end TypedOracleCompiler.Slice.CarryOne
