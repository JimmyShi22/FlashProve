-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LeafBodies.lean: how a symbol of a prover's oracle is written into the body of a leaf,
and read back, for the three files' protocols: a body is a string of bits, the leaf's own string as
the format hashes it between the start and the salt, for a tree of a run.

A wire of the three files' protocols asks for each protocol a map from (position, symbol) to bodies
and a reading back, with the law that what is written is read back. Here both are made round by
round, for any list of rounds, and laid together along the lists' joins.

A symbol at a position is written as what the library's code of one tree's leaves (`Run.PQ.leaf1`,
Run/PageQChain.lean) writes at that position's own tree: the label with the tree's number, width and
the salt's words, the index 2^depth + place, the column, the fill (`leaf1_fit`, Run/PageQFit.lean).
A body is read at a position by that same tree's code, and is refused if its place is not the
position's: two places of one tree have two bodies. Over trees a body is not one to one: it holds
the number in the tree's label, its width, its depth and the place, and two trees can bear one
number; what parts them in the programs is the start, which is no part of a body.
That code writes the number 164, whatever the shape's mark `stored` says; the format writes 174 for
a tree so marked. So a body is the format's string for a tree of a run (`stored = false`) alone; no
theorem here says that of any data.

Main names.
  `RCode Bd r`, `SCode Bd s`: the two maps for a round r; for a list of rounds s, round by round.
  `SCode.emb`, `SCode.prj`: the two maps on the positions of the list. `SCode.prj_emb`: what is
    written is read back, if that holds round by round (`SCode.OK`).
  `SCode.app`, `SCode.app_ok`: two lists laid behind each other. `RCode.none`: a round without
    positions.
  `emb1 salt t`, `prj1 salt t`: the two maps of one tree's leaves. `prj1_emb1`: what is written is
    read back, and `emb1_fit`: the body is the bits of the format's label and of column and fill,
    both under "not deeper than 63".
  `scL salt C ds`, `scLink salt C ds`: at the library's rounds' data, a tree a round, without and
    with the round in front (an entry file's protocol). `scLink_ok`.
  `embTs salt ts`, `prjTs salt ts`, `scT salt C ds`: at rounds' data with a list of trees a round.
    `scT_ok`.
  `scWhole salt C D tF tJ t3`: at the rounds of a whole file (a key file's, a proof file's
    protocol). `scWhole_ok`.

Limits: the law, and for one tree what a body is; that is not said again here for a list. Nothing on
the stored tables' symbols, on salts, on hashes, on soundness. Where a tree is deeper than 63 its
code writes nothing and the body is the empty string.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Whole
import Run.PageQFit
import Run.OneIsTypedLeaf

set_option autoImplicit false

namespace OnBytes.Flat
open Iop _root_.Run _root_.Run.PQ OnBytes.Maker

/-! ## Any list of rounds -/

/-- The two maps for a round. -/
structure RCode (Bd : Type) (r : Round) where
  emb : (p : r.Pos) → r.Sym p → Bd
  prj : (p : r.Pos) → Bd → Option (r.Sym p)

/-- What is written is read back. -/
def RCode.OK {Bd : Type} {r : Round} (c : RCode Bd r) : Prop := ∀ p a, c.prj p (c.emb p a) = some a

/-- A round without positions. -/
def RCode.none (Bd : Type) (r : Round) (h : r.Pos → Empty) : RCode Bd r :=
  ⟨fun p => (h p).elim, fun p => (h p).elim⟩

/-- A round without positions has the law. -/
theorem RCode.none_ok (Bd : Type) (r : Round) (h : r.Pos → Empty) : (RCode.none Bd r h).OK :=
  fun p => (h p).elim

/-- The two maps for a list of rounds, round by round. -/
def SCode (Bd : Type) : Shape → Type
  | [] => Unit
  | r :: s => RCode Bd r × SCode Bd s

namespace SCode
variable {Bd : Type}

/-- What is written is read back, round by round. -/
def OK : (s : Shape) → SCode Bd s → Prop
  | [], _ => True
  | _ :: s, (c, cs) => c.OK ∧ OK s cs

/-- A symbol at a position of the list, as a body. -/
def emb : (s : Shape) → SCode Bd s → (p : OPos s) → OSym s p → Bd
  | _ :: _, (c, _), .inl p, a => c.emb p a
  | _ :: s, (_, cs), .inr q, a => emb s cs q a

/-- A body, read at a position of the list. -/
def prj : (s : Shape) → SCode Bd s → (p : OPos s) → Bd → Option (OSym s p)
  | _ :: _, (c, _), .inl p, b => c.prj p b
  | _ :: s, (_, cs), .inr q, b => prj s cs q b

/-- What is written is read back. -/
theorem prj_emb : ∀ (s : Shape) (cs : SCode Bd s), OK s cs →
    ∀ (p : OPos s) (a : OSym s p), prj s cs p (emb s cs p a) = some a
  | _ :: _, (_, _), h, .inl p, a => h.1 p a
  | _ :: s, (_, cs), h, .inr q, a => prj_emb s cs h.2 q a

/-- Two lists laid behind each other. -/
def app : (s t : Shape) → SCode Bd s → SCode Bd t → SCode Bd (s ++ t)
  | [], _, _, ct => ct
  | _ :: s, t, (c, cs), ct => (c, app s t cs ct)

/-- Two lists that have the law, laid behind each other, have it. -/
theorem app_ok : ∀ (s t : Shape) (cs : SCode Bd s) (ct : SCode Bd t), OK s cs → OK t ct →
    OK (s ++ t) (app s t cs ct)
  | [], _, _, _, _, ht => ht
  | _ :: s, t, (_, cs), ct, hs, ht => ⟨hs.1, app_ok s t cs ct hs.2 ht⟩

end SCode

/-! ## One tree's leaves -/

/- salt: the length of a file's salt, in bytes -/
variable (salt : ℕ)

/-- A leaf's own string; the empty string where the tree's code writes nothing. -/
def emb1 (t : Option Fmt.Shape) (x : Fin (posN t)) (col : Fin (colW t) → UInt64) : List Bool :=
  ((leaf1 t salt).put (x, col)).getD []

/-- A string read at a place by the tree's code: the column, if the place is that one. -/
def prj1 (t : Option Fmt.Shape) (x : Fin (posN t)) (b : List Bool) :
    Option (Fin (colW t) → UInt64) :=
  ((leaf1 t salt).parse b).bind fun z => if z.1 = x then some z.2 else none

/-- What is written is read back, if the tree is not deeper than 63. -/
theorem prj1_emb1 (t : Option Fmt.Shape) (ht : posN t + posN t ≤ 2 ^ 64) (x : Fin (posN t))
    (col : Fin (colW t) → UInt64) : prj1 salt t x (emb1 salt t x col) = some col := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (leaf1_some t salt ht (x, col))
  unfold prj1 emb1
  rw [hm]
  show ((leaf1 t salt).parse m).bind (fun z => if z.1 = x then some z.2 else none) = some col
  rw [(leaf1 t salt).parse_put _ m hm]
  exact if_pos rfl

/-- The body is the bits of the format's label under the number 164, with the tree's numbers and the
index, and of column and fill, if the tree is not deeper than 63. The format writes that number for
a tree of a run (`stored = false`). -/
theorem emb1_fit (t : Option Fmt.Shape) (ht : posN t + posN t ≤ 2 ^ 64) (x : Fin (posN t))
    (col : Fin (colW t) → UInt64) :
    emb1 salt t x col =
      bytesToBits (Fmt.label 164 (Fmt.leafPlace (trNo t) (colW t) (salt / 8)) (posN t + x.val)) ++
        bytesToBits
          (Fmt.colBytes (List.ofFn col) ++ Fmt.zeroBytes (Fmt.fillLen (colW t) salt)) := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (leaf1_some t salt ht (x, col))
  unfold emb1
  rw [hm]
  exact leaf1_fit t salt x col m hm

/-! ## The library's rounds' data: a tree a round -/

variable (C : CK)

/-- The two maps at the library's rounds' data. -/
def scL : (ds : List RD) → SCode (List Bool) (uL C ds)
  | [] => ()
  | d :: ds => (⟨fun x col => emb1 salt d.tree x col, fun x b => prj1 salt d.tree x b⟩, scL ds)

/-- What is written is read back, if no tree of the rounds' data is deeper than 63. -/
theorem scL_ok : ∀ (ds : List RD), (∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64) →
    SCode.OK (uL C ds) (scL salt C ds)
  | [], _ => trivial
  | d :: ds, h => ⟨fun x col => prj1_emb1 salt d.tree (h d (List.mem_cons_self ..)) x col,
      scL_ok ds fun d hd => h d (List.mem_cons_of_mem _ hd)⟩

/-- The same with the round in front: the rounds of an entry file's protocol. -/
def scLink (ds : List RD) : SCode (List Bool) (Twin.up (SOf C ds)) :=
  (RCode.none _ _ fun p => p, scL salt C ds)

/-- What is written is read back at an entry file's rounds, if no tree of the rounds' data is deeper
than 63. -/
theorem scLink_ok (ds : List RD) (h : ∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64) :
    SCode.OK (Twin.up (SOf C ds)) (scLink salt C ds) :=
  ⟨RCode.none_ok _ _ _, scL_ok salt C ds h⟩

/-! ## Rounds' data with a list of trees a round -/

/-- A symbol at a position of a round, as a body: by its own tree's code. -/
def embTs : (ts : List Fmt.Shape) → (p : PosT ts) → SymT ts p → List Bool
  | s :: _, .inl x, col => emb1 salt (some s) x col
  | _ :: ts, .inr p, col => embTs ts p col

/-- A body read at a position of a round: by its own tree's code. -/
def prjTs : (ts : List Fmt.Shape) → (p : PosT ts) → List Bool → Option (SymT ts p)
  | s :: _, .inl x, b => prj1 salt (some s) x b
  | _ :: ts, .inr p, b => prjTs ts p b

/-- What is written at a position of a round is read back, if no tree of the list is deeper than
63. -/
theorem prjTs_embTs : ∀ (ts : List Fmt.Shape), (∀ s ∈ ts, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
    ∀ (p : PosT ts) (a : SymT ts p), prjTs salt ts p (embTs salt ts p a) = some a
  | s :: _, h, .inl x, a => prj1_emb1 salt (some s) (h s (List.mem_cons_self ..)) x a
  | _ :: ts, h, .inr p, a => prjTs_embTs ts (fun s hs => h s (List.mem_cons_of_mem _ hs)) p a

/-- The two maps at rounds' data with a list of trees a round. -/
def scT : (ds : List RDT) → SCode (List Bool) (uLT C ds)
  | [] => ()
  | d :: ds => (⟨fun p a => embTs salt d.trees p a, fun p b => prjTs salt d.trees p b⟩, scT ds)

/-- What is written is read back, if no tree of any round's list is deeper than 63. -/
theorem scT_ok : ∀ (ds : List RDT), (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
    SCode.OK (uLT C ds) (scT salt C ds)
  | [], _ => trivial
  | d :: ds, h => ⟨fun p a => prjTs_embTs salt d.trees (h d (List.mem_cons_self ..)) p a,
      scT_ok ds fun d hd => h d (List.mem_cons_of_mem _ hd)⟩

/-! ## A whole file -/

section
variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- The two maps at the rounds of a whole file: the front round, the joining round and the seam have
no position. -/
def scWhole : SCode (List Bool) (chainsOf C D tF tJ t3).sh :=
  (RCode.none _ _ fun p => p, SCode.app _ _ (scT salt C D.ds₁)
    (RCode.none _ _ fun p => p, SCode.app _ _ (scT salt C D.ds₂)
      (RCode.none _ _ fun p => p, scT salt C D.ds₃)))

/-- What is written is read back, if no tree of the file is deeper than 63. -/
theorem scWhole_ok
    (h : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    SCode.OK (chainsOf C D tF tJ t3).sh (scWhole salt C D tF tJ t3) :=
  ⟨RCode.none_ok _ _ _, SCode.app_ok _ _ _ _
    (scT_ok salt C D.ds₁ fun d hd => h d (List.mem_append_left _ hd))
    ⟨RCode.none_ok _ _ _, SCode.app_ok _ _ _ _
      (scT_ok salt C D.ds₂ fun d hd =>
        h d (List.mem_append_right _ (List.mem_append_left _ hd)))
      ⟨RCode.none_ok _ _ _, scT_ok salt C D.ds₃ fun d hd =>
        h d (List.mem_append_right _ (List.mem_append_right _ hd))⟩⟩⟩

end

end OnBytes.Flat
