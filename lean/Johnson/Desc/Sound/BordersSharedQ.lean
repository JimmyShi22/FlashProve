-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersSharedQ.lean: the shared chain's table of joints
(Johnson/Desc/Shared/BordersShared.lean) AS THE CONDITIONS AND RELATIONS OF THE RULE OF COMPOSITION AT THE
SECOND CHAIN: `onQ₂`, `relQ₂`: NAMED TERMS. Definitions, and one statement written as `def … : Prop`. A
SKELETON (the letters follow another version of the table: no `Reading`, no description, no letter
for "the mask goes out ahead"). NOTHING IS PROVED IN THIS FILE.

What is said. The second chain's record is a pair: what was handed to the chain (P₁: each slot's own),
and the chain's own record (S₂). The acting part at border k: the own record, the stored table, the
chain's own trees that are sent (`actsOf Prod.snd lo p l k`).
  `strsOfAct`: what an acting part's VALUE shows, as plain functions.
  `muQ`: a SHARED item's meaning at border k: `ItemS.holdsSh` AT THE ACTING PART's VALUE: it is handed
    nothing else.
  `insSh`, `outsSh`, `startSh`: the table's shared items, as the rule's letters.
  `ownAt`, `relOwn`: the own items open at border k (one list up to "LIN point", one behind it), and
    "every one of them holds": this may read the whole statement.
  **`relQ₂`**: every open shared item holds, and every open own item holds.
  **`onQ₂`**: the table's shared promise at the acting part's value, and the slot's own condition Oc.
  `SharedJoin`: THE STRETCH BEHIND "LIN point" IS PAID ONCE: if each of its blocks has its own law for ONE
    statement between the shared items that its row closes and opens, the shared items that ride are
    kept, the extractors read through the acting part and keep the own items, and Oc is carried: then
    every block of the stretch pays for every N at its own errors, AT `onQ₂` AND `relQ₂`.

Limits. (1) Those of BordersShared.lean: a skeleton; no row is confirmed; most meanings are
letters (`MeaningS`, `PromMeaning`, `NumbersS`, Oc; the type Wt of witnesses). UNDER LETTERS THE TERMS ARE NAMED, NOT
CLOSED: a row of laws owed that is stated at them is closed only when the letters are filled. (2) The
front block and "LIN point" are not in the stretch: they owe `PaysN` at these same terms by laws of
their own. (3) That `ownAt` is the own part of the table's computed open sets is a test on the table, run
(BordersShared.lean: `ownStill`; the harness's last line but one), not a theorem.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Shared.BordersShared
import Johnson.Desc.Sound.SpineOnce
import Johnson.Desc.Sound.MsgAt
import Johnson.Desc.Sound.FileRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)
open VerifiableInference.Desc.Shared

/-- What an acting part's value shows: the stored table, and the chain's own trees that are sent. -/
def strsOfAct (Fr : Frame) {S₀ : Type}
    (v : S₀ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64))) : Strs :=
  ⟨fun x => if h : x < 2 ^ Fr.a then some (v.2.1 ⟨x, h⟩) else none, fun j x => (v.2.2 j x).getD []⟩

/-- The row of block number k. A number behind the last block: the empty row. -/
def rowAtS (split : Bool) (k : ℕ) : RowOfS :=
  ((sharedPlaces split)[k]?.map (rowS split)).getD {}

/-- The SHARED items that block number k closes, with those that it reads. -/
def insSh (split : Bool) (k : ℕ) (i : ItemS) : Prop :=
  i.own = false ∧ i ∈ (rowAtS split k).ins ++ (rowAtS split k).ctx

/-- The SHARED items that it opens, with those that it reads. -/
def outsSh (split : Bool) (k : ℕ) (i : ItemS) : Prop :=
  i.own = false ∧ i ∈ (rowAtS split k).outs ++ (rowAtS split k).ctx

/-- The SHARED items that are open at the chain's start. -/
def startSh (i : ItemS) : Prop := i.own = false ∧ i ∈ startS

/-- The OWN items that are open at border k. -/
def ownAt (k : ℕ) : List ItemS :=
  if k ≤ pointAt then startS.filter (·.own) else endS.filter (·.own)

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))

/-- The acting parts at the shared chain's borders. -/
abbrev actQ : ℕ → BKey Fr (P₁ × S₂) := actsOf (Prod.snd : P₁ × S₂ → S₂) N.lo p l

/-- **A shared item's meaning at border k**: at the acting part's value. -/
def muQ (i : ItemS) (k : ℕ) (v : (actQ N p l k).1) (w : Wt) : Prop :=
  i.holdsSh N Mg v.1 (strsOfAct Fr v) w

/-- Every own item that is open at border k holds. -/
def relOwn (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) (w : Wt) : Prop :=
  ∀ i ∈ ownAt k, i.holdsOwn N Mg a.1.1 a.1.2 (strsOf Fr a.2) w

/-- **THE RELATION AT BORDER k OF THE SHARED CHAIN.** -/
def relQ₂ (k : ℕ) : (P₁ × S₂) × Fr.E.Str → Wt → Prop := fun a w =>
  relSh (actQ N p l) (muQ N Mg p l)
      (openAfter (insSh split) (outsSh split) startSh k) k a w ∧
    relOwn N Mg k a w

/-- The shared promise at border k, at the acting part's value. -/
def promQ (k : ℕ) (v : (actQ N p l k).1) : Prop :=
  ∀ c ∈ promsAt split k, c.holds N Pm v.1 (strsOfAct Fr v)

/-- **THE CONDITION AT BORDER k OF THE SHARED CHAIN.** -/
def onQ₂ (k : ℕ) : (P₁ × S₂) × Fr.E.Str → Prop := fun a =>
  promQ N Pm split p l k ((actQ N p l k).2 a) ∧ Oc a.1.1 (strsOf Fr a.2)

end

/-- **THE STRETCH BEHIND "LIN point" IS PAID ONCE, AT THE TABLE's OWN TERMS.** The chain's pieces are
f (the front block), pt ("LIN point"), then q :: r. -/
def SharedJoin : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (n : ℕ)
    (f pt q : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt)),
    Tiled q r →
    (∀ x ∈ q :: r, ∃ b₀ : Block S₂ Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s)) →
    (∀ x ∈ q :: r, ∀ d ∈ x.ds, ∀ j ∈ d.opens, N.lo ≤ j) →
    EachOwnSh (fun k a => promQ N Pm split f (pt :: q :: r) k
        ((actQ N f (pt :: q :: r) k).2 a)) (actQ N f (pt :: q :: r))
      (muQ N Mg f (pt :: q :: r)) (insSh split) (outsSh split) 2 (q :: r) →
    EachFramesSh (fun k a => promQ N Pm split f (pt :: q :: r) k
        ((actQ N f (pt :: q :: r) k).2 a)) (actQ N f (pt :: q :: r))
      (muQ N Mg f (pt :: q :: r)) (insSh split)
      (openAfter (insSh split) (outsSh split) startSh) 2 (q :: r) →
    EachExtBy (actQ N f (pt :: q :: r)) 2 (q :: r) →
    EachKeeps (fun k a => promQ N Pm split f (pt :: q :: r) k
        ((actQ N f (pt :: q :: r) k).2 a)) (relOwn N Mg 2) 2 (q :: r) →
    (∀ x ∈ q :: r, ∀ a τ b, Oc a.1.1 (strsOf Fr a.2) → x.ior.red.out a τ = some b →
      Oc b.1.1 (strsOf Fr b.2)) →
    EachPaysN n (onQ₂ N Pm Oc split f (pt :: q :: r))
      (relQ₂ N Mg split f (pt :: q :: r)) (actQ N f (pt :: q :: r)) 2 (q :: r)

-- THE FORM: the two terms go, as they are, into the second chain's fields of the rule's `Places`
example (D : WholeD) (all : List LeftT) (P₁ S₂ S₁ S₃ Cl Wt : Type) (C : CK) (ft : ℕ) (N : NumbersS)
    (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (p : Piece C (frameAt D all D.key₂ ft) (P₁ × S₂) Cl Wt)
    (l : List (Piece C (frameAt D all D.key₂ ft) (P₁ × S₂) Cl Wt))
    (Q : Places D all S₁ (P₁ × S₂) S₃ Wt) : Places D all S₁ (P₁ × S₂) S₃ Wt :=
  { Q with on₂ := onQ₂ N Pm Oc split p l, R₂ := relQ₂ N Mg split p l }

#check @SharedJoin

end VerifiableInference.Desc.Sound
