-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Shared.lean: the parameters of the shared chain's invariant as
one term, general in the library's parameters. It gives every field of `Thread`
(Honest/Thread/Thr.lean) for the shared chain, from the library's own table of joints
(Johnson/Desc/Shared/BordersShared.lean: `ItemS`, `rowS`, `MeaningS`, `ItemS.holdsSh`). Definitions;
no theorem is stated.

What is supplied. The items: the shared ones alone (Honest/Thread/SharedRows.lean): by type this
chain's prover's sides are given no instance and no state of the first chain; so nothing is given to
the chain (`P := Unit`), and an item's proposition is `ItemS.holdsSh`, which reads the chain's own
state. The form: the kind's book-keeping at the border, a Bool (`shape`), and after the last
sub-protocol "nothing is left"; beside it a parameter `order` for what is no Bool (that the
statement is in order: under it what a row says does not change when the statement grows). The
promise's other clauses (the stored table's; no collision; every leaf shown) speak of a word that
may be any word: the invariant's clause (H) says outright which tables have been sent.

Limits.
  * Every field of `Letters` is a parameter; `Mg` is meant to be supplied at a meaning that is
    already adapted to the honest side (a pin: the state holds the sample and the message answers it
    so; nearU at distance 0). It may depend on the input, as in Honest/Thread/First.lean.
  * Nothing proves that the invariant can hold at any run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharedRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SharedThread
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Shared (ItemS NumbersS MeaningS sharedPlaces)

/-- **The parameters of the shared chain.** -/
structure Letters (Bk : ProverCoinCounts) (S₂ Cl W₀ Rc Ky X₀ P₁ Wt : Type) where
  /-- the two messages differ in code; the table's numbers; the items' meaning -/
  split : Bool
  N : NumbersS
  Mg : Common W₀ Rc Ky → MeaningS S₂ P₁ Wt
  /-- the form -/
  shape : Nat → S₂ → Bool
  nothingLeft : S₂ → Bool
  order : S₂ → Prop
  /-- the description's own blocksInOrder list; the prover's sides -/
  bs : List (Block S₂ Cl)
  hs : List (Placed Empty (Common W₀ Rc Ky) X₀)
  /-- the witness and the trees' tables: meant to be computed from one structure of functions -/
  wit : Coins Bk → Common W₀ Rc Ky → List Fmt.Drawn → Wt
  table : Fmt.TreeSource → Coins Bk → Common W₀ Rc Ky → List Fmt.Drawn → Place × Table
  fixed : Fmt.TreeSource → Nat
  stored : Common W₀ Rc Ky → Nat → Nat → Option (List UInt64)
  /-- the chain's first state, computed from the key -/
  first : Ky → S₂
  item : Nat
  n₁ : Nat
  n₂ : Nat
  valid : Common W₀ Rc Ky → Prop
  rides : Nat → Common W₀ Rc Ky → S₂ → Prop
  keeps : Nat → S₂ → S₂ → Prop

variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Ky X₀ P₁ Wt : Type}

/-- **The shared chain's `Thread`.** -/
def Letters.thread (L : Letters Bk S₂ Cl W₀ Rc Ky X₀ P₁ Wt) :
    Thread Bk S₂ Cl Empty (Common W₀ Rc Ky) X₀ Ky :=
  { φ := .shared, chain := 1, ft := 0, bs := L.bs, hs := L.hs, ahead := [], near := 0, taken := []
    fixed := L.fixed, table := L.table, stored := L.stored, valid := L.valid
    ι := ItemS, dec := inferInstance, start := SharedRows.start, row := SharedRows.rows L.split
    P := Unit, handed := fun _ _ _ => ()
    Wt := Wt
    form := fun b a => L.shape b a.2 &&
      (!decide ((sharedPlaces L.split).length ≤ b) || L.nothingLeft a.2)
    formP := fun _ a => L.order a.2
    means := fun w i a y v => ItemS.holdsSh L.N (L.Mg w) i a.2 y v
    wit := L.wit
    strs := Env.strs L.item (srcAt 1 L.n₁ L.n₂)
    begun := fun _ w _ s₀ => s₀ = L.first w.key
    rides := L.rides, keeps := L.keeps }

end ProofFile.Honest.SharedThread
