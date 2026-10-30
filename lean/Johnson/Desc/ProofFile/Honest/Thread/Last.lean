-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Last.lean: the second chain's `Thread` as one term, general in
the library's parameters: every field of `Thread` (Honest/Thread/Thr.lean) for the second chain,
from the library's own table of joints (Johnson/Desc/Last/BordersLast.lean: `ItemL`, `rowL`,
`MeaningL`, `ItemL.holds`, `PromMeaningL`). Definitions; no theorem is stated.

What is defined. What was passed to the chain is a pair: the public part with the first chain's last
state, and the shared chain's last state: the five items that come over the joint, and the
book-keeping, read both. These two states are computed by the run: so `handed` is a function `ends`
of the run's coins, the input and the challenges before the chain: a parameter here; that it is what
the two earlier chains' invariants hold at their last borders has to be proved at the second chain's
start. `ahead`: the rounds of the two earlier chains; `near`: how many of them are the first chain's
(this chain's stops read the first chain's challenges and its own). `taken`: the sources of the
trees that are taken over.

Limits.
  * Every field of `Letters` is a parameter; `Mg` and `ML` are meant to be supplied at honest
    parameters already.
  * It is not proved that the invariant holds at any run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.LastRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.LastThread
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (ItemL MeaningL PromMeaningL startLast lastPlaces)

/-- **The parameters of the second chain.** -/
structure Letters (Bk : ProverCoinCounts) (S₂ S₃ Cl W₀ Rc Xi Tr X P₁ Wt : Type) where
  N : NumbersS
  Mg : Local W₀ Rc Xi Tr → MeaningS S₂ P₁ Wt
  ML : MeaningL S₃ Wt
  /-- the form -/
  PL : PromMeaningL S₂ S₃ P₁
  order : S₃ → Prop
  /-- the number in the label of the chain's first own tree -/
  ft : Nat
  /-- the description's own flat list; the prover's sides -/
  bs : List (Block S₃ Cl)
  hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)
  /-- the two earlier chains' rounds; how many are the first chain's; the trees taken over -/
  ahead : List Fmt.DeclaredRound
  near : Nat
  taken : List Fmt.TreeSource
  /-- what was passed to the chain -/
  ends : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → P₁ × S₂
  /-- the chain's first state, from what was passed -/
  first : P₁ × S₂ → S₃ → Prop
  wit : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Wt
  table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Place × Table
  fixed : Fmt.TreeSource → Nat
  stored : Local W₀ Rc Xi Tr → Nat → Nat → Option (List UInt64)
  item : Nat
  n₁ : Nat
  n₂ : Nat
  valid : Local W₀ Rc Xi Tr → Prop
  rides : Nat → Local W₀ Rc Xi Tr → S₃ → Prop
  keeps : Nat → S₃ → S₃ → Prop

variable {Bk : ProverCoinCounts} {S₂ S₃ Cl W₀ Rc Xi Tr X P₁ Wt : Type}

/-- **The second chain's `Thread`.** -/
def Letters.thread (L : Letters Bk S₂ S₃ Cl W₀ Rc Xi Tr X P₁ Wt) :
    Thread Bk S₃ Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { φ := .own, chain := 2, ft := L.ft, bs := L.bs, hs := L.hs
    ahead := L.ahead, near := L.near, taken := L.taken
    fixed := L.fixed, table := L.table, stored := L.stored, valid := L.valid
    ι := ItemL, dec := inferInstance, start := startLast, row := LastRows.rows
    P := P₁ × S₂, handed := L.ends
    Wt := Wt
    form := fun b a => L.PL.shape b a.1.1 a.1.2 a.2 &&
      (!decide (lastPlaces.length ≤ b) || L.PL.nothingLeft a.2)
    formP := fun _ a => L.order a.2
    means := fun w i a y v => ItemL.holds L.N (L.Mg w) L.ML i a.1.1 a.1.2 a.2 y v
    wit := L.wit
    strs := Env.strs L.item (srcAt 2 L.n₁ L.n₂)
    begun := fun k w h s₀ => L.first (L.ends k w h) s₀
    rides := L.rides, keeps := L.keeps }

end ProofFile.Honest.LastThread
