-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/First.lean: the parameters of the first chain's invariant as
one term, general in the library's parameters. It gives every field of `Thread`
(Honest/Thread/Thr.lean) for the first chain, from the library's own table of joints
(Johnson/Desc/First/Borders.lean: `Item`, `rowOf`, `start`, `Meaning`, `Item.holds`, `onAt`,
`openSets`, `pubSets`). Definitions; no theorem is stated.

  1  `honest`   a `Meaning` adapted to the honest side: the same structure with five fields replaced
  2  `Script`, `Script.wit`   one structure of functions from which the witness and the trees'
     tables are computed
  3  `Letters`, `Letters.mg`, `Letters.mgP`, `Letters.thread`   the parameters of the first chain;
     the `Thread` built from them

Why general. The library's own meaning of the items (`mgAll`, Johnson/Desc/Sound/MgAll.lean) and the
hypothesis that ties its parameters to the proof file's description come late in the library's order
of imports. This file takes a meaning, the table's numbers, the segments' sorts, the places and the
flat list as parameters, and imports the table alone. The term at the library's own parameters is a
few lines in a file of its own (Honest/Thread/FirstAt.lean).

The meaning adapted to the honest side. An item's proposition is the library's, at a meaning that is
changed at five fields. `pin`: a parameter `ans`: the verifier's state holds the sample of the
message's seat (tenant t of tree j: the position at which the message is committed), and the
witness's message answers it so: no decoder. `noColl`, `shown`, `decodes`: true: they are promises
on a word that may be any word; the invariant's clause (H) says outright which tables have been
sent. `totalB`: the item that promises a later acceptance is stated under "no fall":
`test m s = none →` the meaning's own proposition. `test`: the parameter for the fall that is placed
at the sub-protocol without a round after the batching of segment m, asked at the state at which the
item is held.

The form. `form`: no named test on values has failed. `formP`: the library's own promise `onAt` (the
public book-keeping that is promised at a border), at the adapted meaning, at the table's own open
sets (`openSets`, `pubSets`): not at the forward ones, which hold `wrow` besides. It reads no oracle
at this meaning: an empty `Strs` is supplied.

Limits.
  * Every field of `Letters` is a parameter: nothing here compares `bs` with `ps`, `N` with `bs`,
    the public fields of `MgP` with those of `Mg w`, the tables of the `Script` with what a prover's
    side sends, or its witness with its tables.
  * `ans` and `test` have no definition here.
  * It is not proved that the invariant can hold at any run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Place Strs Wit)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt openSets pubSets start)

/-! ## 1 The meaning adapted to the honest side -/

/-- **A meaning adapted to the honest side.** `ans`: what a pin says on the honest side. `test`: for
each segment, the fall that is placed after its batching. -/
def honest {P Wt : Type} (Mg : Meaning P Wt) (ans : Nat → Nat → P × S → Strs → Wt → Prop)
    (test : Nat → S → Option String) : Meaning P Wt :=
  { Mg with
    pin := ans
    noColl := fun _ _ _ _ => True
    shown := fun _ _ _ => True
    decodes := fun _ _ => True
    totalB := fun m a y w => test m a.2 = none → Mg.totalB m a y w }

/-- No oracle. -/
def noStrs : Strs := ⟨fun _ => none, fun _ _ => []⟩

/-! ## 2 The `Script` -/

/-- **The `Script`**: what the honest prover's messages are, as functions of a run's coins, the
input and the challenges heard. One structure feeds the witness and the tables. -/
structure Script (Bk : ProverCoinCounts) (W Cells Tok M : Type) where
  /-- what the stored table commits to: meant to be computed from the index alone -/
  cells : W → Cells
  /-- the token: meant to be the instance's asked token -/
  tok : W → Tok
  /-- message number n, and after how many challenges it no longer changes: from the last challenge
  that it reads on, not from its sending -/
  msg : Nat → Coins Bk → W → List Fmt.Drawn → M
  fixedMsg : Nat → Nat
  /-- tenant t of tree j: the table of which the pad's places are read -/
  pad : Nat → Nat → Coins Bk → W → M
  /-- a tree's sender's place and its table, and after how many challenges it no longer changes -/
  table : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table
  fixed : Fmt.TreeSource → Nat

/-- **The witness**, from a run's coins, the input and challenges. -/
def Script.wit {Bk : ProverCoinCounts} {W Cells Tok M : Type} (Q : Script Bk W Cells Tok M) (k : Coins Bk)
    (w : W) (h : List Fmt.Drawn) : Wit Cells Tok M :=
  ⟨Q.cells w, Q.tok w, fun n => Q.msg n k w (h.take (Q.fixedMsg n)), fun j t => Q.pad j t k w⟩

/-! ## 3 The parameters and the `Thread` -/

/-- **The parameters of the first chain.** -/
structure Letters (Bk : ProverCoinCounts) (Cl W₀ Rc Xi Tr X P Cells Tok M : Type) where
  /-- the segments' sorts; the flat list's places; the table's numbers -/
  links : List ModelPart
  ps : List Place
  N : Numbers
  /-- the items' meaning: it may depend on the input (at the library's own meaning the decoder of
  the stored table is a field: on the honest side it is the constant "the input's cells"); the
  meaning of which the promise's public fields are read, which has no input to read; the two
  parameters of the honest side -/
  Mg : Local W₀ Rc Xi Tr → Meaning P (Wit Cells Tok M)
  MgP : Meaning P (Wit Cells Tok M)
  ans : Nat → Nat → P × S → Strs → Wit Cells Tok M → Prop
  test : Nat → S → Option String
  /-- the description's own flat list; the prover's sides -/
  bs : List (Block S Cl)
  hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)
  Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok M
  /-- the stored table's columns -/
  stored : Local W₀ Rc Xi Tr → Nat → Nat → Option (List UInt64)
  /-- what the chain is given of the instance; the chain's first state, computed from that -/
  pubOf : Xi → P
  first : P → S
  /-- the statement's item of the stored table; how many trees the first and the shared chain send
  -/
  item : Nat
  n₁ : Nat
  n₂ : Nat
  valid : Local W₀ Rc Xi Tr → Prop
  rides : Nat → Local W₀ Rc Xi Tr → S → Prop
  keeps : Nat → S → S → Prop

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- The items' meaning, adapted to the honest side, at an input. -/
def Letters.mg (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) (w : Local W₀ Rc Xi Tr) :
    Meaning P (Wit Cells Tok M) :=
  honest (L.Mg w) L.ans L.test

/-- The promise's meaning, adapted to the honest side. -/
def Letters.mgP (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) : Meaning P (Wit Cells Tok M) :=
  honest L.MgP L.ans L.test

/-- **The `Thread` of the first chain.** -/
def Letters.thread (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) :
    Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { φ := .own, chain := 0, ft := 0, bs := L.bs, hs := L.hs, ahead := [], near := 0, taken := []
    fixed := L.Q.fixed, table := L.Q.table, stored := L.stored, valid := L.valid
    ι := Item, dec := inferInstance, start := start L.links
    row := FirstRows.rows L.links L.ps
    P := P, handed := fun _ w _ => L.pubOf w.x
    Wt := Wit Cells Tok M
    form := fun _ a => a.2.failed.isNone
    formP := fun b a => onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) a noStrs
    means := fun w i a y v => Item.holds L.N (L.mg w) i a y v
    wit := L.Q.wit
    strs := Env.strs L.item (srcAt 0 L.n₁ L.n₂)
    begun := fun _ w _ s₀ => s₀ = L.first (L.pubOf w.x)
    rides := L.rides, keeps := L.keeps }

end ProofFile.Honest.FirstThread
