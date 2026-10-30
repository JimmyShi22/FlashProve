-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyOfSides.lean: Conditional: `ready`
(Honest/Frame.lean) RETURNS WHERE ITS PUBLIC TESTS PASS AND EVERY SIDE OF THE PROVER's THREE CHAINS
PAYS FOR ITSELF. General in the description, the book and the prover: no kind, no filling and no lot
is named. What a side pays is stated so that it names no other side: each group of authors can pay
at its own sides, and the payments join. Two definitions, one structure, four theorems; nothing is
evaluated.

  `SidePays B ch bs g`     at each member b of the chain's list bs that stands at g's place:
                           wherever a list of sides has g as its first at that place, `chainSteps`
                           returns at [b], at the book's table and coins of chain number ch (0, 1 or
                           2), at every view and every run's coins
  `KindPays B ch bs hs κ`  every side of the list hs whose place bears the kind κ pays
  `ReadyDebts F B H`       what is left to show so that `ready` returns, by name: thirteen fields
  `sidePays_of_tests`      how a side can be paid: the five tests that `chainSteps` asks at a member
                           with a side, and one return of the book's lending at some run's coins
  `chainSteps_of_pays`     one chain: where every member has as many lists of oracle messages as
                           rounds and every side pays, `chainSteps` returns at the whole list
  `readyTests_of_debts`    `readyTests` accepts at every index in range
  `ready_of_sides`         **the join**: under `ReadyDebts`, at every index in range and every
                           request that has a trace, at every rc and every run's coins, `ready`
                           returns

Why these letters. `ready` calls `chainSteps` three times: at the book's tables `B.rowsOf 0`, `1`
and `2`; at the coins `c.look 0`, `sharedLook B c.shared` (which is `c.look 1`: `look_shared`,
Honest/Law/Along.lean) and `c.look 2`; at the view `some w` in the first and the second chain and
`none` in the shared one, where the view's type is empty: so the form binds `v : Option V`.

It asks no more than is needed. The ways back are the frame's: from one return of `ready`,
`chainSteps` returns at each member of each chain, at the prover's own list, at every view and every
run's coins (`laid_first`, `laid_shared`, `laid_second`, Honest/Thread/Laid.lean). "At every view
and every run's coins" is no more than "at one": `chainSteps_any`, `look_due`
(Honest/Law/ReadyAny.lean).

Kin. `ready_of_parts`, `chainSteps_of_members`, `chainSteps_bare`, `chainSteps_side`
(Honest/Law/ReadyOfParts.lean): what this file stands on. `ready_of_rows`
(Johnson/FrontRoad/SessionStopsFit.lean) and `run_setup` (Honest/Law/Rule/OnFile.lean) conclude a
return of `ready` from the return of a whole run. `Owed` (Honest/Owed.lean) has the fields plan,
book, places, seats and input; `FileOk` (Honest/Law/Rule/Model.lean) has rows₁, rows₂, rows₃ (the
rows' places are apart) and seat₁, seat₂, seat₃ (`Side.fits`, which holds two of the five tests).
`lendRow_ok` (E2E/KeyBookLends.lean) and `key_lends` (E2E/KeyBookLendsNamed.lean) conclude that the
lending returns. `K12.lays_of_B` (Honest/K12/StepsReturn.lean) proves the form's body at one kind's
side, in the chains 0 and 1.

Limits.
  * Implications. That any side pays, or that any prover meets `ReadyDebts`, is not shown here.
  * "`ready` returns" says nothing on whether a part plays, a round is reached or a verifier
    accepts. What `ready` returns is not said.
  * At a side whose place is no member's the form asks nothing: the fields seats₁, seats₂, seats₃
    bar such a side.
  * It gives neither `halvedAll` (Honest/Law/Run.lean) nor `rootedAll` (Honest/Law/PlanGives.lean),
    and spends neither. No field bars a side in any chain.
  * Completeness's road: never under a law over coins.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfParts
import Johnson.Desc.ProofFile.Honest.Law.ReadyAny
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription KindName)

variable {S Cl V W Y Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The form -/

/-- **A side pays**, at a book, a chain's number (0, 1 or 2) and that chain's list of sub-protocols.
It names no other side, no prover and no filling. -/
def SidePays (B : ProverCoinCounts) (ch : Nat) (bs : List (Block S Cl)) (g : Placed V W Y) : Prop :=
  ∀ b ∈ bs, b.place = g.place →
    ∀ hs : List (Placed V W Y), (hs.find? fun q => q.place == b.place) = some g →
      ∀ (v : Option V) (k : Coins B),
        ∃ l, chainSteps B (B.rowsOf ch) (k.look ch) v [b] hs = .ok l

/-- **A kind pays**: every side of the list whose place bears the kind pays. -/
def KindPays (B : ProverCoinCounts) (ch : Nat) (bs : List (Block S Cl)) (hs : List (Placed V W Y))
    (κ : KindName) : Prop :=
  ∀ g ∈ hs, g.place.kind = κ → SidePays B ch bs g

/-- **How a side can be paid**: at each member at its place the five tests that `chainSteps` asks
there, which read the member, the side's counts and the book, and one return of the book's lending,
at some run's coins. -/
theorem sidePays_of_tests (B : ProverCoinCounts) (ch : Nat) (bs : List (Block S Cl)) (g : Placed V W Y)
    (H : ∀ b ∈ bs, b.place = g.place →
      b.oracles.length = b.rounds.length ∧ g.rounds = b.rounds.length ∧
      B.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
      (B.rowsOf ch).any
        (fun r => r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = false ∧
      B.ahead.any
        (fun e => e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = false ∧
      ∃ (k₀ : Coins B) (c : RowCoins g.parts),
        lendRow B (B.rowsOf ch) (k₀.look ch) b.place g.parts 0 = .ok c) :
    SidePays B ch bs g := by
  intro b hb hp hs hf v k
  obtain ⟨ho, hr, hc, h1, h2, k₀, c, hl⟩ := H b hb hp
  obtain ⟨c', hl'⟩ := lendRow_any (look_due k₀ k ch) B (B.rowsOf ch) b.place g.parts 0 c hl
  exact ⟨_, chainSteps_side B _ _ v b hs g hf ho hr hc h1 h2 c' hl'⟩

/-! ## 2 One chain -/

/-- **One chain**: where every member has as many lists of oracle messages as rounds and every side
of the list pays, `chainSteps` returns at the whole list, at every view and every run's coins. -/
theorem chainSteps_of_pays (B : ProverCoinCounts) (ch : Nat) (bs : List (Block S Cl))
    (hs : List (Placed V W Y)) (hsh : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hp : ∀ g ∈ hs, SidePays B ch bs g) (v : Option V) (k : Coins B) :
    ∃ l, chainSteps B (B.rowsOf ch) (k.look ch) v bs hs = .ok l := by
  refine chainSteps_of_members _ _ _ _ _ _ fun b hb => ?_
  cases hf : hs.find? fun q => q.place == b.place with
  | none => exact chainSteps_bare _ _ _ _ _ (hsh b hb) hf
  | some g =>
    have hg : g ∈ hs := List.mem_of_find?_eq_some hf
    have hgp : g.place = b.place := by simpa using List.find?_some hf
    exact hp g hg b hb hgp.symm hs hf v k

/-! ## 3 What is left to show, by name; and the join -/

/-- **What is left to show so that `ready` returns, by name.** No field has an index, an rc, an
instance or a run's coins as a letter; `dummy` names the prover's own named index; the last three
bind a view and a run's coins under "for all". -/
structure ReadyDebts (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop where
  /-- On the public files: the description passes its own tests on the plan: a Boolean test -/
  plan : F.planOk = true
  /-- On the public files: the description passes its own test on the places: a Boolean test. It
  follows from `plan` (`placesOk_of_planOk`, Johnson/RunOne/Sound/KeyListsAtFK.lean); it is asked by
  name so that this file need not stand over that one -/
  places : F.placesOk = true
  /-- On the book: it fails none of its own tests at the description: a test with code -/
  book : B.word F = none
  /-- On the sides' places: each side of the first chain stands at a place of that chain: a test
  with code -/
  seats₁ : strays F.first.blocksInOrder H.first = []
  /-- On the sides' places: the like in the shared chain -/
  seats₂ : strays F.shared.blocksInOrder H.shared = []
  /-- On the sides' places: the like in the second chain -/
  seats₃ : strays F.second.blocksInOrder H.second = []
  /-- On the sides' places: no two sides of the first chain stand at one place: a test with code -/
  once₁ : twice H.first = []
  /-- On the sides' places: the like in the shared chain -/
  once₂ : twice H.shared = []
  /-- On the sides' places: the like in the second chain -/
  once₃ : twice H.second = []
  /-- On the prover's range: its named member is in range: a Boolean test -/
  dummy : H.inRange H.dummy = true
  /-- On a side, kind by kind: every side of the first chain pays -/
  pays₁ : ∀ κ, KindPays B 0 F.first.blocksInOrder H.first κ
  /-- On a side, kind by kind: every side of the shared chain pays -/
  pays₂ : ∀ κ, KindPays B 1 F.shared.blocksInOrder H.shared κ
  /-- On a side, kind by kind: every side of the second chain pays -/
  pays₃ : ∀ κ, KindPays B 2 F.second.blocksInOrder H.second κ

/-- Under `ReadyDebts` the tests of `ready` that read no instance accept, at every index in range.
-/
theorem readyTests_of_debts {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    (D : ReadyDebts F B H) {w₀ : W₀} (hi : H.inRange w₀ = true) : readyTests F B H w₀ = .ok () := by
  unfold readyTests
  rw [D.seats₁, D.seats₂, D.seats₃, D.once₁, D.once₂, D.once₃, D.places, D.dummy, hi, D.book]
  rfl

/-- **The join: under `ReadyDebts`, at every index in range and every request that has a trace, at
every rc and every run's coins, `ready` returns.** It says nothing on whether a part plays. -/
theorem ready_of_sides {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    (D : ReadyDebts F B H) {w₀ : W₀} {x : Xi} (hi : H.inRange w₀ = true)
    (ht : (H.trace w₀ x).isSome = true) (rc : Rc) (k : Coins B) :
    ∃ R, ready F B H w₀ rc x k = .ok R := by
  obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 ht
  obtain ⟨sh1, sh2, sh3⟩ := planOk_all D.plan
  exact ready_of_parts (readyTests_of_debts D hi) htr
    (chainSteps_of_pays B 0 _ _ (fun b hb => (shaped_parts (sh1 b hb).2).1)
      (fun g hg => D.pays₁ g.place.kind g hg rfl) _ k)
    (chainSteps_of_pays B 1 _ _ (fun b hb => (shaped_parts (sh2 b hb).2).1)
      (fun g hg => D.pays₂ g.place.kind g hg rfl) _ k)
    (chainSteps_of_pays B 2 _ _ (fun b hb => (shaped_parts (sh3 b hb).2).1)
      (fun g hg => D.pays₃ g.place.kind g hg rfl) _ k)

end ProofFile.Honest

#print axioms ProofFile.Honest.SidePays
#print axioms ProofFile.Honest.KindPays
#print axioms ProofFile.Honest.sidePays_of_tests
#print axioms ProofFile.Honest.chainSteps_of_pays
#print axioms ProofFile.Honest.ReadyDebts
#print axioms ProofFile.Honest.readyTests_of_debts
#print axioms ProofFile.Honest.ready_of_sides
