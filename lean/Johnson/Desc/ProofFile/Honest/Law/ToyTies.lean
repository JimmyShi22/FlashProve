-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyTies.lean: the invariants through the toy example of
Honest/Law/ToyRow.lean: a condition before each sub-protocol of the description's three flat lists,
and at each sub-protocol `PlaysOn` (Honest/Law/ThreadC.lean) from the condition before it to the one
after it; the conditions at the two starts and at the second chain's start. These are the hypotheses
h₁, h₂, h₃, a₁, a₂, a₃ of `runC_returns` (Honest/Law/RunsFile.lean) at this example. The theorems
are about these files' own made-up objects alone. None is one of the library's goals.

  1  `playsOn_mono`, `playsOn_keeps`   two small rules for `PlaysOn`
  2  `Hy`, `storedOk`, `Iy₁`, `Iy₂`, `Iy₃`   the example's prover; the conditions by position
  3  `thread₁`, `thread₂`, `thread₃`   `PlaysOn` at the ten sub-protocols: four from `Good`
     (Honest/Law/ToyGood.lean), four sub-protocols without a round, two with a round and without a
     prover's side
  4  `start₁y`, `start₂y`, `door₃y`   the three starts

Limits.
  * A toy example.
  * What the plan declares of the three lists of rounds (`PlanServes`) and that `ready` returns are
    not in this file.
  * No part of the example reads what it is handed as `Seen`, so none reads the field `opened`: what
    the hypotheses here ask of that field is met for free. Of a prover with a part that reads the
    columns nothing is shown here.
  * The invariants leave the field free, `none` too. How invariants that pin it are paid is not
    shown here (Honest/Law/RunsFile.lean, Limits).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunsFile
import Johnson.Desc.ProofFile.Honest.Law.ToyGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn)
open VerifiableInference.Desc.BlockToy (St)

/-! ## 1 Two small rules -/

section
variable {S Cl V W Y Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat}
  {hs : List (Placed V W Y)} {b : Block S Cl}

/-- A stronger condition before, a weaker one after. -/
theorem playsOn_mono {A A' B B' : Coins Bk → S → Mid W Y → Env → Prop}
    (h : PlaysOn φ Bk chain ft hs b A B) (hA : ∀ k s m E, A' k s m E → A k s m E)
    (hB : ∀ k s m E, B k s m E → B' k s m E) : PlaysOn φ Bk chain ft hs b A' B' := by
  intro k s m E ds l hA' hd hst hl
  obtain ⟨y, cols, h1, h2, h3⟩ := h k s m E ds l (hA _ _ _ _ hA') hd hst hl
  exact ⟨y, cols, h1, h2, fun s' n hs' => hB _ _ _ _ (h3 s' n hs')⟩

/-- No sub-protocol changes the stored tables' columns: a condition on them alone is carried along.
-/
theorem playsOn_keeps {A B : Coins Bk → S → Mid W Y → Env → Prop}
    (h : PlaysOn φ Bk chain ft hs b A B) (Q : (Nat → Nat → Option (List UInt64)) → Prop) :
    PlaysOn φ Bk chain ft hs b (fun k s m E => A k s m E ∧ Q E.stored)
      (fun k s m E => B k s m E ∧ Q E.stored) := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨y, cols, h1, h2, h3⟩ := h k s m E ds l hA.1 hd hst hl
  exact ⟨y, cols, h1, h2, fun s' n hs' => ⟨h3 s' n hs', hA.2⟩⟩

end

/-! ## 2 The conditions by position -/

/-- The prover whose sides are the example's. -/
def Hy : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat := Gy.prover Py

/-- The stored table's columns are available, two words wide. -/
def storedOk (st : Nat → Nat → Option (List UInt64)) : Prop :=
  ∀ x, ∃ u, st 0 x = some u ∧ u.length = 2

/-- The first chain: its front, the sealing round: nothing is asked. -/
def Iy₁ : Nat → Coins By → St → Mid L Nat → Env → Prop := fun _ => anyAt

/-- The shared chain: before its front and before `look`: no tree yet; before `storeY`: the tree of
`look`, with this run's coins in its words; all along the stored columns; after `storeY` nothing. -/
def Iy₂ : Nat → Coins By → St → Mid L₀ Nat → Env → Prop
  | 0 => fun k s m E => noTree k s m E ∧ storedOk E.stored
  | 1 => fun k s m E => noTree k s m E ∧ storedOk E.stored
  | 2 => fun k s m E => lookSent k s m E ∧ storedOk E.stored
  | _ => anyAt

/-- The second chain: before its front and before `send`: no tree yet; before `tellB` and before
`askQ`: the tree of `send`, with this run's coin in its words; then nothing. -/
def Iy₃ : Nat → Coins By → St → Mid L Nat → Env → Prop
  | 0 => noTree
  | 1 => noTree
  | 2 => sendSent
  | 3 => sendSent
  | _ => anyAt

/-! ## 3 `PlaysOn` at the ten sub-protocols -/

theorem thread₁ : ∀ j b, Fy.first.blocksInOrder[j]? = some b →
    PlaysOn .own By 0 0 Hy.first b (Iy₁ j) (Iy₁ (j + 1)) := by
  intro j b hj
  match j, hj with
  | 0, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ _ _ => trivial
  | 1, hj =>
    obtain rfl := Option.some.inj hj
    refine plays_of_bare rfl fun k s m E ds y _ hd _ => ⟨[], ?_, fun _ _ _ => trivial⟩
    have hd' : drawsFit [{ entry := { name := "SEAL" } }] ds = true := hd
    obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
    rfl
  | n + 2, hj => cases hj

theorem thread₂ : ∀ j b, Fy.shared.blocksInOrder[j]? = some b →
    PlaysOn .shared By 1 0 Hy.shared b (Iy₂ j) (Iy₂ (j + 1)) := by
  intro j b hj
  match j, hj with
  | 0, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ hA _ => hA
  | 1, hj =>
    obtain rfl := Option.some.inj hj
    exact playsOn_keeps (plays_of_good (good_look (pre := [])) rfl) storedOk
  | 2, hj =>
    obtain rfl := Option.some.inj hj
    refine plays_of_bare rfl fun k s m E ds y hA hd _ => ?_
    have hd' : drawsFit storeY.rounds ds = true := hd
    obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
    obtain ⟨p, hp⟩ := one_of_length (poss_of_drawFit h₀)
    obtain ⟨el, ps, tr, dg⟩ := R
    have hp' : ps = [p] := hp
    subst hp'
    obtain ⟨u, hu, hl⟩ := hA.2 (p % 2 ^ 3)
    refine ⟨[(Fmt.storedKey 0, p % 2 ^ 3, u)], ?_, fun _ _ _ => trivial⟩
    show fillCols [⟨Fmt.storedKey 0, p % 2 ^ 3, some 0, none, none, E.stored 0 (p % 2 ^ 3), 2⟩] [] =
      _
    rw [hu]
    show (if (u.length != 2) = true then _ else _) = _
    rw [hl]
    rfl
  | n + 3, hj => cases hj

theorem thread₃ : ∀ j b, Fy.second.blocksInOrder[j]? = some b →
    PlaysOn .own By 2 Fy.lastChainFirstTreeNumber Hy.second b (Iy₃ j) (Iy₃ (j + 1)) := by
  intro j b hj
  match j, hj with
  | 0, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ hA _ => hA
  | 1, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_send (pre := [])) rfl
  | 2, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_tell (pre := [])) rfl
  | 3, hj =>
    obtain rfl := Option.some.inj hj
    exact playsOn_mono (plays_of_good (good_carry (pre := [])) rfl) (fun _ _ _ _ _ => trivial)
      fun _ _ _ _ h => h
  | 4, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ _ _ => trivial
  | n + 5, hj => cases hj

/-! ## 4 The three starts -/

theorem start₁y (k : Coins By) (s : St) (m : Mid L Nat) (E : Env) : Iy₁ 0 k s m E := trivial

theorem start₂y (k : Coins By) (s : St) (m : Mid L₀ Nat) (w₀ : Wit₀) (rc : UInt64) :
    Iy₂ 0 k s m (envOf (Hy.storedWords w₀ rc) (fun _ _ => none) []) :=
  show noTree k s m _ ∧ storedOk _ from ⟨rfl, fun _ => ⟨_, rfl, rfl⟩⟩

theorem door₃y (k : Coins By) (s : St) (m : Mid L Nat) (E₁ E₂ : Env) :
    Iy₃ 0 k s m (envThird E₁ E₂) := rfl

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.playsOn_mono
#print axioms ProofFile.Honest.Toy.playsOn_keeps
#print axioms ProofFile.Honest.Toy.thread₁
#print axioms ProofFile.Honest.Toy.thread₂
#print axioms ProofFile.Honest.Toy.thread₃
#print axioms ProofFile.Honest.Toy.start₁y
#print axioms ProofFile.Honest.Toy.start₂y
#print axioms ProofFile.Honest.Toy.door₃y
#print axioms ProofFile.Honest.Toy.Hy
#print axioms ProofFile.Honest.Toy.storedOk
#print axioms ProofFile.Honest.Toy.Iy₁
#print axioms ProofFile.Honest.Toy.Iy₂
#print axioms ProofFile.Honest.Toy.Iy₃
