-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Bools.lean: THE PUBLIC PREMISES OF K12's LAW IN THE PLAIN FORM (`AtPlace`,
Sheet.lean), AND THE PROMISE `FirstOpens`, AS TESTS WITH CODE, EACH TIED TO ITS PROPOSITION.
Statements and proofs; the tests themselves: BoolsTests.lean. So that a run can say whether the law
has a member at a plan's data and at a record that runs, and what it evaluates is this library's own
text, no twin.

  `likeOk π ds` ⇒ `AtPlace.like` (`like_of_ok`).
  `wantsB dep num ds rs` ⇒ `AtPlace.wants` (`wants_of_B`): round by round: no stored table on either
    side; the data open just the trees that the declared openings name, in turn; the stage knows
    each at its declared depth.
  `numOwn_numAt`: at `numAt` (Johnson/Desc/BlockSlot.lean) `AtPlace.numOwn` is one equation.
  `treesOk π` ⇒ `AtPlace.trees` (`trees_of_ok`): along the written rounds as `chainFrom` cuts them:
    a fold's rounds send no tree, a switch's first sends one, its second none.
  `firstOpensB π num no base t` ⇒ `FirstOpens π num no base t` (`firstOpens_of_B`).
  `PlaceB`, `atPlace_of`: all of `AtPlace` from the tests' yes, `CodesAt` and `bears`.
Limits: evaluated is not proved; a test's no does not refute its proposition but where that is said.
Nothing has been evaluated. No soundness is claimed.

-/
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.Coin.BoolsTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk Letters kk stepEndX stepMidX)
open H2K.First (gpOf Plain)

/-! ## like -/

theorem like_of_B {d : RDT} {w : WR} (h : likeB d w = true) : Like d w := by
  simp only [likeB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem likeAll_of_B : ∀ (ds : List RDT) (ws : List WR), likeAllB ds ws = true →
    List.Forall₂ Like ds ws
  | [], [], _ => .nil
  | d :: ds, w :: ws, h => by
    simp only [likeAllB, Bool.and_eq_true] at h
    exact .cons (like_of_B h.1) (likeAll_of_B ds ws h.2)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem like_of_ok (π : P12) (ds : List RDT) (h : likeOk π ds = true) :
    ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like ds (w0 :: l) := by
  unfold likeOk at h
  split at h
  · rename_i w0 l hw
    exact ⟨w0, l, hw, likeAll_of_B _ _ h⟩
  · cases h

/-! ## wants -/

theorem wants_of_B (a : ℕ) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ) :
    ∀ (ds : List RDT) (rs : List Fmt.DeclaredRound), wantsB dep num ds rs = true →
    ∀ Rs, wantsOf a dep ds Rs = wantsDecl num rs Rs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | _ :: _, _ :: _, _, [] => rfl
  | d :: ds, r :: rs, h, R :: Rs => by
    simp only [wantsB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    simp only [wantsOf, wantsDecl, h1, h2, h3, List.flatMap_nil, List.nil_append,
      List.flatMap_map, wants_of_B a dep num ds rs h5 Rs]
    congr 1
    refine List.flatMap_congr fun o ho => ?_
    rw [h4 o ho]

/-! ## numOwn -/

theorem numOwn_numAt (t₁ t₂ chain free base : ℕ) (h : numAt t₁ t₂ chain (.own free) = base) :
    ∀ n, numAt t₁ t₂ chain (.own (free + n)) = base + n := by
  intro n
  rw [← h]
  show _ + (free + n) = _ + free + n
  omega

/-! ## trees -/

theorem isSome_false {α : Type} {x : Option α} (h : x.isNone = true) : x.isSome = false := by
  cases x with
  | none => rfl
  | some _ => cases h

theorem trees_of_walk (X : Letters) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage)
    (l : List WR) (c : OnBytes.Slice.Chain (sgOf a)), chainFrom X rest a l = some c →
    treesWalk rest a l = true → c.Trees
  | [], a, l, c, hc, _ => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      trivial
    · cases hc
  | b :: rest, a, l, c, hc, h => by
    unfold chainFrom at hc
    unfold treesWalk at h
    split at hc
    · rename_i dE dT l'
      dsimp only at h
      split at hc
      · split at hc
        · rename_i dS dC l'' hd
          rw [hd] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
          cases hn : chainFrom X rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            have ih := trees_of_walk X rest b l'' next hn h5
            split
            · exact ⟨isSome_false h1, isSome_false h2, h3, isSome_false h4, ih⟩
            · exact ⟨isSome_false h1, isSome_false h2, h3, isSome_false h4, ih⟩
        · cases hc
      · cases hc
    · cases hc

theorem trees_of_ok (X : Letters) (π : P12) (h : treesOk π = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : OnBytes.Slice.Chain (sgOf a))
    (hs : π.nums.stages = a :: rest) (hw : writtenOf π.nums = some (w0 :: l))
    (hc : chainFrom X rest a l = some c) : c.Trees := by
  unfold treesOk at h
  rw [hs, hw] at h
  exact trees_of_walk X rest a l c hc h

/-! ## FirstOpens -/

theorem firstOpens_of_B (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12)
    (h : firstOpensB π num no base t = true) : FirstOpens π num no base t := by
  intro a rest G0 Ly D hf
  obtain ⟨f1, f2, f3, f4⟩ := hf
  have f5 : gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly = some D :=
    f4 default
  unfold firstOpensB at h
  rw [f1, f2, f3] at h
  dsimp only at h
  rw [f5] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h

/-! ## All of AtPlace -/

theorem atPlace_of (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hB : PlaceB F π num base dB dt = true) (hcodes : CodesAt L mC mS mW rad π.nums.stages)
    (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hbears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlace F π num L mC mS mW rad base dB dt εt := by
  simp only [PlaceB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩ := hB
  exact ⟨b1, b2, b3, b4, b5, hcodes, like_of_ok π _ b6, b7, b8, wants_of_B _ _ _ _ _ b9, hnum,
    fun a rest w0 l c hs hw hc => trees_of_ok _ π b10 a rest w0 l c hs hw hc, hbears⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.wants_of_B
#print axioms VerifiableInference.Desc.K12.Coin.trees_of_ok
#print axioms VerifiableInference.Desc.K12.Coin.firstOpens_of_B
#print axioms VerifiableInference.Desc.K12.Coin.atPlace_of
