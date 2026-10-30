-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverChain.lean: THE CANONICAL GATES OF ONE CHAIN. A gate's test
(Honest/Law/SharesHeld.lean) is a function of the challenges in front and of its own rounds'
challenges: so it cannot ask a whole run. `fellBy` asks the walk (Honest/Walk.lean) over the chain's
first n Steps, and reads the frame's own `chainFall` (Honest/Fall.lean) off what that walk has laid.
One gate a member: at the member's own rounds' data; its test: a mark at its place speaks
(Honest/Law/Marks.lean), or by the member's last round the run has met a fall. Each test asks «by
then»: so where the run has met a fall by the chain's last round, the last gate has spoken. A MARK's
TEST IS HANDED ALL CHALLENGES IN FRONT, those in front of the chain first.

WHAT THIS IS. Definitions, and one lemma on lists. No measure is in this file. None of the library's
goals.

A FALL AT A MEMBER WITHOUT A ROUND needs no case of its own: the walk settles such members as soon
as the rounds in front of them are laid, and `frontsOf` lists them: so the gate of the member with a
round in front of it holds that fall.

  1  `fellBy`   by the chain's first n rounds the run has met a fall
  2  `coverGates`, `cover_ds`   one gate a member
  3  `cover_chain`   the last gate has it

Limits. Where the walk over a front refuses (a stop, a fault) `fellBy` says false, and so it does
where `start` or `s₀` is `none`. X: what a chain's walk starts from, as a function of the challenges
in front of the chain: a letter. A MARK IS TO STAND AT A MEMBER WITH A ROUND: at a member without
one its gate has no message to measure over, and holds it by 0 or by 1 alone. A fall at a member
without a round IN FRONT OF THE CHAIN's FIRST ROUND hangs on no challenge of the chain: the first
gate holds it, by 0 or by 1 alone. WHERE THE LAST GATED MEMBER HAS NO ROUND, a fall at a member of
the tail's rounds is held by 0 or by 1 alone. A mark at no gated member's place is asked by no gate.
This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Fall
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.ProofFile.Honest.Law.SharesChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc (Block)
open OnBytes.Maker (RDT)

variable {S Cl W Y : Type}

/-! ## 1 By the chain's first n rounds -/

/-- **What a chain's walk starts from.** lay, steps, start: as `walk` takes them. s₀: the verifier's
first state, as `chainFall` takes it. `none` for start: the chain is not reached. -/
structure ChainAt (S Cl W Y : Type) where
  lay : Lay
  steps : List (Step W Y)
  start : Option (ChainProgress S Cl W Y)
  s₀ : Option S

/-- **By the chain's first n rounds the run has met a fall.** -/
def fellBy (bs : List (Block S Cl)) (fs : List (Fall S)) (X : ChainAt S Cl W Y) (n : Nat)
    (dr : List Fmt.Drawn) : Bool :=
  match X.start, X.s₀ with
  | some a, some s =>
    match walk X.lay (X.steps.take n) (dr.take n) a with
    | .ok z => (chainFall fs X.lay.firstTree bs s ⟨roundsOf z.laid, z.cols⟩).isSome
    | .error _ => false
  | _, _ => false

theorem fellBy_take (bs : List (Block S Cl)) (fs : List (Fall S)) (X : ChainAt S Cl W Y) (n : Nat)
    (dr dr' : List Fmt.Drawn) (h : dr.take n = dr'.take n) :
    fellBy bs fs X n dr = fellBy bs fs X n dr' := by
  unfold fellBy
  rw [h]

/-! ## 2 One gate a member -/

section
variable (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (tail : List Fmt.Drawn)

/-- **The canonical gates.** all: the chain's whole flat list. skip: how many challenges stand in
front of the chain; X: what the chain's walk starts from, of these. j, n: the number of the first of
these members, and how many of the chain's rounds stand in front of it. p: the gates' numbers. tail:
fixed challenges of rounds behind these members that have no typed message (the first chain's
sealing round): the last gate walks on over them. -/
def coverGates : List (Block S Cl) → Nat → Nat → List RDT → List Gate
  | [], _, _, _ => []
  | [b], j, n, ds =>
    [⟨ds.take b.rounds.length, fun fr own =>
        (markOf ms b.place fr own).isSome ||
          fellBy all fs (X (fr.take skip)) (n + b.rounds.length + tail.length)
            (fr.drop skip ++ own ++ tail), p j⟩]
  | b :: b' :: bs, j, n, ds =>
    ⟨ds.take b.rounds.length, fun fr own =>
        (markOf ms b.place fr own).isSome ||
          fellBy all fs (X (fr.take skip)) (n + b.rounds.length) (fr.drop skip ++ own), p j⟩ ::
      coverGates (b' :: bs) (j + 1) (n + b.rounds.length) (ds.drop b.rounds.length)

theorem cover_ds : ∀ (bs : List (Block S Cl)) (j n : Nat) (ds : List RDT),
    ds.length = (bs.flatMap (·.rounds)).length →
    (coverGates all fs ms skip X p tail bs j n ds).flatMap (·.ds) = ds
  | [], _, _, ds, h => (List.eq_nil_of_length_eq_zero h).symm
  | [b], j, n, ds, h => by
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
    show ds.take b.rounds.length ++ [] = ds
    rw [List.append_nil, ← h, List.take_length]
  | b :: b' :: bs, j, n, ds, h => by
    rw [List.flatMap_cons, List.length_append] at h
    show ds.take b.rounds.length ++ (coverGates all fs ms skip X p tail (b' :: bs) (j + 1)
      (n + b.rounds.length) (ds.drop b.rounds.length)).flatMap (·.ds) = ds
    rw [cover_ds (b' :: bs) _ _ _ (by rw [List.length_drop]; omega), List.take_append_drop]

/-! ## 3 The last gate has it -/

/-- **Where the run has met a fall by the chain's last round, some gate has spoken.** base: the
challenges in front of the chain. dr: the chain's own typed ones. -/
theorem cover_chain (base dr : List Fmt.Drawn) (hb : base.length = skip) :
    ∀ (bs : List (Block S Cl)) (j n : Nat) (ds : List RDT), bs ≠ [] →
    ds.length = (bs.flatMap (·.rounds)).length →
    dr.length = n + (bs.flatMap (·.rounds)).length →
    fellBy all fs (X base) (n + (bs.flatMap (·.rounds)).length + tail.length) (dr ++ tail) =
      true →
    spoken (coverGates all fs ms skip X p tail bs j n ds) (base ++ dr.take n) (dr.drop n) = true
  | [], _, _, _, h, _, _, _ => absurd rfl h
  | [b], j, n, ds, _, hl, hd, hf => by
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl hd hf
    have hm : (ds.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    have e1 : (base ++ dr.take n).take skip = base := by
      rw [← hb]
      exact List.take_left' rfl
    have e2 : (base ++ dr.take n).drop skip = dr.take n := by
      rw [← hb]
      exact List.drop_left' rfl
    have e3 : dr.take n ++ (dr.drop n).take b.rounds.length = dr := by
      rw [← List.take_add, ← hd, List.take_length]
    show ((markOf ms b.place (base ++ dr.take n)
          ((dr.drop n).take (ds.take b.rounds.length).length)).isSome ||
        fellBy all fs (X ((base ++ dr.take n).take skip)) (n + b.rounds.length + tail.length)
          ((base ++ dr.take n).drop skip ++ (dr.drop n).take (ds.take b.rounds.length).length ++
            tail) || false) = true
    rw [hm, e1, e2, e3, hf]
    simp
  | b :: b' :: bs, j, n, ds, _, hl, hd, hf => by
    rw [List.flatMap_cons, List.length_append] at hl hd hf
    have hm : (ds.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    have e3 : dr.take n ++ (dr.drop n).take b.rounds.length = dr.take (n + b.rounds.length) :=
      List.take_add.symm
    have ih := cover_chain base dr hb (b' :: bs) (j + 1) (n + b.rounds.length)
      (ds.drop b.rounds.length) (by simp) (by rw [List.length_drop]; omega)
      (by rw [Nat.add_assoc]; exact hd)
      (by rw [Nat.add_assoc n b.rounds.length]; exact hf)
    show ((markOf ms b.place (base ++ dr.take n)
          ((dr.drop n).take (ds.take b.rounds.length).length)).isSome ||
        fellBy all fs (X ((base ++ dr.take n).take skip)) (n + b.rounds.length)
          ((base ++ dr.take n).drop skip ++ (dr.drop n).take (ds.take b.rounds.length).length) ||
      spoken (coverGates all fs ms skip X p tail (b' :: bs) (j + 1) (n + b.rounds.length)
          (ds.drop b.rounds.length))
        (base ++ dr.take n ++ (dr.drop n).take (ds.take b.rounds.length).length)
        ((dr.drop n).drop (ds.take b.rounds.length).length)) = true
    rw [hm, List.append_assoc, e3, List.drop_drop, ih]
    simp

end

end ProofFile.Honest

#print axioms ProofFile.Honest.fellBy_take
#print axioms ProofFile.Honest.cover_ds
#print axioms ProofFile.Honest.cover_chain
