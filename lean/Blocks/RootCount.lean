-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RootCount.lean: upper bounds on the number of prover messages that have an oracle.

The compiler for Batch takes a root only for a component of a prover message that has a tree
(Iop/BatchWire.lean: `has0`, `hasJ`). The generic wires (Iop/BatchWireDraw.lean) give a component a
tree exactly if it has an oracle position. So the number of roots (`nRootsB`) is at most the number
of rounds with an oracle position (`nOrc`), if the annotation follows the same rule in every round
and under this rule a round has at most `orcR` roots (`nRootsB_const_le`). (Words of this library:
lean/GLOSSARY.md.)
Here: `orcR`, `nOrc` (of a shape); `rootsR`, `nRootsB` (with an annotation for Batch, `RoundSplits`);
bounds for an encoded shape (Blocks/BlockFront.lean) and for the levels (the recursive column test
of Blocks/LevelDef.lean).

Limits: all inequalities here are upper bounds. The file says nothing on sizes:
Compile/Batch/Size.lean (`cRoots`) does.
-/
import Blocks.SizesFr
import Iop.BatchWireOf

set_option autoImplicit false

namespace Blocks
open Iop

/-! ## Rounds with an oracle position -/

/-- 1 if n is positive, else 0 -/
def pos01 (n : ℕ) : ℕ := (decide (0 < n)).toNat

theorem pos01_le_one (n : ℕ) : pos01 n ≤ 1 := Bool.toNat_le _

theorem pos01_zero : pos01 0 = 0 := rfl

theorem pos01_mono {a b : ℕ} (h : a ≤ b) : pos01 a ≤ pos01 b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Nat.zero_le _
  · have hb : 0 < b := lt_of_lt_of_le ha h
    simp [pos01, ha, hb]

/-- 1 if the round has an oracle position, else 0 -/
def orcR {r : Round} (pt : r.IsPoint) : ℕ := pos01 (@Fintype.card r.Pos pt.finPos)

/-- The number of rounds with an oracle position. -/
def nOrc : (s : Shape) → s.IsPoint → ℕ
  | [], _ => 0
  | _ :: s, (pt, pts) => orcR pt + nOrc s pts

theorem orcR_le_one {r : Round} (pt : r.IsPoint) : orcR pt ≤ 1 := pos01_le_one _

/-- a message without oracles -/
theorem orcR_plain (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dPlain : Plain) :
    orcR (plainPoint Plain Chal dPlain) = 0 := rfl

/-- a message of several oracles counts at most their number (for a nonempty type of challenges) -/
theorem orcR_words_le (A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (Sy : A → Type)
    (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dSy : ∀ a, Sy a) (dPlain : Plain) :
    orcR (wordsPoint A n Sy Plain Chal dSy dPlain) ≤ Fintype.card A := by
  rcases Nat.eq_zero_or_pos (Fintype.card A) with h | h
  · haveI : IsEmpty A := Fintype.card_eq_zero_iff.1 h
    show pos01 (Fintype.card (Σ a, Fin (n a))) ≤ _
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
  · exact le_trans (orcR_le_one _) h

theorem nOrc_le_length : ∀ (s : Shape) (pts : s.IsPoint), nOrc s pts ≤ s.length
  | [], _ => Nat.le_refl _
  | _ :: s, (pt, pts) => by
      have h1 := orcR_le_one pt
      have h2 := nOrc_le_length s pts
      show orcR pt + nOrc s pts ≤ s.length + 1
      omega

theorem nOrc_app :
    ∀ {s t : Shape} (a : s.IsPoint) (b : t.IsPoint),
      nOrc (s ++ t) (pointApp a b) = nOrc s a + nOrc t b
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (pt, a), b => by
      show orcR pt + nOrc _ (pointApp a b) = orcR pt + nOrc _ a + _
      rw [nOrc_app a b, Nat.add_assoc]

theorem nOrc_rep (r : Round) (h : r.IsPoint) :
    ∀ (n : ℕ) {t : Shape} (b : t.IsPoint),
      nOrc (List.replicate n r ++ t) (pointRep r h n b) = n * orcR h + nOrc t b
  | 0, _, _ => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | n + 1, _, b => by
      show orcR h + nOrc _ (pointRep r h n b) = _
      rw [nOrc_rep r h n b, Nat.succ_mul]
      omega

/-! ## With an annotation for batches -/

/-- the roots of one round: that of the slot's component, and in a shared round that of the shared
component; each only if the component has a position -/
def rootsR {r : Round} (a : RAnn r) (pt : r.IsPoint) : ℕ :=
  (match a.kind with | .lo => 0 | .sh => pos01 (a.card0 pt)) + pos01 (a.cardJ pt)

/-- The roots of a batch IOP over the generic wire, summed over the rounds. -/
def nRootsB : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => rootsR a pt + nRootsB s A pts

theorem rootsR_le {r : Round} (a : RAnn r) (pt : r.IsPoint) :
    rootsR a pt ≤ pos01 (a.card0 pt) + pos01 (a.cardJ pt) := by
  unfold rootsR
  cases a.kind
  · exact Nat.le_refl _
  · exact Nat.add_le_add_right (Nat.zero_le _) _

theorem card0_ofSlot (k : Kind) (r : Round) (pt : r.IsPoint) : (RAnn.ofSlot k r).card0 pt = 0 := by
  letI := pt.finPos
  exact Fintype.card_eq_zero_iff.2 ⟨fun x => Bool.noConfusion x.2⟩

theorem cardJ_ofShared (k : Kind) (r : Round) (pt : r.IsPoint) :
    (RAnn.ofShared k r).cardJ pt = 0 := by
  letI := pt.finPos
  exact Fintype.card_eq_zero_iff.2 ⟨fun x => Bool.noConfusion x.2⟩

theorem card0_le {r : Round} (a : RAnn r) (pt : r.IsPoint) :
    a.card0 pt ≤ @Fintype.card r.Pos pt.finPos := by
  letI := pt.finPos
  exact Fintype.card_subtype_le _

theorem cardJ_le {r : Round} (a : RAnn r) (pt : r.IsPoint) :
    a.cardJ pt ≤ @Fintype.card r.Pos pt.finPos := by
  letI := pt.finPos
  exact Fintype.card_subtype_le _

/-- a round in which only the slots send -/
theorem rootsR_ofSlot (k : Kind) (r : Round) (pt : r.IsPoint) :
    rootsR (RAnn.ofSlot k r) pt ≤ orcR pt := by
  refine le_trans (rootsR_le _ pt) ?_
  rw [card0_ofSlot, pos01_zero, Nat.zero_add]
  exact pos01_mono (cardJ_le _ pt)

/-- a round in which only the shared part is sent -/
theorem rootsR_ofShared (k : Kind) (r : Round) (pt : r.IsPoint) :
    rootsR (RAnn.ofShared k r) pt ≤ orcR pt := by
  refine le_trans (rootsR_le _ pt) ?_
  rw [cardJ_ofShared, pos01_zero, Nat.add_zero]
  exact pos01_mono (card0_le _ pt)

theorem nRootsB_app : ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (a : s.IsPoint) (b : t.IsPoint),
    nRootsB (s ++ t) (RoundSplits.app A B) (pointApp a b) = nRootsB s A a + nRootsB t B b
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (x, A), B, (pt, a), b => by
      show rootsR x pt + nRootsB _ (RoundSplits.app A B) (pointApp a b) = rootsR x pt + nRootsB _ A a + _
      rw [nRootsB_app A B a b, Nat.add_assoc]

/-- the same rule of annotation in every round, under which a round has at most `orcR` roots: then
at most `nOrc` roots in all -/
theorem nRootsB_const_le (f : ∀ r : Round, RAnn r)
    (hf : ∀ (r : Round) (pt : r.IsPoint), rootsR (f r) pt ≤ orcR pt) :
    ∀ (s : Shape) (pts : s.IsPoint), nRootsB s (RoundSplits.const f s) pts ≤ nOrc s pts
  | [], _ => Nat.le_refl _
  | r :: s, (pt, pts) => Nat.add_le_add (hf r pt) (nRootsB_const_le f hf s pts)

theorem nRootsB_allLocal_le (s : Shape) (pts : s.IsPoint) :
    nRootsB s (RoundSplits.allLocal s) pts ≤ nOrc s pts :=
  nRootsB_const_le _ (fun r pt => rootsR_ofSlot .lo r pt) s pts

/-! ## Encoded shapes -/

section Enc
variable {F E : Type} [Field F] [Field E]

/-- An encoded shape has at most as many rounds with an oracle as it has vectors. -/
theorem nOrc_enc_le :
    ∀ (s : Shape) (d : EncData F E s),
      nOrc (encShape s d) (encPoint s d) ≤ EncData.sum (fun _ _ _ _ _ => 1) s d
  | [], _ => Nat.le_refl _
  | r :: s, (e, d) => by
      refine Nat.add_le_add
        (le_trans (orcR_words_le e.A _ _ r.Plain r.Chal _ _) ?_) (nOrc_enc_le s d)
      simp

end Enc

/-! ## The levels -/

section Levels
variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

omit [Field F] [DecidableEq E] [Algebra F E] in
/-- the levels: at most one message with an oracle for each later array -/
theorem nOrc_levels_le :
    ∀ (a : LevSpec F) (rest : List (LevSpec F)),
      nOrc (levelsShape E a rest) (levelsPoint E a rest) ≤ rest.length
  | a, [] => by
      show nOrc (List.replicate a.mu (LinSh.rSC E) ++ [a.rTheta E, a.rLast E])
          (pointRep (LinSh.rSC E) (plainPoint _ _ _) a.mu
            (plainPoint _ _ _, (plainPoint _ _ _, ()))) ≤ 0
      rw [nOrc_rep, orcR_plain, Nat.mul_zero]
      exact Nat.le_refl 0
  | a, b :: rest => by
      show nOrc
          (List.replicate a.mu (LinSh.rSC E) ++ (a.rTheta E :: a.rNext E b :: levelsShape E b rest))
          (pointRep (LinSh.rSC E) (plainPoint _ _ _) a.mu
            (plainPoint _ _ _,
              (wordsPoint Unit _ _ Unit _ (fun _ _ => 0) (), levelsPoint E b rest))) ≤
        rest.length + 1
      rw [nOrc_rep, orcR_plain, Nat.mul_zero, Nat.zero_add]
      have ih := nOrc_levels_le b rest
      have h1 := orcR_le_one
        (wordsPoint Unit (fun _ => b.code.n) (fun _ => Fin b.rows → E) Unit _
          (fun _ _ => 0) () : (a.rNext E b).IsPoint)
      show 0 + (orcR _ + nOrc (levelsShape E b rest) (levelsPoint E b rest)) ≤ rest.length + 1
      omega

end Levels

end Blocks
