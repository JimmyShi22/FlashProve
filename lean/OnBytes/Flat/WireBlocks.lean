-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/WireBlocks.lean: the number of blocks for the one wire of the three files' protocols,
by definition, with the bounds that the wire records ask of it.

The wire records of a key file, an entry file and a proof file share one number K of blocks, and ask
that no round's verifier message needs more than K blocks.

Main names.
  `blocksT f l`: the greatest number of blocks that a round of the list l needs, at the field f.
  `kThree f DK ds DP`: the greatest of the three files' numbers.
  `kThree_key`, `kThree_entry`, `kThree_proof`: no round of the key file's data DK, of the entry's
    data ds, of the proof file's data DP needs more blocks, whatever the data.
  `le_kThree_entry`: it is at least the entry's own number (`kMax`, Run/PlanQWire.lean).

Limits: bounds on data, true by the definition of the number. The number is evaluated at no data
here. Nothing on a wire's other laws, on soundness, on bytes or files.


-/
import OnBytes.Maker.Whole
import Run.PlanQRun

set_option autoImplicit false

namespace OnBytes.Flat
open OnBytes.Maker _root_.Run _root_.Run.PQ

/-- The greatest number of blocks that a round of the list needs. -/
def blocksT (f : Fmt.Fld) (l : List RDT) : ℕ :=
  l.foldl (fun a d => max a (bsRound f d.entry d.kind).b) 0

/-- A fold by the greater is at least its start and at least every member's value. -/
theorem foldl_max_ge {α : Type} (g : α → ℕ) : ∀ (l : List α) (n : ℕ),
    n ≤ l.foldl (fun a d => max a (g d)) n ∧ ∀ d ∈ l, g d ≤ l.foldl (fun a d => max a (g d)) n
  | [], n => ⟨Nat.le_refl n, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, n => by
    obtain ⟨h1, h2⟩ := foldl_max_ge g l (max n (g x))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun d hd => ?_⟩
    rcases List.mem_cons.1 hd with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 d h

/-- No round of the list needs more blocks. -/
theorem le_blocksT (f : Fmt.Fld) (l : List RDT) :
    ∀ d ∈ l, (bsRound f d.entry d.kind).b ≤ blocksT f l :=
  (foldl_max_ge (fun d : RDT => (bsRound f d.entry d.kind).b) l 0).2

/-- The number of blocks for the three files' one wire: the greatest of the three. -/
def kThree (f : Fmt.Fld) (DK : WholeD) (ds : List RD) (DP : WholeD) : ℕ :=
  max (blocksT f (DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃)))
    (max (kMax (fun e k => (bsRound f e k).b) ds) (blocksT f (DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃))))

section
variable (f : Fmt.Fld) (DK : WholeD) (ds : List RD) (DP : WholeD)

/-- No round of the key file's data needs more blocks. -/
theorem kThree_key : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃),
    (bsRound f d.entry d.kind).b ≤ kThree f DK ds DP :=
  fun d hd => Nat.le_trans (le_blocksT f (DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃)) d hd) (Nat.le_max_left _ _)

/-- It is at least the entry's own number. -/
theorem le_kThree_entry : kMax (fun e k => (bsRound f e k).b) ds ≤ kThree f DK ds DP :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- No round of the entry's data needs more blocks. -/
theorem kThree_entry : ∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ kThree f DK ds DP :=
  fun d hd => Nat.le_trans
    ((foldl_max_ge (fun d : RD => (bsRound f d.entry d.kind).b) ds 0).2 d hd)
    (le_kThree_entry f DK ds DP)

/-- No round of the proof file's data needs more blocks. -/
theorem kThree_proof : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃),
    (bsRound f d.entry d.kind).b ≤ kThree f DK ds DP :=
  fun d hd => Nat.le_trans (le_blocksT f (DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃)) d hd)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

end

end OnBytes.Flat
