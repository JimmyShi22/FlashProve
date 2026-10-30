-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1BaseOps.lean: the two sides of BASE's linear check and the right side of its check at a
position, written over a structure of field operations (Fmt/M1PscOps.lean: `FOps`); and what
"baseOK = true" says, written out. At the format's field they are the sides that the decision
compares; they commute with every map that respects the operations.

The first toy is a small test protocol of the programs (Fmt/M1Types.lean, the head). A block is one
step of it, as the verifier's function of what was sent, drawn and opened. BASE is the first toy's
last block (Fmt/M1Fold.lean: `baseB1`, `baseB2At`, `baseOK`). BASE has a linear check on the
vectors M0, M1 that the prover sends last, and a second check at every drawn position. Both
checks test equations.
BASE is the one block in which elements of the field are tested. Elsewhere the decision tests the
sizes, numbers of elements, lengths, and that a column was opened.
Definitions that compute; theorems; tests (#guard). Core Lean, no Mathlib.

The codes' symbols are not made generic (not written over `FOps`). The left sides of the second
check are the symbols of an encoding at a position (`symE`, Fmt/M1Codes.lean). `symE` computes in
the format's second field whatever f is. Here they stay as they are. This file does not name them in
the field.

Main names:
  `dotLG`, `dotG`: the product of two vectors, as in the vector arithmetic of Fmt/M1Types.lean (it
    ends where the shorter one ends).
  `b1L`, `b1R`: the two sides of the linear check: <c, M0> + <d, M1>; tau* + lambda tau.
  `b2R`: the right side of the check at a position: (the masking word's symbol) + lambda (the last
    message's symbol).
  `baseB1_at`, `baseB2At_at`: the functions of Fmt/M1Fold.lean are "decide (left = right)" at
    `opsOf f` (`baseB2At`: two such, joined by "and").
  `map_dotL`, `map_dot`, `map_b1L`, `map_b1R`, `map_b2R`: under a map that respects the operations
    (`FOps.Hom A B φ`), φ of the function at A is the function at B at the arguments under φ.
  `baseOK_iff`: baseOK .. = true ↔ the four lengths are the codes'; b1L = b1R; and at every drawn
    position x a column o was opened, and the two symbols are b2R of o's parts.

Tests: `dotG`, `b1R` and `b2R` at another carrier (the integers modulo 101).

Notation: `mul`, `mulF`: two fields of `FOps` (Fmt/M1PscOps.lean); at `opsOf f` they are `mulE` and
`mulEF`; o: a four-tuple (`baseB2At`, Fmt/M1Fold.lean, tells each part): o.1 and o.2.1 are `b2R`'s s
and g at the code C, o.2.2.1 and o.2.2.2 at Z; `cp Z x`: x modulo Z's length (Fmt/M1Codes.lean).

Limits: this file does not say that equality of words is equality in the field. That is a matter for
the file that has the map to the field; both sides of each equation are results of operations. This
file proves `FOps.Hom` of no map, so the map to the field is not in it. This file does not say
anything on a protocol.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1PscOps
import Fmt.M1Fold

set_option autoImplicit false

namespace Fmt.M1

section
variable {α : Type} (A : FOps α)

def dotLG : List α → List α → α → α
  | a :: u, b :: v, acc => dotLG u v (A.add acc (A.mulF a b))
  | _, _, acc => acc

def dotG (u v : Array α) : α := dotLG A u.toList v.toList A.zero

/-- the left side of the linear check -/
def b1L (c d : Array α) (M0 M1 : List α) : α := A.add (dotG A c M0.toArray) (dotG A d M1.toArray)

/-- its right side -/
def b1R (tau tauS lam : α) : α := A.add tauS (A.mul lam tau)

/-- the right side of the check at a position: g: the masking word's symbol; s: the last
message's -/
def b2R (lam g s : α) : α := A.add g (A.mul lam s)

end

/-! ## At the format's operations -/

theorem dotL_at (f : Fld) : ∀ (u v : List E) (acc : E), dotL f u v acc = dotLG (opsOf f) u v acc
  | a :: u, b :: v, acc => dotL_at f u v (f.addE acc (f.mulEF a b))
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem dot_at (f : Fld) (u v : Array E) : dot f u v = dotG (opsOf f) u v := dotL_at f _ _ _

theorem baseB1_at (f : Fld) (c d : Array E) (tau tauS lam : E) (M0 M1 : List E) :
    baseB1 f c d tau tauS lam M0 M1 =
      decide (b1L (opsOf f) c d M0 M1 = b1R (opsOf f) tau tauS lam) := by
  unfold baseB1 b1L
  rw [dot_at, dot_at]
  rfl

theorem baseB2At_at (f : Fld) (C Z : Code) (lam : E) (M0 M1 R0 R1 : List E)
    (x : Nat) (o : E × E × E × E) :
    baseB2At f C Z lam M0 M1 R0 R1 x o =
      (decide (symE C x M0 R0 = b2R (opsOf f) lam o.2.1 o.1) &&
        decide (symE Z (cp Z x) M1 R1 = b2R (opsOf f) lam o.2.2.2 o.2.2.1)) := rfl

/-- What "baseOK = true" says, written out. In words: the head, "Main names". -/
theorem baseOK_iff (f : Fld) (C Z : Code) (c d : Array E) (tau tauS lam : E) (M0 M1 R0 R1 : List E)
    (xs : List Nat) (col : Nat → Option (E × E × E × E)) :
    baseOK f C Z c d tau tauS lam M0 M1 R0 R1 xs col = true ↔
    (M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r) ∧
    b1L (opsOf f) c d M0 M1 = b1R (opsOf f) tau tauS lam ∧
    ∀ x ∈ xs, ∃ o,
      col x = some o ∧
      symE C x M0 R0 = b2R (opsOf f) lam o.2.1 o.1 ∧
      symE Z (cp Z x) M1 R1 = b2R (opsOf f) lam o.2.2.2 o.2.2.1 := by
  unfold baseOK
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, baseB1_at, decide_eq_true_iff,
    List.all_eq_true, and_assoc]
  refine and_congr_right fun _ =>
    and_congr_right fun _ => forall_congr' fun x => imp_congr_right fun _ => ?_
  cases col x with
  | none => exact ⟨fun h => Bool.noConfusion h, fun ⟨_, h, _⟩ => nomatch h⟩
  | some o =>
      show baseB2At f C Z lam M0 M1 R0 R1 x o = true ↔ _
      rw [baseB2At_at, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      exact ⟨fun h => ⟨o, rfl, h⟩, fun ⟨_, e, h⟩ => Option.some.inj e ▸ h⟩

/-! ## Maps that respect the operations -/

section
variable {α β : Type} {A : FOps α} {B : FOps β} {φ : α → β} (h : FOps.Hom A B φ)
include h

theorem map_dotL :
    ∀ (u v : List α) (acc : α), φ (dotLG A u v acc) = dotLG B (u.map φ) (v.map φ) (φ acc)
  | a :: u, b :: v, acc => by
      show φ (dotLG A u v (A.add acc (A.mulF a b))) =
        dotLG B (u.map φ) (v.map φ) (B.add (φ acc) (B.mulF (φ a) (φ b)))
      rw [map_dotL u v, h.add, h.mulF]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem map_dot (u v : Array α) : φ (dotG A u v) = dotG B (u.map φ) (v.map φ) := by
  unfold dotG
  rw [map_dotL h, h.zero, Array.toList_map, Array.toList_map]

theorem map_b1L (c d : Array α) (M0 M1 : List α) :
    φ (b1L A c d M0 M1) = b1L B (c.map φ) (d.map φ) (M0.map φ) (M1.map φ) := by
  unfold b1L
  rw [h.add, map_dot h, map_dot h, List.map_toArray (l := M0), List.map_toArray (l := M1)]

theorem map_b1R (tau tauS lam : α) : φ (b1R A tau tauS lam) = b1R B (φ tau) (φ tauS) (φ lam) := by
  unfold b1R
  rw [h.add, h.mul]

theorem map_b2R (lam g s : α) : φ (b2R A lam g s) = b2R B (φ lam) (φ g) (φ s) := by
  unfold b2R
  rw [h.add, h.mul]

end

/-! ## Tests at another carrier -/

#guard dotG OpsT.m101 #[1, 2, 3] #[10, 20, 30] == (10 + 40 + 90) % 101
-- it ends where the shorter vector ends
#guard dotG OpsT.m101 #[1, 2, 3] #[10, 20] == 50 && dotG OpsT.m101 #[1, 2] #[10, 20, 30] == 50
#guard b1R OpsT.m101 7 5 3 == 26 && b2R OpsT.m101 3 5 7 == 26

end Fmt.M1
