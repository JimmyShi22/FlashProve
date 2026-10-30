-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/VecFlat.lean: matrices written end to end in rows of a fixed length.

A relation is about a family of matrices m a, a : A, with rows a rows of len a entries: the logical
form. A code has a fixed message length M a, which has nothing to do with len a. So the matrix a is
sent end to end: its entry (i, j) has the flat index i · len a + j and is in the row (i · len a + j)
/ M a, at the position (i · len a + j) % M a, of a vector with ⌈rows a · len a / M a⌉ rows of M a
entries: the physical form. Throughout, the set C of challenges is nonempty and every code has
n > 0.
 * `Flat.rFlat`: the round of the physical form (a round `vRoundK`, so that all that is proved of
   such rounds applies).
 * `Flat.unflat`: how a physical message is read: the logical form. What comes after the last entry
   is not read.
 * `Flat.flat`: the physical form of a logical message, filled up with 0. `Flat.unflat_flat`: for M
   a > 0, reading it gives the logical message back.
Further names: `Flat.nRows`, `row`, `pos`; `Flat.eFlat`, `read`, `src`. Used by
Blocks/VecFlatTrack.lean.
-/
import Blocks.BlockFront
import Blocks.StageData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Flat

open Iop

/-! ## 1. Numbers -/

/-- ⌈r l / M⌉ -/
def nRows (r l M : ℕ) : ℕ := (r * l + M - 1) / M

/-- the row and the position of the entry (i, j) of a matrix with rows of l entries -/
def row (l M i j : ℕ) : ℕ := (i * l + j) / M
def pos (l M i j : ℕ) : ℕ := (i * l + j) % M

theorem flat_lt {r l i j : ℕ} (hi : i < r) (hj : j < l) : i * l + j < r * l :=
  calc i * l + j < i * l + l := by omega
    _ = (i + 1) * l := by ring
    _ ≤ r * l := Nat.mul_le_mul_right _ hi

theorem row_lt {r l M i j : ℕ} (hM : 0 < M) (hi : i < r) (hj : j < l) :
    row l M i j < nRows r l M := by
  unfold row nRows
  have h := flat_lt hi hj
  rw [Nat.div_lt_iff_lt_mul hM]
  have h2 := Nat.div_add_mod (r * l + M - 1) M
  have h3 := Nat.mod_lt (r * l + M - 1) hM
  rw [Nat.mul_comm] at h2
  omega

theorem pos_lt {M : ℕ} (hM : 0 < M) (l i j : ℕ) : pos l M i j < M := Nat.mod_lt _ hM

theorem row_mul_add_pos (l M i j : ℕ) : row l M i j * M + pos l M i j = i * l + j :=
  Nat.div_add_mod' _ _

/-- With M = l > 0 nothing moves. (`row_self`, `pos_self`: for j < l) -/
theorem nRows_self (r : ℕ) {l : ℕ} (hl : 0 < l) : nRows r l l = r := by
  unfold nRows
  rw [Nat.add_sub_assoc hl, Nat.mul_comm, Nat.mul_add_div hl,
    Nat.div_eq_of_lt (by omega), Nat.add_zero]
theorem row_self {l i j : ℕ} (hj : j < l) : row l l i j = i := by
  unfold row
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]
theorem pos_self {l i j : ℕ} (hj : j < l) : pos l l i j = j := by
  unfold pos
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-! ## 2. The round, its reading, the honest message -/

section Round

variable (E F : Type) [Field F] [Field E] [Algebra F E] (A : Type) (overF : A → Bool)
  (rows len M : A → ℕ) (K C : Type) [Fintype C] [Nonempty C]

/-- the logical form -/
abbrev Log : Type := ∀ a, Fin (rows a) → Fin (len a) → Kf F E (overF a)

/-- The round of the physical form. -/
abbrev rFlat : Round := vRoundK E F A overF (fun a => nRows (rows a) (len a) (M a)) M K C

variable {E F A overF rows len M K C}

/-- a physical message, indexed by natural numbers; 0 outside -/
def at' (o : (rFlat E F A overF rows len M K C).Orc) (a : A) (r t : ℕ) : Kf F E (overF a) :=
  nat (fun r' => nat (o a r') t) r

/-- How a physical message is read. -/
def unflat (o : (rFlat E F A overF rows len M K C).Orc) : Log E F A overF rows len := fun a i j =>
  at' o a (row (len a) (M a) i.val j.val) (pos (len a) (M a) i.val j.val)

variable (M K C) in
/-- The physical form of a logical message, filled up with 0. -/
def flat (m : Log E F A overF rows len) : (rFlat E F A overF rows len M K C).Orc := fun a r t =>
  nat (fun i => nat (m a i) ((r.val * M a + t.val) % len a)) ((r.val * M a + t.val) / len a)

private theorem nat_fin {X : Type} [Zero X] {n : ℕ} (f : Fin n → X) (j : Fin n) :
    nat f j.val = f j := by
  unfold nat
  rw [dif_pos j.2]

private theorem nat_lt {X : Type} [Zero X] {n : ℕ} (f : Fin n → X) {t : ℕ} (h : t < n) :
    nat f t = f ⟨t, h⟩ := by
  unfold nat
  rw [dif_pos h]

/-- Under hM: reading the physical form gives the logical message back. -/
theorem unflat_flat (hM : ∀ a, 0 < M a) (m : Log E F A overF rows len) :
    unflat (flat M K C m) = m := by
  funext a i j
  unfold unflat at'
  rw [nat_lt _ (row_lt (hM a) i.2 j.2), nat_lt _ (pos_lt (hM a) _ _ _)]
  show nat (fun i' =>
        nat (m a i')
          ((row (len a) (M a) i.val j.val * M a + pos (len a) (M a) i.val j.val) % len a))
      ((row (len a) (M a) i.val j.val * M a + pos (len a) (M a) i.val j.val) / len a) = m a i j
  rw [row_mul_add_pos]
  have e1 : (i.val * len a + j.val) / len a = i.val := row_self j.2
  have e2 : (i.val * len a + j.val) % len a = j.val := pos_self j.2
  rw [e1, e2, nat_fin (fun i' => nat (m a i') j.val) i, nat_fin (m a i) j]

end Round

/-! ## 3. Encoding data, and the condition that tracking data (`Core.Track`, Blocks/StageTrack.lean)
need -/

section Enc

variable (E : Type) {F : Type} [Field F] [Field E] [Algebra F E] (A : Type) [Fintype A]
  [DecidableEq A] (overF : A → Bool) (rows len M : A → ℕ) (code : A → Code.Enc F) (mrow : A → ℕ)
  (role : A → Role) (q : A → ℕ) (hlen : ∀ a, (code a).msg = M a) [∀ a, Nonempty (Fin (code a).n)]
  (K C : Type) [Fintype C] [Nonempty C]

/-- The encoding data of the physical form, for codes with the message lengths M a. -/
def eFlat : REnc F E (rFlat E F A overF rows len M K C) :=
  REnc.ofVKc E A overF code (fun a => nRows (rows a) (len a) (M a)) mrow role q M hlen K C

variable {E A overF rows len M K C}

private theorem toE_nat {b : Bool} {n : ℕ} (f : Fin n → Kf F E b) (t : ℕ) :
    (nat f t).toE = nat (fun j => (f j).toE) t := by
  unfold nat
  split_ifs
  · rfl
  · exact Kf.toE_zero b

/-- For codes with the message lengths M a (`hlen`): the entry (i, j) of the matrix a is the entry
of the vector a at the row and the position of its flat index. -/
theorem read (o : (rFlat E F A overF rows len M K C).Orc) (a : A)
    (i : Fin (rows a)) (j : Fin (len a)) :
    (unflat o a i j).toE =
      nat (fun r' =>
          nat ((eFlat E A overF rows len M code mrow role q hlen K C).vecE o a r')
            (pos (len a) (M a) i.val j.val))
        (row (len a) (M a) i.val j.val) := by
  unfold unflat at' eFlat
  rw [toE_nat]
  congr 1
  funext r'
  rw [REnc.nat_vecE_ofVKc, toE_nat]

/-- where the entry (i, j) of the matrix a is: vector, row, position -/
def src (len M : A → ℕ) (a : A) (i j : ℕ) : A × ℕ × ℕ :=
  (a, row (len a) (M a) i j, pos (len a) (M a) i j)

variable (E A overF rows len M K C) in
/-- The numbering of the round (Blocks/StageData.lean). -/
def nFlat [FinEnum E] [FinEnum A] [FinEnum K] [IdxK K] [FinEnum C] [ChalK E C] :
    RNum (eFlat E A overF rows len M code mrow role q hlen K C) :=
  RNum.ofVKc A overF code (fun a => nRows (rows a) (len a) (M a)) mrow role q M hlen K C

/-- What the encoding data say of the vector a. -/
theorem eFlat_code (a : A) :
    (eFlat E A overF rows len M code mrow role q hlen K C).code a = code a := rfl
theorem eFlat_rows (a : A) :
    (eFlat E A overF rows len M code mrow role q hlen K C).rows a = nRows (rows a) (len a) (M a) :=
  rfl
theorem eFlat_mrow (a : A) :
    (eFlat E A overF rows len M code mrow role q hlen K C).mrow a = mrow a := rfl
theorem eFlat_role (a : A) :
    (eFlat E A overF rows len M code mrow role q hlen K C).role a = role a := rfl
theorem eFlat_q (a : A) : (eFlat E A overF rows len M code mrow role q hlen K C).q a = q a := rfl

end Enc

end Blocks.Flat
