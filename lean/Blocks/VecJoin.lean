-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/VecJoin.lean: several matrices of one message as one vector.

Blocks/VecFlat.lean writes each matrix m a, a : A, of a message end to end into the rows of a
separate vector. Here all matrices of the message, which must be over one field, are in one vector:
the entry (i, j) of the matrix a has the flat index off a + i · len a + j. The offsets are data
(`Join.Lay`); the condition (`Lay.OK`): the index ranges of the matrices are below the total length
and do not overlap. Throughout, the set C of challenges is nonempty and the code has n > 0.
 * `Join.offL`, `Lay.ofWeights w ord`, `ofWeights_ok`: the matrices in the order of a list that
   holds every a, the matrix a in a range of w a ≥ rows a · len a indices.
Further names: `Lay.endToEnd`; `Join.cat`, `uncat`, `uncat_cat`; `Join.rJoin`, `unjoin`, `join`,
`unjoin_join`; `Join.eJoin`, `read`, `src`, `nJoin`.
-/
import Blocks.VecFlat

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Join

open Iop

/-! ## 1. Offsets -/

/-- Where the matrices are in the one vector: the first index of each, and the total length. -/
structure Lay (A : Type) where
  off : A → ℕ
  tot : ℕ

/-- The condition: the range of each matrix is below the total length, and an index is in the range
of one matrix at most. -/
structure Lay.OK {A : Type} (L : Lay A) (rows len : A → ℕ) : Prop where
  le : ∀ a, L.off a + rows a * len a ≤ L.tot
  disj : ∀ a a' x, L.off a ≤ x → x < L.off a + rows a * len a → L.off a' ≤ x →
    x < L.off a' + rows a' * len a' → a = a'

section Weights

variable {A : Type} [DecidableEq A] (w : A → ℕ)

/-- the sum of the weights of the members of the list before a -/
def offL : List A → A → ℕ
  | [], _ => 0
  | b :: l, a => if a = b then 0 else w b + offL l a

theorem offL_add_le : ∀ (l : List A) {a : A}, a ∈ l → offL w l a + w a ≤ (l.map w).sum
  | b :: l, a, h => by
    by_cases e : a = b
    · subst e
      simp [offL]
    · have h' : a ∈ l := (List.mem_cons.mp h).resolve_left e
      have := offL_add_le l h'
      simp only [offL, if_neg e, List.map_cons, List.sum_cons]
      omega

theorem offL_disj :
    ∀ (l : List A) {a a' : A} {x : ℕ}, a ∈ l → a' ∈ l → offL w l a ≤ x → x < offL w l a + w a →
      offL w l a' ≤ x → x < offL w l a' + w a' → a = a'
  | b :: l, a, a', x, h, h', h1, h2, h3, h4 => by
    by_cases e : a = b <;> by_cases e' : a' = b
    · rw [e, e']
    · subst e
      simp only [offL, if_true, if_neg e'] at h1 h2 h3 h4
      omega
    · subst e'
      simp only [offL, if_true, if_neg e] at h1 h2 h3 h4
      omega
    · simp only [offL, if_neg e, if_neg e'] at h1 h2 h3 h4
      exact offL_disj l (x := x - w b) ((List.mem_cons.mp h).resolve_left e)
        ((List.mem_cons.mp h').resolve_left e') (by omega) (by omega) (by omega) (by omega)

/-- The matrices in the order of a list, the matrix a in a range of w a indices. -/
def Lay.ofWeights (ord : List A) : Lay A := ⟨offL w ord, (ord.map w).sum⟩

theorem ofWeights_ok {ord : List A} (hall : ∀ a, a ∈ ord)
    {rows len : A → ℕ} (hw : ∀ a, rows a * len a ≤ w a) :
    (Lay.ofWeights w ord).OK rows len where
  le := fun a => le_trans (Nat.add_le_add_left (hw a) _) (offL_add_le w ord (hall a))
  disj := fun a a' _ h1 h2 h3 h4 =>
    offL_disj w ord (hall a) (hall a') h1 (lt_of_lt_of_le h2 (Nat.add_le_add_left (hw a) _)) h3
      (lt_of_lt_of_le h4 (Nat.add_le_add_left (hw a') _))

variable (rows len : A → ℕ)

/-- each matrix directly after the other -/
def Lay.endToEnd (ord : List A) : Lay A := Lay.ofWeights (fun a => rows a * len a) ord

theorem endToEnd_ok {ord : List A} (hall : ∀ a, a ∈ ord) :
    (Lay.endToEnd rows len ord).OK rows len :=
  ofWeights_ok _ hall fun _ => le_rfl

theorem le_mul_nRows (r l : ℕ) {M : ℕ} (hM : 0 < M) : r * l ≤ M * Flat.nRows r l M := by
  unfold Flat.nRows
  have h2 := Nat.div_add_mod (r * l + M - 1) M
  have h3 := Nat.mod_lt (r * l + M - 1) hM
  omega


end Weights

/-! ## 2. The family of matrices as one long row -/

section Cat

variable {A X : Type} [Zero X] {rows len : A → ℕ} (L : Lay A)

/-- the index x is in the range of the matrix a -/
def inBlock (rows len : A → ℕ) (x : ℕ) (a : A) : Bool :=
  decide (L.off a ≤ x ∧ x < L.off a + rows a * len a)

/-- The long row: at an index in the range of a matrix of ord (the first such) its entry, else 0. -/
def cat (ord : List A) (m : ∀ a, Fin (rows a) → Fin (len a) → X) : Fin L.tot → X := fun x =>
  match ord.find? (inBlock L rows len x.val) with
  | some a => nat (fun i => nat (m a i) ((x.val - L.off a) % len a)) ((x.val - L.off a) / len a)
  | none => 0

/-- Back: the entry (i, j) of the matrix a is at the index off a + i · len a + j. -/
def uncat (v : Fin L.tot → X) : ∀ a, Fin (rows a) → Fin (len a) → X := fun a i j =>
  nat v (L.off a + (i.val * len a + j.val))

private theorem nat_fin {n : ℕ} (f : Fin n → X) (j : Fin n) : nat f j.val = f j := by
  unfold nat
  rw [dif_pos j.2]

private theorem nat_lt {n : ℕ} (f : Fin n → X) {t : ℕ} (h : t < n) : nat f t = f ⟨t, h⟩ := by
  unfold nat
  rw [dif_pos h]

variable {L}

theorem idx_lt (h : L.OK rows len) (a : A) (i : Fin (rows a)) (j : Fin (len a)) :
    L.off a + (i.val * len a + j.val) < L.tot :=
  lt_of_lt_of_le (Nat.add_lt_add_left (Flat.flat_lt i.2 j.2) _) (h.le a)

theorem uncat_cat (h : L.OK rows len) {ord : List A} (hall : ∀ a, a ∈ ord)
    (m : ∀ a, Fin (rows a) → Fin (len a) → X) : uncat L (cat L ord m) = m := by
  funext a i j
  unfold uncat
  rw [nat_lt _ (idx_lt h a i j)]
  have hin : inBlock L rows len (L.off a + (i.val * len a + j.val)) a = true :=
    decide_eq_true ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Flat.flat_lt i.2 j.2) _⟩
  unfold cat
  dsimp only
  cases hf : ord.find? (inBlock L rows len (L.off a + (i.val * len a + j.val))) with
  | none => exact absurd hin (by simpa using List.find?_eq_none.mp hf a (hall a))
  | some a' =>
    have h' : inBlock L rows len (L.off a + (i.val * len a + j.val)) a' = true := List.find?_some hf
    obtain ⟨h1, h2⟩ := of_decide_eq_true h'
    obtain ⟨h3, h4⟩ := of_decide_eq_true hin
    obtain rfl := h.disj a' a _ h1 h2 h3 h4
    show nat (fun i' => nat (m a' i') ((L.off a' + (i.val * len a' + j.val) - L.off a') % len a'))
        ((L.off a' + (i.val * len a' + j.val) - L.off a') / len a') = m a' i j
    rw [Nat.add_sub_cancel_left,
      show (i.val * len a' + j.val) / len a' = i.val from Flat.row_self j.2,
      show (i.val * len a' + j.val) % len a' = j.val from Flat.pos_self j.2,
      nat_fin (fun i' => nat (m a' i') j.val) i, nat_fin (m a' i) j]

end Cat

/-! ## 3. The round, its reading, the honest message -/

section Round

variable (E F : Type) [Field F] [Field E] [Algebra F E] {A : Type} (b : Bool) (rows len : A → ℕ)
  (L : Lay A) (M : ℕ) (K C : Type) [Fintype C] [Nonempty C]

/-- the logical form: matrices over one field -/
abbrev Log : Type := Flat.Log E F A (fun _ => b) rows len

/-- The round: one vector, the long row written into rows of M entries. -/
abbrev rJoin : Round :=
  Flat.rFlat E F Unit (fun _ => b) (fun _ => 1) (fun _ => L.tot) (fun _ => M) K C

variable {E F b rows len L M K C}

/-- How a message is read. -/
def unjoin (o : (rJoin E F b L M K C).Orc) : Log E F b rows len :=
  uncat L fun x => Flat.unflat o () 0 x

variable (L M K C) in
/-- The honest message. -/
def join (ord : List A) (m : Log E F b rows len) : (rJoin E F b L M K C).Orc :=
  Flat.flat (E := E) (F := F) (overF := fun _ : Unit => b) (rows := fun _ => 1)
    (len := fun _ => L.tot) (fun _ => M) K C fun _ _ => cat L ord m

/-- Under hM, h, hall: reading the honest message gives the matrices back. -/
theorem unjoin_join (hM : 0 < M) (h : L.OK rows len) {ord : List A}
    (hall : ∀ a, a ∈ ord) (m : Log E F b rows len) :
    unjoin (join L M K C ord m) = m := by
  unfold unjoin join
  rw [Flat.unflat_flat fun _ => hM]
  exact uncat_cat h hall m

end Round

/-! ## 4. Encoding data, and the condition that tracking data (`Core.Track`, Blocks/StageTrack.lean)
need -/

section Enc

variable (E : Type) {F : Type} [Field F] [Field E] [Algebra F E] {A : Type} (b : Bool)
  {rows len : A → ℕ} (L : Lay A) (M : ℕ) (code : Code.Enc F) (mrow : ℕ) (role : Role) (q : ℕ)
  (hlen : code.msg = M) [Nonempty (Fin code.n)] (K C : Type) [Fintype C] [Nonempty C]

/-- The encoding data: one code. -/
def eJoin : REnc F E (rJoin E F b L M K C) :=
  Flat.eFlat E Unit (fun _ => b) (fun _ => 1) (fun _ => L.tot) (fun _ => M) (fun _ => code)
    (fun _ => mrow) (fun _ => role) (fun _ => q) (fun _ => hlen) K C

/-- where the entry (i, j) of the matrix a is: the vector, the row, the position -/
def src (len : A → ℕ) (a : A) (i j : ℕ) : Unit × ℕ × ℕ :=
  Flat.src (fun _ : Unit => L.tot) (fun _ => M) () 0 (L.off a + (i * len a + j))

/-- The numbering of the round. -/
def nJoin [FinEnum E] [FinEnum K] [IdxK K] [FinEnum C] [ChalK E C] :
    RNum (eJoin E b L M code mrow role q hlen K C) :=
  Flat.nFlat E Unit (fun _ => b) (fun _ => 1) (fun _ => L.tot) (fun _ => M) (fun _ => code)
    (fun _ => mrow) (fun _ => role) (fun _ => q) (fun _ => hlen) K C

variable {E b L M K C}

private theorem nat_lt' {X : Type} [Zero X] {n : ℕ} (f : Fin n → X) {t : ℕ} (h : t < n) :
    nat f t = f ⟨t, h⟩ := by
  unfold nat
  rw [dif_pos h]

/-- Under `Lay.OK` and hlen (the code's message length is M), the entry (i, j) of the matrix a is
the entry of the one vector at the row and the position of its flat index. -/
theorem read (h : L.OK rows len) (o : (rJoin E F b L M K C).Orc) (a : A)
    (i : Fin (rows a)) (j : Fin (len a)) :
    (unjoin (rows := rows) (len := len) o a i j).toE =
      nat (fun r' =>
          nat ((eJoin E b L M code mrow role q hlen K C).vecE o (src L M len a i.val j.val).1 r')
            (src L M len a i.val j.val).2.2)
        (src L M len a i.val j.val).2.1 := by
  unfold unjoin uncat
  rw [nat_lt' _ (idx_lt h a i j)]
  exact Flat.read (fun _ => code) (fun _ => mrow) (fun _ => role) (fun _ => q) (fun _ => hlen) o
    () 0 ⟨_, idx_lt h a i j⟩

/-- What the encoding data say of the one vector. -/
theorem eJoin_code : (eJoin E b L M code mrow role q hlen K C).code () = code := rfl
theorem eJoin_rows : (eJoin E b L M code mrow role q hlen K C).rows () = Flat.nRows 1 L.tot M := rfl
theorem eJoin_mrow : (eJoin E b L M code mrow role q hlen K C).mrow () = mrow := rfl
theorem eJoin_role : (eJoin E b L M code mrow role q hlen K C).role () = role := rfl
theorem eJoin_q : (eJoin E b L M code mrow role q hlen K C).q () = q := rfl

end Enc

end Blocks.Join

