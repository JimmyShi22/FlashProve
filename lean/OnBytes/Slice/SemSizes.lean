-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SemSizes.lean: the row of a code switch that the format's decision folds has a mask
vector of the full length.

A fold cuts the public weights of its hiding polynomial at the length of the folded mask row
(OnBytes/Slice/FoldPeel.lean: `maskLen`). That length depends on the length of the row's vector on
the mask table. This file shows that it is the length of one mask row of the stage, for the row
that a code switch gives.


Main theorems.
 `maskLen_eq`       the length, if the vector on the mask table has as many entries as the table
 `size_csStep_d`    the row of a code switch has such a vector

 `maskLen_csStep`   the two put together

Not claimed. Nothing is said of the vectors' entries. Nothing on the row of a link's batching.
-/
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.SimCs
import OnBytes.Slice.BatSem
import Fmt.M3Dec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The folded mask row has the length of one mask row, if the vector on the mask table has as many
entries as the table. -/
theorem maskLen_eq (s : Sg) (G : Fmt.M1.GRow) (h : G.d.size = 2 ^ s.h * s.Z.l) :
    maskLen s G = s.Z.l := by
  unfold maskLen
  rw [size_foldStep_d0_eq, h, Nat.min_eq_left (Nat.le_add_right s.h s.g)]
  have hp : 0 < 2 ^ s.h := Nat.two_pow_pos s.h
  rw [Nat.add_sub_assoc hp, Nat.mul_add_div hp, Nat.div_eq_of_lt (Nat.sub_lt hp Nat.one_pos),
    Nat.add_zero]

/-- The largest of the lengths of vectors that all have the length n. -/
private theorem foldl_max_const (n : ℕ) : ∀ (rows : List Fmt.M1.GRow) (m : ℕ), m ≤ n →
    (∀ R ∈ rows, R.d.size = n) → rows ≠ [] → rows.foldl (fun k R => max k R.d.size) m = n
  | [], _, _, _, h => absurd rfl h
  | [R], m, hm, hr, _ => by
    show max m R.d.size = n
    rw [hr R List.mem_cons_self]
    exact Nat.max_eq_right hm
  | R :: R' :: rows, m, hm, hr, _ => by
    show (R' :: rows).foldl (fun k R => max k R.d.size) (max m R.d.size) = n
    refine foldl_max_const n (R' :: rows) _ ?_ (fun Q hQ => hr Q (List.mem_cons_of_mem _ hQ))
      (List.cons_ne_nil _ _)
    rw [hr R List.mem_cons_self]
    exact Nat.le_of_eq (Nat.max_eq_right hm)

/-- Each of a draw's three rows has a vector of nD entries on the mask table. -/
private theorem size_drawRows_d (f : Fmt.Fld) (old : Fmt.M1.Stage) (nM nD : ℕ) (s : Fmt.M1.SRow)
    (x : ℕ) (cl : Fmt.M1.Col) : ∀ R ∈ Fmt.M1.drawRows f old nM nD s x cl, R.d.size = nD := by
  intro R hR
  unfold Fmt.M1.drawRows at hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact size_layAt _ _ _
  · show (Fmt.M1.addV f _ _).size = nD
    rw [size_addV, size_layAt, size_layAt, Nat.max_self]
  · show (Fmt.M1.addV f _ _).size = nD
    rw [size_addV, size_layAt, size_layAt, Nat.max_self]

/-- So has each row of all draws. -/
private theorem size_rowsOf_d (f : Fmt.Fld) (old : Fmt.M1.Stage) (nM nD : ℕ) (s : Fmt.M1.SRow)
    (col : ℕ → Option Fmt.M1.Col) : ∀ (xs : List ℕ) (rs : List Fmt.M1.GRow),
    Fmt.M1.CsEq.rowsOf f old nM nD s col xs = some rs → ∀ R ∈ rs, R.d.size = nD
  | [], rs, h => by
    have e : rs = [] := (Option.some.inj h).symm
    rw [e]
    intro R hR
    cases hR
  | x :: xs, rs, h => by
    have h' : (match Fmt.M1.CsEq.rowsOf f old nM nD s col xs, col x with
      | some rs', some cl => some (Fmt.M1.drawRows f old nM nD s x cl ++ rs')
      | _, _ => none) = some rs := h
    split at h'
    · next rs' cl h1 _ =>
      have e : Fmt.M1.drawRows f old nM nD s x cl ++ rs' = rs := Option.some.inj h'
      rw [← e]
      intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · exact size_drawRows_d f old nM nD s x cl R hR
      · exact size_rowsOf_d f old nM nD s col xs rs' h1 R hR
    · cases h'

/-- The row that a code switch gives has one entry for each entry of the new mask table. -/
theorem size_csStep_d (f : Fmt.Fld) (old new : Fmt.M1.Stage) (s : Fmt.M1.SRow)
    (sample : Fmt.M1.GRow) (xs : List ℕ) (theta : Fmt.M1.E) (col : ℕ → Option Fmt.M1.Col)
    (G : Fmt.M1.GRow) (h : Fmt.M1.csStep f old new s sample xs theta col = some G) :
    G.d.size = 2 ^ new.h * new.Z.l := by
  rw [Fmt.M1.CsEq.csStep_eq] at h
  unfold Fmt.M1.csStepLit at h
  rw [Fmt.M1.CsEq.csRows_eq] at h
  cases hr : Fmt.M1.CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col xs with
  | none =>
    rw [hr] at h
    cases h
  | some rs =>
    rw [hr] at h
    have e : Fmt.M1.sumRows f theta
        (Fmt.M1.CsEq.carriedR f old new s :: Fmt.M1.CsEq.smpR new sample :: rs) = G :=
      Option.some.inj h
    rw [← e, size_sumRows_d]
    refine foldl_max_const _ _ 0 (Nat.zero_le _) (fun R hR => ?_) (List.cons_ne_nil _ _)
    rcases List.mem_cons.1 hR with rfl | hR
    · show (Fmt.M1.addV f _ _).size = _
      rw [size_addV, size_layAt, size_layAt, Nat.max_self]
    · rcases List.mem_cons.1 hR with rfl | hR
      · exact size_layAt _ _ _
      · exact size_rowsOf_d f old _ _ s col xs rs hr R hR

/-- The fold of the row that a code switch gives cuts the hiding weights at the length of one mask
row of the new stage. -/
theorem maskLen_csStep (s' : Sg) (f : Fmt.Fld) (old : Fmt.M1.Stage) (s : Fmt.M1.SRow)
    (sample : Fmt.M1.GRow) (xs : List ℕ) (theta : Fmt.M1.E) (col : ℕ → Option Fmt.M1.Col)
    (G : Fmt.M1.GRow) (h : Fmt.M1.csStep f old s'.st s sample xs theta col = some G) :
    maskLen s' G = s'.Z.l :=
  maskLen_eq s' G (size_csStep_d f old s'.st s sample xs theta col G h)

end OnBytes.Slice

#print axioms OnBytes.Slice.maskLen_eq
#print axioms OnBytes.Slice.size_csStep_d
#print axioms OnBytes.Slice.maskLen_csStep
