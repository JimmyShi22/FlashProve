-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/RowWorth.lean: WHAT THE PIECES OF WHICH A CODE SWITCH's ROWS ARE MADE
ARE WORTH ON THE HONEST NEW MESSAGES. A row's worth hangs on its coefficients alone and is additive
in them (`worthOf`); each row of a switch is a sum of three sorts of pieces. Statements and proofs.

  `worthOf`, `value_worth`, `worthOf_add`, `worthOf_congr`   a function of coefficients, its worth;
                    a row's worth is that of its coefficients
  `size_main`, `size_g`   the size of a main table, off the message's shape; of g's
  `worth_on_g`      a piece that stands on g alone
  `worth_lift`      a form on the old main row's message, carried to g: the form on the folded main
                    row
  `worth_stretch`   coefficients on a stretch of the rest: these coefficients on the rest's entries
  `Lists.sum_single`      a sum over a list without repeats in which one entry alone counts
(The third sort of piece, a form on a kept member's table: Inner/KeptWorth.lean.)

Limits. Nothing on which pieces a row has. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.Value
import Johnson.Desc.K2.Honest.Inner.Worth
import Johnson.Top.H0.K2Hands.Pays
import Johnson.Top.H.SwitchKeptRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE coefAt formAt stretchAt)
open OnBytes.Means (Words value onTable tableSize)
open Johnson.Prover.Send (Rows)
open Finset (range)

/-- The worth of a function of coefficients on words: on g's main table and on each copy's. -/
def worthOf (S : Statement) (w : Words GE) (g : Nat) (anew : Array Nat)
    (κ : Nat → Part → Nat → GE) : GE :=
  (∑ J ∈ range (tableSize S g .main), κ g .main J * w g .main J) +
    (anew.toList.map fun o => ∑ J ∈ range (tableSize S o .main), κ o .main J * w o .main J).sum

theorem worthOf_add (S : Statement) (w : Words GE) (g : Nat) (anew : Array Nat)
    (κ₁ κ₂ : Nat → Part → Nat → GE) :
    worthOf S w g anew (fun o p J => κ₁ o p J + κ₂ o p J) =
      worthOf S w g anew κ₁ + worthOf S w g anew κ₂ := by
  unfold worthOf
  simp only [add_mul, Finset.sum_add_distrib, List.sum_map_add]
  ring

theorem worthOf_congr (S : Statement) (w : Words GE) (g : Nat) (anew : Array Nat)
    (κ₁ κ₂ : Nat → Part → Nat → GE)
    (hg : ∀ J, J < tableSize S g .main → κ₁ g .main J = κ₂ g .main J)
    (ha : ∀ o ∈ anew.toList, ∀ J, J < tableSize S o .main → κ₁ o .main J = κ₂ o .main J) :
    worthOf S w g anew κ₁ = worthOf S w g anew κ₂ := by
  unfold worthOf
  congr 1
  · exact Finset.sum_congr rfl fun J hJ => by rw [hg J (Finset.mem_range.1 hJ)]
  · congr 1
    apply List.map_congr_left
    intro o ho
    exact Finset.sum_congr rfl fun J hJ => by rw [ha o ho J (Finset.mem_range.1 hJ)]

/-- The size of a main table, off the message's shape. -/
theorem size_main (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (hpos : 0 < x.shape.mainRows) :
    tableSize S o .main =
      2 ^ (ceilLog2 x.shape.mainRows + (S.codes.base.getD x.shape.code default).logEll) := by
  have hne : (x.shape.mainRows == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  unfold tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  simp only [hx, OracleShape.rows, hpos, decide_true, if_true, hne, Bool.false_eq_true, if_false]

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- A row's worth is that of its coefficients. -/
theorem value_worth (A : AtSwitch S old T g anew W V) (hn : ∀ o ∈ anew.toList, o < S.oracles.size)
    (r : OnBytes.Row) :
    value rdE S r (newWords (sizesAt S old T) g anew V) =
      worthOf S (newWords (sizesAt S old T) g anew V) g anew (coefAt r) :=
  value_split A hn r

/-- The size of g's main table. -/
theorem size_g (A : AtSwitch S old T g anew W V) :
    tableSize S g .main =
      2 ^ (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll) := by
  obtain ⟨x, hx, hs⟩ := Option.map_eq_some_iff.1 A.seated.carrying
  rw [size_main S g x hx (by rw [hs]; exact A.target.rows), hs]
  rfl

/-- A piece that stands on g alone is worth its sum over g's main table. -/
theorem worth_on_g (A : AtSwitch S old T g anew W V) (f : Nat → GE) (p : Part) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew
        (fun o q J => if g == o && p == q then f J else 0) =
      if p = .main then
        ∑ J ∈ range (tableSize S g .main),
          f J * newWords (sizesAt S old T) g anew V g .main J
      else 0 := by
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons] at hap
  unfold worthOf
  have hz : (anew.toList.map fun o => ∑ J ∈ range (tableSize S o .main),
      (if g == o && p == Part.main then f J else 0) *
        newWords (sizesAt S old T) g anew V o .main J).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    have hne : (g == o) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun e => hap.1 (List.mem_append_left _ (e ▸ ho))
    simp [hne]
  rw [hz, add_zero]
  cases p <;> simp

/-- **Coefficients on a stretch of the rest.** -/
theorem worth_stretch (A : AtSwitch S old T g anew W V) (a n : Nat) (c : Nat → GE)
    (hfit : a + n ≤ (rest (sizesAt S old T) W).length) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew
        (fun o q J => if g == o && T.rest.part == q then
          stretchAt (SwitchPlaces.make S.codes T) a n c J else 0) =
      ∑ i ∈ range n, c i * (rest (sizesAt S old T) W).getD (a + i) zeroG := by
  obtain ⟨_, hrow, hplace, _⟩ := SwitchPlaces.places_of_check A.check
  obtain ⟨_, _, _, c4, _⟩ := Johnson.Top.H.check_facts A.check
  rw [worth_on_g A, if_pos A.restMain, stretch_worth]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [word_rest A (a + i) (by have := Finset.mem_range.1 hi; omega)]
  · intro i hi
    have hlt : a + i < (SwitchPlaces.make S.codes T).size :=
      Nat.lt_of_lt_of_le (by omega) (rest_fits A)
    have h1 := (hrow (a + i)).2
    have h2 := hplace (a + i) hlt
    rw [A.restMain] at h1 h2 c4
    rw [size_g A]
    exact VerifiableInference.Desc.First.K2Hands.lt_pow_of _ _ _ _ _
      (Nat.lt_of_lt_of_le h1 c4) (SwitchPlaces.le_two_pow_ceilLog2' _) h2
      (SwitchPlaces.le_two_pow_ceilLog2' _)

/-- **A form on the old main row's message, carried to g.** -/
theorem worth_lift (A : AtSwitch S old T g anew W V) (c : Form)
    (hc : ∀ v ∈ c.tensors, v.vars = (S.codes.base.getD old.code default).logEll) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew
        (fun o q J => if g == o && q == .main then
          formAt (switchLift c (S.codes.base.getD old.code default).logEll T.main
            (switchRowBits T .main)
            (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll)) J else 0) =
      ∑ j ∈ range (S.codes.base.getD old.code default).ell, formAt c j * W.main j := by
  have F := A.target
  obtain ⟨_, _, hM⟩ := SwitchPlaces.of_check A.check
  rw [F.mainPart] at hM
  obtain ⟨_, _, c3, _⟩ := Johnson.Top.H.check_facts A.check
  obtain ⟨_, h0, _⟩ := VerifiableInference.Desc.First.K2Hands.check_more A.check
  have hpow : 2 ^ (S.codes.base.getD old.code default).logEll =
      (S.codes.base.getD old.code default).ell := F.power.2
  have hb : T.main.bits ≤ (S.codes.base.getD old.code default).logEll :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by rw [hpow]; exact F.mainSmall)
  have hR : T.main.bits ≤ switchRowBits T .main :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by unfold RowCut.Fits at hM; omega)
  have hn : (S.codes.base.getD old.code default).logEll ≤
      (S.codes.base.getD T.shape.code default).logEll + T.main.bits :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by
      rw [hpow, Nat.pow_add]
      exact Nat.le_trans F.mainRoom
        (Nat.mul_le_mul_right _ (SwitchPlaces.le_two_pow_ceilLog2' _)))
  have e : (fun (o : Nat) (q : Part) (J : Nat) => if g == o && q == .main then
      formAt (switchLift c (S.codes.base.getD old.code default).logEll T.main
        (switchRowBits T .main)
        (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll)) J else 0) =
      fun o q J => if g == o && Part.main == q then
      formAt (switchLift c (S.codes.base.getD old.code default).logEll T.main
        (switchRowBits T .main)
        (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll)) J else 0 := by
    funext o q J
    cases q <;> rfl
  rw [e, worth_on_g A, if_pos rfl, size_g A,
    lift_worth c _ T.main _ _ hc hb hR (by omega) (by rw [h0]; exact Nat.dvd_zero _)
      (by rw [h0, Nat.zero_div]; exact Nat.two_pow_pos _), hpow]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [word_main A j (Finset.mem_range.1 hj)]
  · intro j hj
    rw [hpow] at hj
    have hlt : j % 2 ^ T.main.bits < 2 ^ T.main.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
    exact VerifiableInference.Desc.First.K2Hands.lt_pow_of _ _ T.shape.mainRows
      (S.codes.base.getD T.shape.code default).ell _
      (by rw [cutIndex_mod hM j]; omega) (SwitchPlaces.le_two_pow_ceilLog2' _)
      (by
        rw [cutIndex_div hM j]
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact Nat.lt_of_lt_of_le hj F.mainRoom))
      (SwitchPlaces.le_two_pow_ceilLog2' _)

/-- A sum over a list without repeats in which one entry alone counts. -/
theorem Lists.sum_single (F : Nat → GE) : ∀ (l : List Nat) (x : Nat), l.Nodup → x ∈ l →
    (∀ y ∈ l, y ≠ x → F y = 0) → (l.map F).sum = F x
  | [], _, _, h, _ => by simp at h
  | z :: l, x, hn, hx, h0 => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons]
    by_cases e : z = x
    · subst e
      have : (l.map F).sum = 0 := by
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
        exact h0 y (List.mem_cons_of_mem _ hy) (fun e => hn.1 (e ▸ hy))
      rw [this, add_zero]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm e
        · exact h
      rw [h0 z (List.mem_cons_self ..) e, zero_add]
      exact Lists.sum_single F l x hn.2 hx' fun y hy => h0 y (List.mem_cons_of_mem _ hy)

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.worth_stretch
#print axioms VerifiableInference.Desc.K2.Honest.worth_lift
