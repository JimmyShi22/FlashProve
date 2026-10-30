-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFitted.lean: the committer that runs reads its random values through `fitted`
alone, and `fitted` changes nothing at random values that have the shape's form.

The committer (Johnson/Bind/Twin.lean) takes its random values by address, in a type that depends on
no shape (`Coins`): words and byte strings of any kind. `fitted S c` are these values as the
committer reads them at the shape S: each word as its residue modulo p, each salt cut or filled to
sigma bytes. Main definition: `Coins.Fits S c`: every word of c is below p and every salt has sigma
bytes. Main theorems.
   `commitW_fitted`: over every monad and every hash, at every shape, all files and all plain
      entries: the committer at `fitted S c` is the committer at c.
   `fits_fitted`: `fitted S c` has the shape's form.
   `fitted_of_fits`: if c has the shape's form, `fitted S c` is c. So `fitted S` reaches every c of
      that form.
No Mathlib.
Limits.
(1) The form is asked at every address, also at rows, places and leaves that the shape does not
    have. That the committer reads no such address is not stated here.
(2) Nothing on how random values are drawn, on a binding of the commitment or on index privacy.

-/
import Johnson.Bind.Twin
import Fmt.FieldEFast
import Fmt.Rules23Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open Fmt (Ext Fld)

/-! ### Words -/

theorem toNat_residue (w : UInt64) : (residue w).toNat = w.toNat % Fmt.Fld.two.p :=
  Fmt.Fld.toNat_red _ _

theorem residue_residue (w : UInt64) : residue (residue w) = residue w := by
  unfold residue
  refine Fmt.Fld.red_congr _ ?_
  rw [Fmt.Fld.toNat_red, Nat.mod_mod]

theorem residue_zero : residue 0 = 0 := by first | rfl | decide

theorem residue_of_ok (w : UInt64) (h : Fmt.Fld.two.ok w = true) : residue w = w := by
  have hlt : w.toNat < Fmt.Fld.two.p := of_decide_eq_true h
  apply UInt64.toNat_inj.1
  rw [toNat_residue, Nat.mod_eq_of_lt hlt]

theorem ok_residue (w : UInt64) : Fmt.Fld.two.ok (residue w) = true := Fmt.Fld.ok_red _ _

theorem add_residue_left (a b : UInt64) : Fmt.Fld.two.add (residue a) b = Fmt.Fld.two.add a b := by
  unfold Fmt.Fld.add
  refine Fmt.Fld.red_congr _ ?_
  rw [toNat_residue, Nat.mod_add_mod]

theorem mul_residue_right (a b : UInt64) : Fmt.Fld.two.mul a (residue b) = Fmt.Fld.two.mul a b := by
  unfold Fmt.Fld.mul
  refine Fmt.Fld.red_congr _ ?_
  rw [toNat_residue, Nat.mul_mod_mod]

theorem mulE_residue_right (a : Ext) (x y z : UInt64) :
    Fmt.Fld.two.mulE a (residue x, residue y, residue z) = Fmt.Fld.two.mulE a (x, y, z) := by
  simp only [Fmt.Fld.mulE, mul_residue_right]

/-! ### Symbols -/

theorem hornerF_map_residue (z : UInt64) :
    ∀ cs : List UInt64, Fmt.M1.hornerF z (cs.map residue) = Fmt.M1.hornerF z cs
  | [] => rfl
  | c :: cs => by
    have ih := hornerF_map_residue z cs
    unfold Fmt.M1.hornerF at ih ⊢
    simp only [List.map_cons, List.foldr_cons, ih, add_residue_left]

theorem map_residue_fitL (n : Nat) (l : List UInt64) :
    (Fmt.M1.fitL 0 n l).map residue = Fmt.M1.fitL 0 n (l.map residue) := by
  simp only [Fmt.M1.fitL, List.map_append, List.map_take, List.map_replicate, residue_zero,
    List.length_map]

/-- A symbol depends on the message's and the tail's words through their residues alone. -/
theorem symF_congr (C : Fmt.M1.Code) (x : Nat) (m m' rho rho' : List UInt64)
    (hm : m.map residue = m'.map residue) (hr : rho.map residue = rho'.map residue) :
    Fmt.M1.symF C x m rho = Fmt.M1.symF C x m' rho' := by
  have key : ∀ m rho : List UInt64,
      Fmt.M1.hornerF (Fmt.M1.point C.a x) (Fmt.M1.fitL 0 C.r rho ++ Fmt.M1.fitL 0 C.l m) =
        Fmt.M1.hornerF (Fmt.M1.point C.a x)
          (Fmt.M1.fitL 0 C.r (rho.map residue) ++ Fmt.M1.fitL 0 C.l (m.map residue)) := by
    intro m rho
    rw [← hornerF_map_residue, List.map_append, map_residue_fitL, map_residue_fitL]
  unfold Fmt.M1.symF
  rw [key m rho, key m' rho', hm, hr]

theorem map_residue_range (f : Nat → UInt64) (n : Nat) :
    ((List.range n).map fun j => residue (f j)).map residue = ((List.range n).map f).map residue :=
    by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact residue_residue (f j)

theorem message_fitted (S : Shape) (entry : Nat → Nat → UInt64) (c : Coins) (b : Nat) :
    (message S (Table.of entry (fitted S c)) b).map residue =
      (message S (Table.of entry c) b).map residue := by
  show ((List.range S.plain).map (entry b) ++
      (List.range S.pads).map fun j => residue (c.pad b j)).map residue =
    ((List.range S.plain).map (entry b) ++ (List.range S.pads).map (c.pad b)).map residue
  rw [List.map_append, List.map_append, map_residue_range]

theorem tailOf_fitted (S : Shape) (entry : Nat → Nat → UInt64) (c : Coins) (b : Nat) :
    (tailOf S (Table.of entry (fitted S c)) b).map residue =
      (tailOf S (Table.of entry c) b).map residue :=
  map_residue_range (c.tail b) S.r

theorem columnOf_fitted (S : Shape) (entry : Nat → Nat → UInt64) (c : Coins) :
    columnOf S (laid S (Table.of entry (fitted S c))) = columnOf S (laid S (Table.of entry c)) := by
  funext x
  unfold columnOf laid
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  exact symF_congr _ _ _ _ _ _ (message_fitted S entry c b) (tailOf_fitted S entry c b)

/-! ### Answers -/

theorem answers_fitted (S : Shape) (entry : Nat → Nat → UInt64) (c : Coins) :
    answers S (Table.of entry (fitted S c)) = answers S (Table.of entry c) := by
  funext seeds
  unfold answers answerAt
  simp only [Table.of, fitted, mulE_residue_right]

/-! ### Salts -/

theorem size_fit (n : Nat) (b : ByteArray) : (Fmt.fit n b).size = n := by
  unfold Fmt.fit
  split
  · rw [ByteArray.size_extract]
    omega
  · rw [ByteArray.size_append, Fmt.size_zeros]
    omega

theorem fit_fit (n : Nat) (b : ByteArray) : Fmt.fit n (Fmt.fit n b) = Fmt.fit n b :=
  Fmt.fit_self n _ (size_fit n b)

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

theorem leavesFromW_fit (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    ∀ (n x : Nat) (acc : Array ByteArray),
      leavesFromW h S start col (fun y => Fmt.fit S.sigma (salt y)) n x acc =
        leavesFromW h S start col salt n x acc
  | 0, _, _ => rfl
  | n + 1, x, acc => by
    simp only [leavesFromW, leafAtW, fit_fit, leavesFromW_fit S start col salt n]

/-- **The committer reads its random values through `fitted` alone.** -/
theorem commitW_fitted (S : Shape) (files : List ByteArray) (entry : Nat → Nat → UInt64)
    (c : Coins) :
    commitW h S files (Table.of entry (fitted S c)) = commitW h S files (Table.of entry c) := by
  unfold commitW plainW coreW rootW
  simp only [columnOf_fitted, answers_fitted]
  simp only [Table.of, fitted, leavesFromW_fit]

end

/-! ### The form -/

/-- The random values have the form of the shape S: every word is below p, every salt has sigma
bytes. -/
def Coins.Fits (S : Shape) (c : Coins) : Prop :=
  (∀ b j, Fmt.Fld.two.ok (c.tail b j) = true) ∧ (∀ b j, Fmt.Fld.two.ok (c.pad b j) = true) ∧
    ∀ x, (c.salt x).size = S.sigma

theorem fits_fitted (S : Shape) (c : Coins) : (fitted S c).Fits S :=
  ⟨fun _ _ => ok_residue _, fun _ _ => ok_residue _, fun _ => size_fit _ _⟩

/-- **`fitted` changes nothing at random values of the shape's form.** -/
theorem fitted_of_fits (S : Shape) (c : Coins) (hc : c.Fits S) : fitted S c = c := by
  obtain ⟨tail, pad, salt⟩ := c
  obtain ⟨h1, h2, h3⟩ := hc
  unfold fitted
  congr 1
  · funext b j
    exact residue_of_ok _ (h1 b j)
  · funext b j
    exact residue_of_ok _ (h2 b j)
  · funext x
    exact Fmt.fit_self _ _ (h3 x)

end Bind.Twin

#print axioms Bind.Twin.residue_residue
#print axioms Bind.Twin.residue_of_ok
#print axioms Bind.Twin.symF_congr
#print axioms Bind.Twin.residue_zero
#print axioms Bind.Twin.ok_residue
#print axioms Bind.Twin.toNat_residue
#print axioms Bind.Twin.add_residue_left
#print axioms Bind.Twin.mul_residue_right
#print axioms Bind.Twin.mulE_residue_right
#print axioms Bind.Twin.hornerF_map_residue
#print axioms Bind.Twin.map_residue_fitL
#print axioms Bind.Twin.map_residue_range
#print axioms Bind.Twin.message_fitted
#print axioms Bind.Twin.tailOf_fitted
#print axioms Bind.Twin.size_fit
#print axioms Bind.Twin.columnOf_fitted
#print axioms Bind.Twin.answers_fitted
#print axioms Bind.Twin.fit_fit
#print axioms Bind.Twin.leavesFromW_fit
#print axioms Bind.Twin.commitW_fitted
#print axioms Bind.Twin.fits_fitted
#print axioms Bind.Twin.fitted_of_fits
