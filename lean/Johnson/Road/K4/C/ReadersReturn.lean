-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ReadersReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4): the verifier's readers of the reads
(OnBytes/Model/LayerForms.lean) RETURN where the entries that they name lie in their family of
tables. The library's statements on these readers begin «if it returns», or compare the return at
two structures of one skeleton (Johnson/Road/K4/Total/SkelReaders.lean). Three definitions of
hypotheses; statements and proofs. General in the sizes.

  `Reach v t n`      the first n entries of the family that begins at t are there.
  `reach_of_tab`     from the list of tables: the family is found and has n entries; the array has
                     a column; the last row fits 32 bits.
  `limbs_some`, `shortA_some`, `longA_some`, `xbA_some`   a tensor's entry, a block, a stream's
                     block.
  `Long v X i n`     tensor X is found with its long tables, and blocks 0 to n - 1 of layer i are
                     there. `Short v X P i n`: the like for entries at a token point.
  `SA_some`, `SBA_some`, `shA_some`, `shSum_some`, `site_some`   the readers.

Not shown here. That the hypotheses hold at any plan: that a family of tables is found, is long
enough, and that the reads' array has a column: no example is shown here. Public data alone:
whether a form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.Total.IsSomeKit
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Ten TableAt sumForms)
open OnBytes.Model.Layer.Env (site)
open OnBytes.Desc.First.K4.Total (sumForms_all)

variable {v : Env}

/-- What is there has a value. -/
theorem some_of {α : Type} {x : Option α} (h : x.isSome = true) : ∃ a, x = some a :=
  Option.isSome_iff_exists.mp h

/-- **The first n entries of the family that begins at t are there.** This defines a hypothesis; the
definition claims nothing. -/
def Reach (v : Env) (t n : ℕ) : Prop := ∀ i, i < n → (v.U3at t i).isSome = true

/-- Fewer entries are there too. -/
theorem Reach.mono {t n m : ℕ} (R : Reach v t n) (h : m ≤ n) : Reach v t m :=
  fun i hi => R i (Nat.lt_of_lt_of_le hi h)

/-- **From the list of tables.** -/
theorem reach_of_tab {t n : ℕ} {x : TableAt} (hf : (v.tab.find? fun x => x.first == t) = some x)
    (hn : n ≤ x.len) (hK : v.K3 ≠ 0) (hb : (t + x.len) / v.K3 < 2 ^ 32) : Reach v t n := by
  intro i hi
  have h1 : i < x.len := Nat.lt_of_lt_of_le hi hn
  have h2 : (t + i) / v.K3 < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hb
  unfold Env.U3at
  rw [hf]
  have hc : (decide (i < x.len) && v.K3 != 0 && decide ((t + i) / v.K3 < 2 ^ 32)) = true := by
    rw [decide_eq_true h1, decide_eq_true h2, bne_iff_ne.mpr hK]
    rfl
  show (if (decide (i < x.len) && v.K3 != 0 && decide ((t + i) / v.K3 < 2 ^ 32)) = true then
    some (Aff.ent v.iU3 ((t + i) / v.K3) ((t + i) % v.K3)) else none).isSome = true
  rw [if_pos hc]
  rfl

/-- The sum over the limbs. -/
theorem limbs_some {t n nl : ℕ} {cell : ℕ → ℕ} (R : Reach v t n) (h : ∀ l, l < nl → cell l < n) :
    (v.limbs t nl cell).isSome = true := by
  unfold Env.limbs
  rw [sumForms_all, List.all_eq_true]
  intro l hl
  rw [Option.isSome_map]
  exact R _ (h l (List.mem_range.mp hl))

/-- An entry of a tensor, from a short table. -/
theorem shortA_some {t n : ℕ} {X : Ten} {i j : ℕ} (R : Reach v t n)
    (h : ∀ l, l < X.nl → tenCell X.place l i j < n) : (v.shortA t X i j).isSome = true :=
  limbs_some R h

/-- A block of a tensor, from a long table. -/
theorem longA_some {t n : ℕ} {X : Ten} {i jh : ℕ} (R : Reach v t n)
    (h : ∀ l, l < X.nl → tenCell X.place l i 0 / v.y.S2 + jh < n) :
    (v.longA t X i jh).isSome = true :=
  limbs_some R h

/-- A block of a residual stream. -/
theorem xbA_some {t n kh : ℕ} (R : Reach v t n)
    (h : ∀ l, l < v.y.xb.nl → tenCell v.y.xb l 0 0 / v.y.S2 + kh < n) :
    (v.xbA t kh).isSome = true :=
  limbs_some R h

/-- **Tensor X is found with its long tables, and blocks 0 to n - 1 of layer i are there.** This
defines a hypothesis; the definition claims nothing. -/
def Long (v : Env) (X : String) (i n : ℕ) : Prop :=
  ∃ t tb, v.tensorAt X "Z" = some (t, tb) ∧ ∀ jh, jh < n → (v.longA tb t i jh).isSome = true

/-- **Tensor X is found with its tables at the token point P, and entries 0 to n - 1 of layer i are
there.** This defines a hypothesis; the definition claims nothing. -/
def Short (v : Env) (X P : String) (i n : ℕ) : Prop :=
  ∃ t tb, v.tensorAt X P = some (t, tb) ∧ ∀ j, j < n → (v.shortA tb t i j).isSome = true

/-- The sum over the blocks of a layer. -/
theorem SA_some {wh : Array E} {X : String} {i n : ℕ} (L : Long v X i n) (hn : wh.size ≤ n) :
    (v.SA wh X i "Z").isSome = true := by
  obtain ⟨t, tb, e, H⟩ := L
  unfold Env.SA
  rw [e]
  show (sumForms wh.size fun xh => (v.longA tb t i xh).map fun a => (a, wh.getD xh zeroE)).isSome =
    true
  rw [sumForms_all, List.all_eq_true]
  intro xh hx
  rw [Option.isSome_map]
  exact H xh (Nat.lt_of_lt_of_le (List.mem_range.mp hx) hn)

/-- The sum over the blocks of a part of a segment. -/
theorem SBA_some {wh : Array E} {a b x0 : ℕ} {X : String} {i n : ℕ} (L : Long v X i n)
    (hx : x0 / v.y.S2 ≤ a / v.y.S2) (hn : b / v.y.S2 - x0 / v.y.S2 ≤ n) :
    (v.SBA wh a b X i "Z" x0).isSome = true := by
  obtain ⟨t, tb, e, H⟩ := L
  unfold Env.SBA
  rw [e]
  show (sumForms (b / v.y.S2 - a / v.y.S2) fun k =>
    (v.longA tb t i (a / v.y.S2 + k - x0 / v.y.S2)).map fun f =>
      (f, wh.getD (a / v.y.S2 + k) zeroE)).isSome = true
  rw [sumForms_all, List.all_eq_true]
  intro k hk
  rw [Option.isSome_map]
  have hk' := List.mem_range.mp hk
  exact H _ (by omega)

/-- An entry at a token point. -/
theorem shA_some {X P : String} {i j n : ℕ} (S : Short v X P i n) (hj : j < n) :
    (v.shA X P i j).isSome = true := by
  obtain ⟨t, tb, e, H⟩ := S
  unfold Env.shA Env.shIn
  rw [e]
  exact H j hj

/-- The sum over the entries of a layer at a token point. -/
theorem shSum_some {ew : Array E} {X P : String} {i m n : ℕ} (S : Short v X P i n) (hm : m ≤ n) :
    (v.shSum ew m X P i).isSome = true := by
  obtain ⟨t, tb, e, H⟩ := S
  unfold Env.shSum
  dsimp only
  rw [e, sumForms_all, List.all_eq_true]
  intro x hx
  rw [Option.isSome_map]
  exact H x (Nat.lt_of_lt_of_le (List.mem_range.mp hx) hm)

/-- The low key of a rounding site is there where its high digits are. -/
theorem site_some (w : E) (SQ : Aff) (k form : ℕ) {Srh : Unit → Option Aff}
    (h : (Srh ()).isSome = true) : (site w SQ k form Srh).isSome = true := by
  obtain ⟨a, ha⟩ := some_of h
  unfold Env.site
  dsimp only
  split_ifs
  · rfl
  · rw [ha]
    rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.some_of
#print axioms OnBytes.Road.K4.C.Reach.mono
#print axioms OnBytes.Road.K4.C.reach_of_tab
#print axioms OnBytes.Road.K4.C.limbs_some
#print axioms OnBytes.Road.K4.C.shortA_some
#print axioms OnBytes.Road.K4.C.longA_some
#print axioms OnBytes.Road.K4.C.xbA_some
#print axioms OnBytes.Road.K4.C.SA_some
#print axioms OnBytes.Road.K4.C.SBA_some
#print axioms OnBytes.Road.K4.C.shA_some
#print axioms OnBytes.Road.K4.C.shSum_some
#print axioms OnBytes.Road.K4.C.site_some
