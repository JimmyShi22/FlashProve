-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwTeeth.lean.
The small lookup's two relations written out, one family of entries at which the in-relation holds
and one at which it fails, and the keys' row entry by entry.

Definitions, examples by rfl, statements and proofs.
Main names:
  `o65RA`: every key that is not padding is a row of the table. `o65RB` (at a read-out x: the forms
    of `o65Out x`), `o65RBb` (at an out-statement b, a list of rows): the forms meet their targets.
    No verifier is named here. `RA_iff`, `RB_iff`, `RBb_iff`: they are `o65A.lk.inR` and
    `o65A.lk.out id id`.
  `RA_closed`: at every m whose keys are `OnBytes.Lkp.o65Keys` the in-relation holds
    (`closed_exists`: there is such an m). `RA_false_a`: at every m with key 2 equal to 5 it is
    false.
  `eqN_rev`: the weight in `keyRow`, where the claim's point is a point p read backwards, is the
    product over the bits of the key's number, low bit first, in the coordinates of p.
  `keyRow_cf_key`, `keyRow_cf_other`, `keyRow_tg`: the coefficients of `keyRow` at the small lookup,
    entry by entry, for any claim c: key entry b: `Blocks.eqN 4 0 c.pt b` + mf; a plane's or a
    mask's entry: mf alone; target: tg − eqN .. 15 · 1.
  `clK_pt`, `keyRow_cf_chain`, `keyRow_tg_chain`: the same at the chain's own claim `o65A.clK x`,
    whose point is the tree's point read backwards (rfl).
  `sigma_ext`: where the claim's point is a Boolean point β read backwards, the extension reads
    entry Σ β_c 2^c. `sigma_keyRow`: there, with no mask form, `keyRow` holds at m exactly if what
    stands at key number Σ β_c 2^c (an entry, or the public constant) is the target. Both are
    general in k.
Limits: all but the general lemmas at one value. The examples by rfl say that the relations are
those of `o65A` (its key, tab; `o65Out`). The keys of `OnBytes.Lkp.o65Keys` are typed nowhere here.

-/
import OnBytes.Tie.Pv.Lookup.Value.TwSet
import Cb.Ld.LdLkpNumProofs

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Finset
open TwNums (Sizes o65S)

/-! ### The in-relation: where it holds, where it fails -/

/-- the in-relation, written out -/
def o65RA (m : o65J → K) : Prop := ∀ b : Fin 15, ∃ u < 2, m (.inl b) = ((u : ℕ) : K)
/-- the out-relation at a read-out x, written out: the forms of `o65Out x` meet their targets -/
def o65RB (x : TX Unit K o65J) (m : o65J → K) : Prop := ∀ r ∈ o65Out x, r.Holds m
/-- The out-relation as a relation on the out-statement b (a list of rows: coefficients and targets:
public data alone) and the entries. `RBof` (OnBytes/Tie/Pv/Lookup/Know/TwOne.lean), which stands in
`o65_know`, is this at every E, J. -/
def o65RBb (b : List (Row K o65J)) (m : o65J → K) : Prop := ∀ r ∈ b, r.Holds m

-- the relations are those of o65A
example : o65A.lk.inR = fun st m => InTable (3 + 1) 1 (o65A.key st m) (o65A.tab st) ∧ True := rfl
example : o65A.lk.key = o65A.key ∧ o65A.lk.tab = o65A.tab := ⟨rfl, rfl⟩
example (m : o65J → K) : o65A.key () m = fun b => Sum.elim m id (kAt K o65S b) := rfl
example : o65A.tab () = fun u : ℕ => (u : K) := rfl
example (x : TX Unit K o65J) : o65Out x = x.2.2 ++ [(keyRow (3 + 1) (kAt K o65S) x.2.1 : Row K
    o65J)] := rfl
theorem RA_iff (m : o65J → K) : o65A.lk.inR () m ↔ o65RA m := o65_RA_iff m
theorem RB_iff (x : TX Unit K o65J) (m : o65J → K) : o65A.lk.out id id x m ↔ o65RB x m :=
    o65_out_iff x m
example (b : List (Row K o65J)) (m : o65J → K) : o65RBb b m = RowsHold b m := rfl
example (x : TX Unit K o65J) (m : o65J → K) : o65RB x m = o65RBb (o65Out x) m := rfl
/-- The output claim at the read-out x is the out-relation at the out-statement `o65Out x`, and
nothing else. -/
theorem RBb_iff (x : TX Unit K o65J) (m : o65J → K) : o65A.lk.out id id x m ↔ o65RBb (o65Out x) m :=
    o65_out_iff x m

/-- the keys of m are `OnBytes.Lkp.o65Keys` -/
def ClosedKeys (m : o65J → K) : Prop := ∀ b : Fin 15, m (.inl b) = ((OnBytes.Lkp.o65Keys.getD b.1 0
    : ℕ) : K)

theorem RA_closed (m : o65J → K) (h : ClosedKeys m) : o65RA m := fun b =>
  ⟨OnBytes.Lkp.o65Keys.getD b.1 0, by fin_cases b <;> decide, h b⟩
/-- there is such an m -/
theorem closed_exists : ∃ m : o65J → K, ClosedKeys m :=
  ⟨fun j => Sum.elim (fun b : Fin 15 => ((OnBytes.Lkp.o65Keys.getD b.1 0 : ℕ) : K)) (fun _ => 0) j,
      fun _ => rfl⟩

theorem five_ne_zero : (5 : K) ≠ ((0 : ℕ) : K) := by decide +kernel
theorem five_ne_one : (5 : K) ≠ ((1 : ℕ) : K) := by decide +kernel

/-- key 2 equal to 5 is no row -/
theorem RA_false_a (m : o65J → K) (h : m (.inl 2) = 5) : ¬ o65RA m := by
  intro hR
  obtain ⟨u, hu, e⟩ := hR 2
  rw [h] at e
  interval_cases u
  · exact five_ne_zero e
  · exact five_ne_one e

/-! ### the weights of keyRow in the coordinates of the tree's point -/
section
variable {E : Type} [Field E]

/-- low bit first -/
def eqLow {k : ℕ} (p : Fin k → E) (X : ℕ) : E := ∏ i : Fin k, if X.testBit i then p i else 1 - p i

theorem eqN_rev (k : ℕ) (p : Fin k → E) (X : ℕ) :
    Blocks.eqN k 0 (Blocks.nat fun i : Fin k => p i.rev) X = eqLow p X := by
  rw [Blocks.eqN_nat]
  unfold Alg.eqN Alg.eqk Alg.bits eqLow
  refine Fintype.prod_equiv Fin.revPerm _ _ fun v => ?_
  have e : k - 1 - (v : ℕ) = ((Fin.revPerm v : Fin k) : ℕ) := by
    rw [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [e, Fin.revPerm_apply]

/-- the same in the words of `Alg.eqk` -/
theorem blocks_eqN_rev (k : ℕ) (z : Fin k → E) (b : Fin k → Bool) :
    Blocks.eqN k 0 (Blocks.nat fun i : Fin k => z i.rev) (numLE b) = Alg.eqk z b := by
  rw [Blocks.eqN_nat, ldLkpNum_rev k b, Alg.eqN_num]
  unfold Alg.eqk
  exact Fintype.prod_equiv Fin.revPerm _ _ fun v => by simp [Fin.revPerm_apply]

/-- On the reading of a masked claim's point: at the Boolean point β of the tree's point (the
claim's own point is that point read backwards) the extension reads entry Σ β_c 2^c. -/
theorem sigma_ext (k : ℕ) (a : ℕ → E) (β : Fin k → Bool) :
    Blocks.ext k a (Blocks.nat fun i : Fin k => (Alg.corner β : Fin k → E) i.rev) = a (∑ c : Fin k,
        if β c then 2 ^ (c : ℕ) else 0) := by
  rw [← ldLkpNum_ext E k a (Alg.corner β), Alg.mle_corner]
  rfl

/-- On the form: at a Boolean point β, with no mask form, keyRow says: what stands at key number
Σ β_c 2^c (an entry, or the public constant) is the target. -/
theorem sigma_keyRow {J : Type} [Fintype J] [DecidableEq J] (k : ℕ) (kAt : ℕ → J ⊕ E) (β : Fin k →
    Bool) (t : E) (m : J → E) :
    (keyRow k kAt ⟨Blocks.nat fun i : Fin k => (Alg.corner β : Fin k → E) i.rev, 0, t⟩).Holds m ↔
      Sum.elim m id (kAt (∑ c : Fin k, if β c then 2 ^ (c : ℕ) else 0)) = t := by
  rw [← keyRow_iff]
  unfold MCl.Holds
  rw [sigma_ext k (fun b => Sum.elim m id (kAt b)) β]
  simp

end

/-! ### keyRow entry by entry: general, then at the small lookup -/
section
variable {E J : Type} [Field E] [Fintype J] [DecidableEq J]

omit [Fintype J] in
theorem keyRow_cf_of (k : ℕ) (kAt : ℕ → J ⊕ E) (c : MCl E J) (j : J) (X0 : ℕ) (h0 : X0 < 2 ^ k)
    (h : ∀ X < 2 ^ k, kCf (kAt X) j = if X = X0 then 1 else 0) :
    (keyRow k kAt c).cf j = Blocks.eqN k 0 c.pt X0 + c.mf j := by
  unfold keyRow
  simp only
  congr 1
  rw [Finset.sum_eq_single X0]
  · rw [h X0 h0, if_pos rfl, mul_one]
  · intro X hX hne
    rw [h X (Finset.mem_range.mp hX), if_neg hne, mul_zero]
  · intro hn
    exact absurd (Finset.mem_range.mpr h0) hn

omit [Fintype J] in
theorem keyRow_cf_zero (k : ℕ) (kAt : ℕ → J ⊕ E) (c : MCl E J) (j : J) (h : ∀ X < 2 ^ k, kCf (kAt X)
    j = 0) :
    (keyRow k kAt c).cf j = c.mf j := by
  unfold keyRow
  simp only
  rw [Finset.sum_eq_zero, zero_add]
  intro X hX
  rw [h X (Finset.mem_range.mp hX), mul_zero]

omit [Fintype J] in
theorem keyRow_tg_of (k : ℕ) (kAt : ℕ → J ⊕ E) (c : MCl E J) (X0 : ℕ) (a : E) (h0 : X0 < 2 ^ k)
    (h : ∀ X < 2 ^ k, kCo (kAt X) = if X = X0 then a else 0) :
    (keyRow k kAt c).tg = c.tg - Blocks.eqN k 0 c.pt X0 * a := by
  unfold keyRow
  simp only
  congr 1
  rw [Finset.sum_eq_single X0]
  · rw [h X0 h0, if_pos rfl]
  · intro X hX hne
    rw [h X (Finset.mem_range.mp hX), if_neg hne, mul_zero]
  · intro hn
    exact absurd (Finset.mem_range.mpr h0) hn

end

theorem o65_kCf_key (X : ℕ) (hX : X < 16) (b : Fin 15) : kCf (kAt K o65S X) (.inl b : o65J) = if X =
    b.1 then 1 else 0 := by
  by_cases h : X < 15
  · have e := o65_kAt_lt ⟨X, h⟩
    simp only at e
    rw [e]
    show (if (Sum.inl ⟨X, h⟩ : o65J) = Sum.inl b then (1 : K) else 0) = _
    by_cases hb : X = b.1
    · subst hb; simp
    · rw [if_neg hb, if_neg]
      intro q
      exact hb (congrArg Fin.val (Sum.inl.inj q))
  · have e : X = 15 := by omega
    subst e
    rw [o65_kAt_pad]
    have : (15 : ℕ) ≠ b.1 := by have := b.2; omega
    rw [if_neg this]
    rfl
theorem o65_kCf_other (X : ℕ) (hX : X < 16) (j : Fin 16 ⊕ Fin 104) : kCf (kAt K o65S X) (.inr j :
    o65J) = 0 := by
  by_cases h : X < 15
  · have e := o65_kAt_lt ⟨X, h⟩
    simp only at e
    rw [e]
    show (if (Sum.inl ⟨X, h⟩ : o65J) = Sum.inr j then (1 : K) else 0) = _
    rw [if_neg (by simp)]
  · have e : X = 15 := by omega
    subst e
    rw [o65_kAt_pad]
    rfl
theorem o65_kCo (X : ℕ) (hX : X < 16) : kCo (kAt K o65S X) = if X = 15 then 1 else 0 := by
  by_cases h : X < 15
  · have e := o65_kAt_lt ⟨X, h⟩
    simp only at e
    rw [e, if_neg (by omega)]
    rfl
  · have e : X = 15 := by omega
    subst e
    rw [o65_kAt_pad, if_pos rfl]
    show ((1 : ℕ) : K) = 1
    exact Nat.cast_one

/-- a key's entry: its weight, and the mask form's value there -/
theorem keyRow_cf_key (c : MCl K o65J) (b : Fin 15) :
    (keyRow 4 (kAt K o65S) c).cf (.inl b) = Blocks.eqN 4 0 c.pt b.1 + c.mf (.inl b) :=
  keyRow_cf_of 4 (kAt K o65S) c (.inl b) b.1 (by have := b.2; omega) fun X hX => o65_kCf_key X hX b
/-- a plane's or a mask's entry: the mask form alone: no key's weight stands outside the keys'
message -/
theorem keyRow_cf_other (c : MCl K o65J) (j : Fin 16 ⊕ Fin 104) : (keyRow 4 (kAt K o65S) c).cf (.inr
    j) = c.mf (.inr j) :=
  keyRow_cf_zero 4 (kAt K o65S) c (.inr j) fun X hX => o65_kCf_other X hX j
/-- the target: the padded place's share is taken out -/
theorem keyRow_tg (c : MCl K o65J) : (keyRow 4 (kAt K o65S) c).tg = c.tg - Blocks.eqN 4 0 c.pt 15 *
    1 :=
  keyRow_tg_of 4 (kAt K o65S) c 15 1 (by decide) fun X hX => o65_kCo X hX

/-! ### at the chain's own claim -/
theorem clK_pt (x : o65A.X4) :
    (o65A.clK x).pt = Blocks.nat fun i : Fin (0 + 4) => ((o65A.IK.setV 4).DK.lv 4).pnt x.2 i.rev :=
        rfl
theorem keyRow_cf_chain (x : o65A.X4) (b : Fin 15) :
    (keyRow 4 (kAt K o65S) (o65A.clK x)).cf (.inl b) =
      eqLow (fun i : Fin (0 + 4) => ((o65A.IK.setV 4).DK.lv 4).pnt x.2 i) b.1 + (o65A.clK x).mf
          (.inl b) := by
  rw [keyRow_cf_key]
  congr 1
  exact eqN_rev (0 + 4) _ _
theorem keyRow_tg_chain (x : o65A.X4) :
    (keyRow 4 (kAt K o65S) (o65A.clK x)).tg =
      (o65A.clK x).tg - eqLow (fun i : Fin (0 + 4) => ((o65A.IK.setV 4).DK.lv 4).pnt x.2 i) 15 * 1
          := by
  rw [keyRow_tg]
  exact congrArg (fun z => (o65A.clK x).tg - z * 1) (eqN_rev (0 + 4) _ 15)

end Cb.Tw
#print axioms Cb.Tw.keyRow_cf_chain
#print axioms Cb.Tw.keyRow_tg_chain
#print axioms Cb.Tw.RA_closed
#print axioms Cb.Tw.RA_false_a
#print axioms Cb.Tw.eqN_rev
#print axioms Cb.Tw.blocks_eqN_rev
#print axioms Cb.Tw.sigma_ext
#print axioms Cb.Tw.sigma_keyRow
#print axioms Cb.Tw.keyRow_cf_key
#print axioms Cb.Tw.keyRow_cf_other
#print axioms Cb.Tw.keyRow_tg
