-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwForms.lean.
The verifier's last step: from the read-out `TX` of the assembled lookup (state, the masked claim on
all 2^v keys, the rows) to linear forms on the caller's entries alone.

Definitions, statements and proofs. No verifier is named here: `oneK`
(OnBytes/Tie/Pv/Lookup/Know/TwOne.lean) lays `outA` behind the assembled
lookup's verifier.
Main names:
  `keyRow k kAt c`: the masked claim c on the keys as a row: where key number X is an entry
    (`kAt X = inl j`) its weight `eqN k 0 c.pt X` stands at j; where it is a public constant
    (`inr a`) the share weight · a goes into the target and no entry is weighed.
  `keyRow_iff`: `c.Holds k (the keys read by kAt) m ↔ (keyRow k kAt c).Holds m`, for every c, m.
  `outL k kAt x := x.2.2 ++ [keyRow k kAt x.2.1]`: defined at every `x : TX`; a list of any length.
  `KeyRd A kAt`: the one hypothesis: the keys of A are read by kAt at the key numbers below 2^v.
    Public data alone: it reads no witness: it is a statement for every m.
  `out_iff`: under `KeyRd A kAt`: `A.lk.out id id x m ↔ ∀ r ∈ outA A kAt x, r.Holds m`, general in
    A: the forms meet their targets, and nothing else. `out_rows`: the same in the words of
    `RowsHold`.
  At the builder `keyA E S`: `keyA_rd`, `outS`. At the small lookup: `o65Out`, `o65_out_iff`,
    `o65_RA_iff`.
Limits: `out_iff` reaches every A whose keys are so read: kAt does not read the state; a key is one
entry with coefficient 1, or a constant (no shift, no key that is a sum of entries). `keyA_rd` holds
by rfl and says nothing by itself: what says something is tie_key_* in
OnBytes/Tie/Pv/Lookup/Port/TwTies.lean, at the small lookup alone. Cb/Pv/Lookup/Asm/AsmH.lean has
another lemma named `LkAsmH.out_iff`: `A.out_iff` is that one; `out_iff A` in `Cb.Tw` is this one.

-/
import OnBytes.Tie.Pv.Lookup.Value.TwO65

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Finset
open TwNums (Sizes)

section General
variable {E J : Type} [Field E] [Fintype J] [DecidableEq J]

/-- the weight that key number X's share lays on entry j; the constant that it lays into the
target -/
def kCf (q : J ⊕ E) (j : J) : E := Sum.elim (fun j' => if j' = j then 1 else 0) (fun _ => 0) q
def kCo (q : J ⊕ E) : E := Sum.elim (fun _ => 0) id q

theorem kRead (q : J ⊕ E) (m : J → E) : Sum.elim m id q = ∑ j, kCf q j * m j + kCo q := by
  cases q with
  | inl j' => simp [kCf, kCo]
  | inr a => simp [kCf, kCo]

/-- The keys' claim as a row on the entries. -/
def keyRow (k : ℕ) (kAt : ℕ → J ⊕ E) (c : MCl E J) : Row E J :=
  ⟨fun j => (∑ X ∈ range (2 ^ k), Blocks.eqN k 0 c.pt X * kCf (kAt X) j) + c.mf j,
    c.tg - ∑ X ∈ range (2 ^ k), Blocks.eqN k 0 c.pt X * kCo (kAt X)⟩

theorem keyRow_iff (k : ℕ) (kAt : ℕ → J ⊕ E) (c : MCl E J) (m : J → E) :
    c.Holds k (fun b => Sum.elim m id (kAt b)) m ↔ (keyRow k kAt c).Holds m := by
  unfold MCl.Holds Row.Holds keyRow Blocks.ext
  have h : ∑ i, ((∑ X ∈ range (2 ^ k), Blocks.eqN k 0 c.pt X * kCf (kAt X) i) + c.mf i) * m i =
      (∑ X ∈ range (2 ^ k), Blocks.eqN k 0 c.pt X * ∑ j, kCf (kAt X) j * m j) + ∑ i, c.mf i * m i :=
          by
    simp only [add_mul, sum_add_distrib, sum_mul, mul_sum]
    rw [sum_comm]
    congr 1
    exact sum_congr rfl fun X _ => sum_congr rfl fun j _ => by ring
  simp only [kRead, mul_add, sum_add_distrib]
  rw [h]
  constructor
  · intro e; rw [← e]; ring
  · intro e; rw [eq_sub_iff_add_eq] at e; rw [← e]; ring

/-- The out-statement: the rows as they are, then the keys' row. Public data alone: coefficients and
targets. -/
def outL {St : Type} (k : ℕ) (kAt : ℕ → J ⊕ E) (x : TX St E J) : List (Row E J) := x.2.2 ++ [keyRow
    k kAt x.2.1]

omit [Fintype J] in
theorem outL_length {St : Type} (k : ℕ) (kAt : ℕ → J ⊕ E) (x : TX St E J) : (outL k kAt x).length =
    x.2.2.length + 1 := by
  simp [outL]

end General

section Asm
variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E)

/-- The keys of A are read by kAt: each key number below 2^v is an entry or a public constant, the
same at every state and every m. -/
def KeyRd (kAt : ℕ → A.J ⊕ E) : Prop := ∀ (st : A.St) (m : A.J → E), ∀ b < 2 ^ (A.v' + 1), A.key st
    m b = Sum.elim m id (kAt b)

/-- the out-statement at A -/
def outA (kAt : ℕ → A.J ⊕ E) (x : TX A.St E A.J) : List (Row E A.J) := outL (A.v' + 1) kAt x

/-- General in A: the output claim of the assembled lookup is: the forms of outA meet their targets,
and nothing else. -/
theorem out_iff (kAt : ℕ → A.J ⊕ E) (hk : KeyRd A kAt) (x : TX A.St E A.J) (m : A.J → E) :
    A.lk.out id id x m ↔ ∀ r ∈ outA A kAt x, r.Holds m := by
  have h1 : x.2.1.Holds (A.v' + 1) (A.key x.1 m) m ↔ (keyRow (A.v' + 1) kAt x.2.1).Holds m := by
    rw [← keyRow_iff]
    unfold MCl.Holds
    rw [Blocks.ext_congr (hk x.1 m)]
  show (x.2.1.Holds (A.v' + 1) (A.key x.1 m) m ∧ RowsHold x.2.2 m ∧ True) ↔ _
  rw [h1]
  unfold outA outL RowsHold
  simp only [List.mem_append, List.mem_singleton, and_true]
  constructor
  · rintro ⟨hK, hR⟩ r (hr | rfl)
    · exact hR r hr
    · exact hK
  · intro h
    exact ⟨h _ (Or.inr rfl), fun r hr => h r (Or.inl hr)⟩

/-- The same in the words of `RowsHold`: a relation on the out-statement `b : List (Row E J)`. -/
theorem out_rows (kAt : ℕ → A.J ⊕ E) (hk : KeyRd A kAt) (x : TX A.St E A.J) (m : A.J → E) :
    A.lk.out id id x m ↔ RowsHold (outA A kAt x) m := out_iff A kAt hk x m

end Asm

/-! ### At the builder and at the small lookup -/

theorem keyA_rd (E : Type) [Field E] [Fintype E] (S : Sizes) : KeyRd (keyA E S) (kAt E S) := fun _ _
    _ _ => rfl

/-- the out-statement at the builder: it does not name `LkAsmH`: Lean gives code for it -/
def outS (E : Type) [Field E] (S : Sizes) (x : TX Unit E (JOf S)) : List (Row E (JOf S)) := outL
    (S.v' + 1) (kAt E S) x
theorem outS_eq (E : Type) [Field E] [Fintype E] (S : Sizes) : outA (keyA E S) (kAt E S) = outS E S
    := rfl

/-- the out-statement at the small lookup -/
def o65Out (x : TX Unit Cb.Gl.E o65J) : List (Row Cb.Gl.E o65J) := outS Cb.Gl.E TwNums.o65S x

/-- `out_iff` at the small lookup -/
theorem o65_out_iff (x : TX o65A.St Cb.Gl.E o65A.J) (m : o65A.J → Cb.Gl.E) :
    o65A.lk.out id id x m ↔ ∀ r ∈ o65Out x, r.Holds m :=
  out_iff o65A _ (keyA_rd _ _) x m

theorem o65_kAt_lt (b : Fin 15) : kAt Cb.Gl.E TwNums.o65S b.1 = .inl (.inl b) := by
  fin_cases b <;> rfl
theorem o65_kAt_pad : kAt Cb.Gl.E TwNums.o65S 15 = .inr ((1 : ℕ) : Cb.Gl.E) := rfl

/-- The in-relation at the small lookup is: every key that is not padding is a row of the table. -/
theorem o65_RA_iff (m : o65A.J → Cb.Gl.E) :
    o65A.lk.inR () m ↔ ∀ b : Fin 15, ∃ u < 2, m (.inl b) = ((u : ℕ) : Cb.Gl.E) := by
  show ((∀ b < 2 ^ (3 + 1), ∃ u < 2 ^ 1, Sum.elim m id (kAt Cb.Gl.E TwNums.o65S b) = ((u : ℕ) :
      Cb.Gl.E)) ∧ True) ↔ _
  rw [and_true]
  constructor
  · intro h b
    have := h b.1 (by have := b.2; omega)
    rw [o65_kAt_lt b] at this
    exact this
  · intro h b hb
    by_cases h15 : b < 15
    · have := h ⟨b, h15⟩
      have e := o65_kAt_lt ⟨b, h15⟩
      simp only at e
      rw [e]
      exact this
    · have e : b = 15 := by omega
      subst e
      exact ⟨1, by decide, by rw [o65_kAt_pad]; rfl⟩

end Cb.Tw
#print axioms Cb.Tw.keyRow_iff
#print axioms Cb.Tw.out_iff
#print axioms Cb.Tw.o65_out_iff
#print axioms Cb.Tw.o65_RA_iff
