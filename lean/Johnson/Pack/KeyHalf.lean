-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/KeyHalf.lean: the keys' half of the record for weights-formedness at any number of
forests, over the index matrix of any value; forests cut in parts.

Definitions, statements and proofs. The library's builder of the record `LdWfP` (Cb/Ld/LdWf.lean)
is `BldWf` (Cb/Ld/LdBldWf.lean). Its keys' half needs no builder: the law `keyLin` holds for every
configuration and every record whose keys are affine in one column of the index matrix
(`LinKeys`, `ldWfK_keyLin`, Cb/Ld/LdWfKeys.lean). This file takes the matrix of any value P₀ and
writes such keys for any number of forests.
Main names:
  `KeysD P₀`: the data: the number of forests, their row variables, tables, offsets and row
    factors, and the batching's coefficients.
  `KeysD.T`: the record: from P₀ the messages' half, the matrix and the degree; the keys' half from
    the data. `KeysD.lin`, `KeysD.keyLin`: its keys are affine in one column; the law.
  `KeysD.laws`: `LdWfP.Laws` of it, from the law `describes` and two laws of the configuration.
  `inTable_split`: the keys of a forest of s + t variables lie in the table if and only if those of
    each of its 2^s parts of t variables do.
  `partO`, `partCo`, `key_part`: offsets and row factors of part j of a forest; its keys are the
    forest's keys from j 2^(r + k) on.
  `inT_parts`: if the parts from m on lie in the table, the forest lies in the table if and only if
    its first m parts do.
Limits: the law `describes` is not shown; `inT_parts` reduces it, forest by forest, to the whole
forest's and to a condition on the parts that are left out, which is a hypothesis here. The
messages' half of `KeysD.T` is that of P₀ and fits the new forests in no way; in the place of
`mult` stands the condition that is always true, so the clause `multOf` of `KeysD.laws` says
nothing. The record is meant as the keys' half of a record that gives the messages' half, `mult`
among it, anew and shows its own clause; whoever reads `mult` off `KeysD.T` itself has nothing.
No value is given.
-/
import Cb.Ld.LdWfKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Blocks Hiop

variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample}

/-- The data of the keys' half, over the index matrix of P₀. -/
structure KeysD (P₀ : LdWfP E C) where
  n : ℕ
  rv : ℕ → ℕ
  d : ℕ → ℕ
  o : ℕ → ℕ → E
  co : ℕ → ℕ → P₀.Rw → E
  tab : ℕ → ℕ → E
  Z : Evader E (Fin (n + 1))

variable {P₀ : LdWfP E C} (K : KeysD P₀)

/-- A key: affine in one column of the index matrix. -/
def KeysD.key (f : ℕ) (U : C.Msg) (b : ℕ) : E :=
  K.o f (b / 2 ^ P₀.k) +
    ∑ r, K.co f (b / 2 ^ P₀.k) r * P₀.mat U (r, Alg.bits P₀.k (b % 2 ^ P₀.k))

/-- The record. -/
@[reducible] def KeysD.T : LdWfP E C where
  S := P₀.S
  Sd := P₀.Sd
  Body := P₀.Body
  body := P₀.body
  bodyOf := P₀.bodyOf
  N := P₀.N
  ent := P₀.ent
  n := K.n
  v := fun f => K.rv f + P₀.k
  d := K.d
  key := K.key
  tab := K.tab
  mult := fun _ _ _ => True
  nR := P₀.nR
  gC := P₀.gC
  gR := P₀.gR
  Rw := P₀.Rw
  k := P₀.k
  mat := P₀.mat
  off := fun f z => ext (K.rv f) (K.o f) z
  gOf := fun f z r => ext (K.rv f) (fun u => K.co f u r) z
  cOf := fun f z i => z (K.rv f + (i : ℕ))
  Z := K.Z
  deg := P₀.deg
  wAt := P₀.wAt

theorem KeysD.lin : K.T.LinKeys K.rv K.o K.co :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The law `keyLin` of the record. -/
theorem KeysD.keyLin (f : ℕ) (hf : f ≤ K.T.n) (U : C.Msg) (z : ℕ → E) :
    ext (K.T.v f) (K.T.key f U) z =
      K.T.off f z + Alg.mle (fun c => ∑ r, K.T.gOf f z r * K.T.mat U (r, c)) (K.T.cOf f z) :=
  ldWfK_keyLin E C K.T K.rv K.o K.co K.lin f hf U z

/-- The laws of the record, from the law on the index set and two laws of the configuration. -/
theorem KeysD.laws (hd : ∀ U, (C.held U).isSome ↔ ∀ f, f ≤ K.n → K.T.InT f U)
    (h1 : ∀ i η, C.held (C.hold i η) = some i)
    (h2 : ∀ m r s, C.dcd (C.enc m r) (s, C.smp s m) = some m) : K.T.Laws :=
  ⟨hd, h1, h2, fun _ _ _ _ => trivial, K.keyLin⟩

/-! ### Forests cut in parts -/

omit [Field E] [Fintype E] in
/-- The keys of a forest of s + t variables lie in the table if and only if those of each of its
2^s parts of t variables do. -/
theorem inTable_split (s t d : ℕ) (key tab : ℕ → E) :
    Lkp.InTable (s + t) d key tab ↔
      ∀ j < 2 ^ s, Lkp.InTable t d (fun b => key (j * 2 ^ t + b)) tab := by
  constructor
  · intro h j hj b hb
    refine h _ ?_
    calc j * 2 ^ t + b < j * 2 ^ t + 2 ^ t := Nat.add_lt_add_left hb _
      _ = (j + 1) * 2 ^ t := by ring
      _ ≤ 2 ^ s * 2 ^ t := Nat.mul_le_mul_right _ hj
      _ = 2 ^ (s + t) := (pow_add 2 s t).symm
  · intro h b hb
    have hp : 0 < 2 ^ t := Nat.pos_of_ne_zero (by positivity)
    have hj : b / 2 ^ t < 2 ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp, ← pow_add]
      exact hb
    obtain ⟨u, hu, e⟩ := h (b / 2 ^ t) hj (b % 2 ^ t) (Nat.mod_lt _ hp)
    have e' : key (b / 2 ^ t * 2 ^ t + b % 2 ^ t) = tab u := e
    rw [Nat.div_add_mod' b (2 ^ t)] at e'
    exact ⟨u, hu, e'⟩

/-- Offsets and row factors of part j, of r row variables, of a forest. -/
def partO (o : ℕ → E) (r j : ℕ) : ℕ → E := fun u => o (j * 2 ^ r + u)
def partCo {Rw : Type} (co : ℕ → Rw → E) (r j : ℕ) : ℕ → Rw → E := fun u => co (j * 2 ^ r + u)

omit [Fintype E] in
/-- The keys of part j are the forest's keys from j 2^(r + k) on. -/
theorem key_part {Rw : Type} [Fintype Rw] (k r j b : ℕ) (o : ℕ → E) (co : ℕ → Rw → E)
    (m : Rw × (Fin k → Bool) → E) :
    partO o r j (b / 2 ^ k) + ∑ x, partCo co r j (b / 2 ^ k) x * m (x, Alg.bits k (b % 2 ^ k)) =
      o ((j * 2 ^ (r + k) + b) / 2 ^ k) +
        ∑ x, co ((j * 2 ^ (r + k) + b) / 2 ^ k) x *
          m (x, Alg.bits k ((j * 2 ^ (r + k) + b) % 2 ^ k)) := by
  have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  have e1 : (j * 2 ^ (r + k) + b) / 2 ^ k = j * 2 ^ r + b / 2 ^ k := by
    rw [pow_add, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.add_comm]
  have e2 : (j * 2 ^ (r + k) + b) % 2 ^ k = b % 2 ^ k := by
    rw [pow_add, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [e1, e2]
  rfl

omit [Field E] [Fintype E] in
/-- If the parts from m on lie in the table, the forest lies in the table if and only if its first
m parts do. -/
theorem inT_parts (s t d m : ℕ) (key tab : ℕ → E)
    (idle : ∀ j, m ≤ j → j < 2 ^ s → Lkp.InTable t d (fun b => key (j * 2 ^ t + b)) tab) :
    Lkp.InTable (s + t) d key tab ↔
      ∀ j < m, j < 2 ^ s → Lkp.InTable t d (fun b => key (j * 2 ^ t + b)) tab := by
  rw [inTable_split]
  constructor
  · exact fun h j _ hj => h j hj
  · intro h j hj
    by_cases hm : j < m
    · exact h j hm hj
    · exact idle j (Nat.le_of_not_lt hm) hj

end Johnson.Pack

#print axioms Johnson.Pack.KeysD.keyLin
#print axioms Johnson.Pack.KeysD.laws
#print axioms Johnson.Pack.inTable_split
#print axioms Johnson.Pack.key_part
#print axioms Johnson.Pack.inT_parts
