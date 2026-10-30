-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRngLkp.lean: "the digits are in their tables" in the letters of the lookup (`Lk`,
Cb/Ld/LdLkp.lean).

This file restates one claim with which an approximate range check ends, that all digits are in
their tables, as two claims of the form that a lookup argument takes.

Definitions, statements (`Cb.Spec.ldRng_keys`, `Cb.Spec.ldRng_lk`) and proofs. Plain mathematics; no
protocol.
The range check (Cb/Ld/LdRng.lean) ends with the claim that all low digits lie in [0, q) and all
high digits in [0, H) (`Cb.RngPk.InTabs`). A lookup (Cb/Ld/LdLkp.lean: `Lk`) takes a claim "2^v
keys, numbered from 0, are entries of a table with 2^d entries, numbered from 0".

Main names:
  `rngKeys p e d`: the digits of one kind in a row: key number b is the digit of the pair (row of
    cells, combination) with the number b under e; zeros after the last. e: any numbering of these
    pairs.
  `rngLk ..`: the lookup claim for one kind of digits: the keys `rngKeys p e (dig m)`; the table
    u ↦ u mod q on 2^dT indices (Cb/Gen/RngLkp.lean: `tabMod`); "more": what else is claimed and
    rides along.
  `Spec.ldRng_keys`: the first clause (`InTable`) of the relaxed claim of `rngLk ..` (`Lk.inR`,
    Cb/Ld/LdLkp.lean) says that every digit of that kind is the image of a natural number below q,
    if 0 < q ≤ 2^dT and the number of digits is at most 2^v.
  `Spec.ldRng_lk`: under `p.OK`, q ≤ 2^dq, H ≤ 2^dH and a number of digits of each kind of at most
    2^v, the two claims, the second riding along in the first, say: `InTabs`, and what rides along.

Limits: no lookup is run. This file says nothing on multiplicities. The caller of a lookup sends
them: after the ternary matrix (Cb/Ld/LdRng.lean: Θ, round 1), with the digits. This file says
nothing on one table for both kinds of digits or for digits and other keys. The conditions that a
lookup itself puts on v, d and the characteristic are its own.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRng
import Cb.Ld.LdLkp
import Cb.Gen.RngLkpProofs

set_option autoImplicit false

namespace Cb
open Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

section
variable {E St M : Type} [Field E] (p : RngPar) {K : ℕ} (e : p.Row × p.U ≃ Fin K)

/-- The digits of one kind in a row, then zeros. -/
def rngKeys (d : p.Row → p.U → E) : ℕ → E :=
  pad K fun b => if h : b < K then d (e.symm ⟨b, h⟩).1 (e.symm ⟨b, h⟩).2 else 0

/-- The lookup claim for one kind of digits. -/
def rngLk (v dT q : ℕ) (dig : M → p.Row → p.U → E) (more : St → M → Prop) : Lk E St M :=
  ⟨v, dT, fun _ m => rngKeys p e (dig m), fun _ => tabMod q, more⟩

end

namespace Spec

def ldRng_keys : Prop :=
  ∀ (E : Type) [Field E] (p : RngPar) (K : ℕ) (e : p.Row × p.U ≃ Fin K)
      (v dT q : ℕ) (d : p.Row → p.U → E),
    0 < q → q ≤ 2 ^ dT → K ≤ 2 ^ v →
    (InTable v dT (rngKeys p e d) (tabMod q) ↔ ∀ r u, InTab q (d r u))

/-- Under the hypotheses below, the two lookup claims on the digits say that the digits are in their
tables, and what rides along. -/
def ldRng_lk : Prop :=
  ∀ (E St M : Type) [Field E] (p : RngPar) (K : ℕ) (e : p.Row × p.U ≃ Fin K) (v dq dH : ℕ)
      (dg : M → p.Dg E) (more : St → M → Prop) (st : St) (m : M),
    p.OK → p.q ≤ 2 ^ dq → p.H ≤ 2 ^ dH → K ≤ 2 ^ v →
    ((rngLk p e v dq p.q (fun m => (dg m).1) (rngLk p e v dH p.H (fun m => (dg m).2) more).inR).inR
        st m ↔
      InTabs p.q p.H (dg m) ∧ more st m)

end Spec

theorem ldRng_keys : Spec.ldRng_keys := by
  intro E _ p K e v dT q d hq hT hK
  unfold rngKeys
  rw [inTable_pad E v dT q K _ hq hT hK]
  constructor
  · intro h r u
    have h1 := h (e (r, u)).1 (e (r, u)).2
    rw [dif_pos (e (r, u)).2] at h1
    simpa using h1
  · intro h b hb
    rw [dif_pos hb]
    exact h _ _

theorem ldRng_lk : Spec.ldRng_lk := by
  intro E St M _ p K e v dq dH dg more st m h hq hH hK
  have hH0 : 0 < p.H := by
    rcases Nat.eq_zero_or_pos p.H with h0 | h0
    · have h1 := h.qH
      have h2 := h.B1
      have h3 := h.BD
      rw [h0] at h1
      simp at h1
      omega
    · exact h0
  show (InTable v dq (rngKeys p e (dg m).1) (tabMod p.q) ∧
      (InTable v dH (rngKeys p e (dg m).2) (tabMod p.H) ∧ more st m)) ↔
    _
  rw [ldRng_keys E p K e v dq p.q _ h.q0 hq hK, ldRng_keys E p K e v dH p.H _ hH0 hH hK]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

end Cb
