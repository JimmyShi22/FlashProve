-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OmegaTable.lean: the half without chance of the named premise OmegaOfTable of
(Dot)'s joined law: if omega_col is col_psi_lo(u) on the rows of M, and the folded row's message is
the fold at gamma of the table's rows, then omega_col is M applied to the equality vector at the
shared point.

How the matrix is read off the table HERE, by a definition (matOf): the entry in row y and column
t + 2 ^ kLo r is what row r of the table holds at the place t + 2 ^ kLo y: the column's low kLo bits
are the place inside a block of a code row, its high bits the table's row.
  matOf           the matrix, off the table's rows.
  UIsFold         the folded row's message is the fold at gamma of the table's rows, on the places
                  that hold M.
  eqK_two         the equality vector at (psi_lo, gamma), at the column t + 2 ^ kLo r.
  omegaIs_of_col  **the identity.**
  omegaOfTable_of the same in the words of (fold)'s claim OmegaCol and of the named premise.

What is not claimed. THAT matOf IS THE MATRIX OF WHICH THE CLAIMS SPEAK: no lemma ties it to the
program's layout of the table or to the matrix through which W and the row weights are joined: the
named premise is paid at M := matOf kLo Tab alone. One tie is stated elsewhere: HeldTie
(Johnson/Desc/K13/Law/HeldTab.lean): the matrix that the configuration's cells hold is matOf of the
decoded table; heldTie_full (Johnson/Desc/Sound/HeldAlong.lean) has it at the release's
configuration, under three premises: the index's numbers, the matrix's two numbers, and that the
matrix fits in front of the cut. UIsFold is a premise: it is what the locations,
the record and the statement on codes are to give (the pin of the folded row). That the words of
omega_col on the last chain are those on the shared chain is not said here. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.DotLaw
import Johnson.Desc.K14.Law.GoodFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)

variable {K : Type} [Field K]

/-- The matrix, off the table's rows: row y, column c. -/
def matOf (kLo : Nat) (Tab : Nat → Nat → K) : Nat → Nat → K :=
  fun y c => Tab (c / 2 ^ kLo) (c % 2 ^ kLo + 2 ^ kLo * y)

/-- The folded row's message is the fold at gamma of the table's rows, on the places that hold M. -/
def UIsFold (R kLo v : Nat) (Tab : Nat → Nat → K) (gam : List K) (u : Nat → K) : Prop :=
  ∀ k < R * 2 ^ kLo, u k = ∑ r ∈ Finset.range (2 ^ v), eqK gam r * Tab r k

/-- The equality vector at (psi_lo, gamma), at the column t + 2 ^ kLo r. -/
theorem eqK_two (psiLo gam : List K) (t r : Nat) (ht : t < 2 ^ psiLo.length) :
    eqK (psiLo ++ gam) (t + 2 ^ psiLo.length * r) = eqK psiLo t * eqK gam r := by
  rw [eqK_append, eqK_add_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt ht, Nat.zero_add]

/-- **omega_col is M applied to the equality vector at the shared point.** -/
theorem omegaIs_of_col (R kLo v : Nat) (Tab : Nat → Nat → K) (psiLo gam : List K)
    (omega u : Nat → K) (hp : psiLo.length = kLo)
    (hO : ∀ y < R, omega y = ∑ t ∈ Finset.range (2 ^ kLo), eqK psiLo t * u (t + 2 ^ kLo * y))
    (hU : UIsFold R kLo v Tab gam u) :
    OmegaIs R (kLo + v) (matOf kLo Tab) (psiLo ++ gam) omega := by
  intro y hy
  rw [hO y hy, Nat.pow_add, sum_blocks, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have hk : t + 2 ^ kLo * y < R * 2 ^ kLo := by
    have h3 : (y + 1) * 2 ^ kLo ≤ R * 2 ^ kLo := Nat.mul_le_mul_right _ hy
    rw [Nat.succ_mul, Nat.mul_comm y] at h3
    omega
  rw [hU _ hk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e := eqK_two psiLo gam t r (by rw [hp]; exact ht')
  rw [hp] at e
  unfold matOf
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos kLo), Nat.div_eq_of_lt ht', Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht']
  ring

/-- The same in the words of (fold)'s claim and of (Dot)'s named premise, at one state d of the
shared chain. -/
theorem omegaOfTable_of (ρ : OnBytes.Model.Reading K) (S : LinShape) (d : St) (m : Words K)
    (Tab : Nat → Nat → K) (hp : d.loc.psiSh.length = S.kCol) (hO : OmegaCol ρ S d m)
    (hU : UIsFold S.matrixRows S.kLo S.fold.index.v Tab ((gamma S d.loc).map ρ.val)
      (uOf d.loc m)) :
    OmegaOfTable S (matOf S.kLo Tab) (d.loc.psiSh.map ρ.val) d.loc.oOmega
      (linLayOmega d.st.codes S) m := by
  have hl : ((d.loc.psiSh.take S.kLo).map ρ.val).length = S.kLo := by
    rw [List.length_map, List.length_take, hp]
    unfold LinShape.kCol
    omega
  have e : d.loc.psiSh.map ρ.val =
      (d.loc.psiSh.take S.kLo).map ρ.val ++ (gamma S d.loc).map ρ.val := by
    unfold gamma
    rw [← List.map_append, List.take_append_drop]
  unfold OmegaOfTable
  rw [e]
  exact omegaIs_of_col S.matrixRows S.kLo S.fold.index.v Tab _ _ _ _ hl hO hU

end Desc.K14.Law
