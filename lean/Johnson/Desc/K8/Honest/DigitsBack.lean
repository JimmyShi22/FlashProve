-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/DigitsBack.lean: THE SMALLNESS TEST: FROM THE LAW's SENTENCE `DigitsAt` BACK
TO THE ITEM constr l lookDigits OF THE COMPOSED MEANING: the other way of the library's
`digitsAt_mgAll` (Johnson/Desc/Sound/MgAt/K3DigitsAt.lean). Four theorems; no definition; none of
the library's goals.

  `cols_cover_test`   where the public test `DgP.colsTest` says yes and there is a matrix: every
                   column below mz is a matrix's first row's column plus a row of that matrix. KIN,
                   NOT CALLED: the library's `cols_cover` (Johnson/Desc/K8/Honest/TiesLaidOf.lean)
                   has the like end under `ColsFacts`, which asks besides that each matrix has a row
  `digIn_of_digitsOf`   so `DigitsOf`, matrix by matrix, gives the lookup's `DgP.DigIn`, column by
                   column: the other way of `digIn_digitsOf`
                   (Johnson/Desc/First/Look/K3DigInCols.lean)
  `part_of_digitsOf`   at publicOf's public parameters: DigitsOf at the plan's parameters and the
                   lookup's reading gives the lookups' own sentence `digitsPartK3`
  **`constr_of_digitsAt`**   hX · hD · hx as in `digitsAt_mgAll` · there is a matrix · hT: DigitsOf
                   at the state's own parameters gives it at the plan's · hE: the two readings are
                   one at the cells that the sentence reads ⊢ DigitsAt at `cellsAhead` gives (mgAll
                   Dm Mg).constr l .lookDigits (z, s) y w
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. TACTICS THAT SEARCH: `omega` on columns and numbers of
matrices; `simp only` with a written list on two lines, as in the library's proof the other way.
Limits. Implications: hT and hE are paid at no state here. Nothing on the run "small".
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.Sound.MgAt.K3DigitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Meaning)

/-- **Every column below mz lies in a matrix.** -/
theorem cols_cover_test {tl : HTailF2} (h : DgP.colsTest tl = true) (hN : 0 < tl.NM) {c : ℕ}
    (hc : c < tl.mz) :
    ∃ μ, μ < tl.NM ∧ ∃ i, i < DgP.mOf tl μ ∧ c = DgP.offOf tl μ + i := by
  have h' := of_decide_eq_true (Bool.and_eq_true _ _ ▸ h).1
  have h0 : DgP.offOf tl 0 = 0 := of_decide_eq_true (Bool.and_eq_true _ _ ▸ h).2
  have key : ∀ k, k < tl.NM → c < DgP.offOf tl k + DgP.mOf tl k →
      ∃ μ, μ < tl.NM ∧ ∃ i, i < DgP.mOf tl μ ∧ c = DgP.offOf tl μ + i := by
    intro k
    induction k with
    | zero =>
      intro hk hlt
      exact ⟨0, hk, c, by omega, by omega⟩
    | succ k ih =>
      intro hk hlt
      by_cases hge : DgP.offOf tl (k + 1) ≤ c
      · exact ⟨k + 1, hk, c - DgP.offOf tl (k + 1), by omega, by omega⟩
      · have hk' : k < tl.NM := by omega
        have e := h' k hk'
        rw [if_pos hk] at e
        exact ih hk' (by omega)
  have hlast := h' (tl.NM - 1) (by omega)
  rw [if_neg (by omega)] at hlast
  exact key (tl.NM - 1) (by omega) (by omega)

/-- **DigitsOf, matrix by matrix, gives DigIn.** -/
theorem digIn_of_digitsOf {J : Type} (tl : HTailF2) (en : DgP.Ent3 → J) (ν : J → Cb.Gl.E)
    (hc : DgP.colsTest tl = true) (hN : 0 < tl.NM)
    (H : DigitsOf tl (fun t u c => ν (en (t, u, c)))) : DgP.DigIn tl en ν := by
  have both : ∀ i : DgP.Pl tl,
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.lo (ν (en (tl.ix.ZZ, i.2.val, i.1.val))) ∧
        Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.hi
          (ν (en (tl.ix.ZZ, i.2.val, tl.mz + i.1.val))) := by
    intro i
    obtain ⟨μ, hμ, j, hj, e⟩ := cols_cover_test hc hN i.1.isLt
    have h0 : 0 < (tl.mats.getD μ {}).m := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
    have z0 : (tl.zzCol μ 0 0).getD 0 = DgP.offOf tl μ := by
      unfold HTailF2.zzCol
      simp only [hμ, h0, decide_true, Bool.and_self, if_true, Nat.zero_le, Nat.zero_mul,
        Nat.zero_add, Nat.add_zero]
      rfl
    have z1 : (tl.zzCol μ 1 0).getD 0 = tl.mz + DgP.offOf tl μ := by
      unfold HTailF2.zzCol
      simp only [hμ, h0, decide_true, Bool.and_self, if_true, Nat.le_refl, Nat.one_mul,
        Nat.add_zero]
      rfl
    obtain ⟨k0, k1⟩ := H μ hμ i.2.val i.2.isLt j hj
    rw [z0] at k0
    rw [z1, Nat.add_assoc] at k1
    rw [e]
    exact ⟨k0, k1⟩
  exact ⟨fun i => (both i).1, fun i => (both i).2⟩

/-- **To the lookups' own sentence, at publicOf's public parameters.** -/
theorem part_of_digitsOf {P Cells Tok : Type} {pol KL : ByteArray} {layout : Option ByteArray}
    {X : Verify.Public} (hX : Verify.publicOf pol KL layout = .ok X)
    (D : Desc.First.Look.Sent) (L : K3Letters Cells Tok) {i : ℕ} {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X i = some (x, tl)) (hN : 0 < tl.NM) (a : P × Desc.First.S)
    (y : Strs) (w : Desc.Wit Cells Tok MsgT)
    (H : DigitsOf tl (fun t u c =>
      digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w (enOf x.arrays (t, u, c)))) :
    digitsPartK3 X D L i a y w :=
  fDig_part X D L i hx a y w (digIn_of_digitsOf tl (enOf x.arrays) _
    (cols_at (colsAll_of_public hX) (digAt_is (shapeZAll_of_public hX) hx)) hN H)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **FROM «THE DIGITS ARE IN THEIR TABLES» BACK TO THE ITEM, AT THE COMPOSED MEANING.** -/
theorem constr_of_digitsAt {pol KL : ByteArray} {layout : Option ByteArray}
    (hX : Verify.publicOf pol KL layout = .ok X)
    (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3) {l : ℕ} {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl)) (hN : 0 < tl.NM) (z : P) (s : Desc.First.S)
    (y : Strs) (w : Desc.Wit (CellsQ rows cols) Tok MsgT)
    (hT : ∀ ts, s.tl? = some ts → ∀ A, DigitsOf ts A → DigitsOf tl A)
    (hE : ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m → ∀ b, b < 2 →
      digMu x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1) Dm.l3.arr w
          (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i)) =
        cellsAhead Dm.cs Dm.arr Dm.ms Dm.N l (z, s) w tl.ix.ZZ u
          ((tl.zzCol μ b 0).getD 0 + i)) :
    DigitsAt (cellsAhead Dm.cs Dm.arr Dm.ms Dm.N l (z, s)) s w →
      (mgAll Dm Mg).constr l .lookDigits (z, s) y w := by
  rintro ⟨ts, hts, H⟩
  rw [digPart_mgAll Dm Mg hD l (z, s) y w]
  exact part_of_digitsOf hX Dm.sent Dm.l3 hx hN (z, s) y w
    (digitsOf_cells tl (cellsAhead Dm.cs Dm.arr Dm.ms Dm.N l (z, s) w) _
      (fun μ hμ u hu i hi b hb => (hE μ hμ u hu i hi b hb).symm) (hT ts hts _ H))

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.cols_cover_test
#print axioms VerifiableInference.Desc.First.K8.Honest.digIn_of_digitsOf
#print axioms VerifiableInference.Desc.First.K8.Honest.part_of_digitsOf
#print axioms VerifiableInference.Desc.First.K8.Honest.constr_of_digitsAt
