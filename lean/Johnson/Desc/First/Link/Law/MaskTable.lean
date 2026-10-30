-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MaskTable.lean: THE TEXT's MASK TABLE AT ONE POSITION IS THE TYPED
GROUP's CUBE OF MASK ROWS THERE: the two premises of `mask_symbol` (WordJoin.lean) paid off
`mask_laid` and `mask_off` (LongMasks.lean), where the layout fits the typed group.
MainTable.lean's law for the mask rows. Theorems. No text already in the library turns.

  `ordZ_some`, `ordZ_none`: the mask row that `ordZ b` names has the number rowNo b; where it names
    none, no mask row has that number.
  `mask_table`: **R.Good · the members one to one and onto (LaysFit) · a member with mask rows has
    its first mask row at the typed corner R.oZ a · a yes of layMembers from the blank tables ·
    each member's column has R.nZ a mask symbols, and symbol j reads as sym ⟨a, j⟩ ⊢ at every
    vertex b of the cube of h variables: where `ordZ b` names the row r the table's entry rowNo b
    reads as sym r; where it names none, as 0.**
Limits. Those of MainTable.lean. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.MainTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Top.H
open VerifiableInference.Desc.Own (Tables layMember layMembers)

section
variable {S : Sig GE} (R : RowsK S) {L : GroupLayout} {ix : R.G.A → ℕ}

theorem ordZ_some {b : Fin R.s.h → Bool} {r : Σ a : R.G.A, Fin (R.nZ a)}
    (h : R.Sh.ordZ b = some r) : R.atZ r = Sz.rowNo b := by
  by_cases hex : ∃ r, R.atZ r = Sz.rowNo b
  · have e : R.Sh.ordZ b = some hex.choose := dif_pos hex
    rw [← Option.some.inj (e.symm.trans h)]
    exact hex.choose_spec
  · have e : R.Sh.ordZ b = none := dif_neg hex
    exact nomatch e.symm.trans h

theorem ordZ_none {b : Fin R.s.h → Bool} (h : R.Sh.ordZ b = none)
    (r : Σ a : R.G.A, Fin (R.nZ a)) : R.atZ r ≠ Sz.rowNo b := by
  intro hr
  have hex : ∃ r, R.atZ r = Sz.rowNo b := ⟨r, hr⟩
  have e : R.Sh.ordZ b = some hex.choose := dif_pos hex
  exact nomatch e.symm.trans h

theorem offZ_of_ne (hf : ∀ a, R.nZ a ≠ 0 → L.maskFirst.getD (ix a) none = some (R.oZ a))
    {a' : R.G.A} {n i : ℕ} (hn : n = R.nZ a')
    (hi : ∀ j : Fin (R.nZ a'), R.atZ ⟨a', j⟩ ≠ i) : OffMask L n (ix a') i := by
  intro f hf'
  by_cases h0 : R.nZ a' = 0
  · omega
  · obtain rfl : R.oZ a' = f := Option.some.inj ((hf a' h0).symm.trans hf')
    by_contra hc
    have h2 : i - R.oZ a' < R.nZ a' := by omega
    exact hi ⟨i - R.oZ a', h2⟩ (by
      show R.oZ a' + (i - R.oZ a') = i
      omega)

/-- **THE TEXT's MASK TABLE IS THE TYPED CUBE.** -/
theorem mask_table (hg : R.Good) (Ft : LaysFit R L ix)
    (hf : ∀ a, R.nZ a ≠ 0 → L.maskFirst.getD (ix a) none = some (R.oZ a))
    {opened : Array (Array Column)} {i : ℕ} {t : Tables}
    (hl : layMembers L opened i (List.range L.members.size) (blankTables L) = some t)
    (sym : (Σ a : R.G.A, Fin (R.nZ a)) → GE)
    (hz : ∀ a c, colAt opened i (ix a) = some c → c.mask.size = R.nZ a)
    (hs : ∀ a c (j : Fin (R.nZ a)), colAt opened i (ix a) = some c →
      readV c.mask j.val = sym ⟨a, j⟩) :
    (∀ b r, R.Sh.ordZ b = some r → readV t.mask (Sz.rowNo b) = sym r) ∧
      ∀ b, R.Sh.ordZ b = none → readV t.mask (Sz.rowNo b) = 0 := by
  refine ⟨fun b r hb => ?_, fun b hb => ?_⟩
  · have h2 := ordZ_some R hb
    obtain ⟨a, j⟩ := r
    obtain ⟨c, hc⟩ := lay_cols L opened i _ _ _ hl (ix a) (List.mem_range.2 (Ft.lt a))
    have hn : R.nZ a ≠ 0 := fun h0 => absurd j.isLt (by omega)
    have e := mask_laid L opened i _ _ _ hl List.nodup_range (ix a)
      (List.mem_range.2 (Ft.lt a)) (R.oZ a) (hf a hn) c hc j.val
      (by rw [hz a c hc]; exact j.isLt) fun w' hw' hne c' hc' => by
        obtain ⟨a', rfl⟩ := Ft.onto w' (List.mem_range.1 hw')
        refine offZ_of_ne R hf (hz a' c' hc') fun j' e' => hne ?_
        have := hg.injZ (a₁ := ⟨a', j'⟩) (a₂ := ⟨a, j⟩) e'
        rw [(Sigma.mk.inj_iff.1 this).1]
    have e2 : readV t.mask (Sz.rowNo b) = readV t.mask (R.oZ a + j.val) :=
      congrArg (readV t.mask) h2.symm
    exact e2.trans ((congrArg readE e).trans (hs a c j hc))
  · have e := mask_off L opened i _ _ _ hl (Sz.rowNo b) fun w' hw' c' hc' => by
      obtain ⟨a', rfl⟩ := Ft.onto w' (List.mem_range.1 hw')
      exact offZ_of_ne R hf (hz a' c' hc') fun j' => ordZ_none R hb ⟨a', j'⟩
    show readE (t.mask.getD (Sz.rowNo b) zeroE) = 0
    rw [e]
    show readE ((Array.replicate (2 ^ L.h) zeroE).getD (Sz.rowNo b) zeroE) = 0
    have : (Array.replicate (2 ^ L.h) zeroE).getD (Sz.rowNo b) zeroE = zeroE := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [this, readE_zero]

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ordZ_some
#print axioms VerifiableInference.Desc.LinkJoin.ordZ_none
#print axioms VerifiableInference.Desc.LinkJoin.mask_table
