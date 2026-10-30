-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MainTable.lean: THE TEXT's MAIN TABLE AT ONE POSITION IS THE TYPED
GROUP's CUBE OF MAIN ROWS THERE: the two premises of `main_symbol` (WordJoin.lean) paid off
`main_laid` and `main_off` (LongTables.lean), where the layout fits the typed group. Theorems. It
changes no other file.

  `rowAt_spec`: the row that `rowAt i` names has no slot and the number i.
  `lay_cols`: a yes of layMembers: every member laid has a column at that position.
  `LaysFit R L ix`: the layout fits the typed group, member by member, ix a being a's number among
    the layout's members: one to one and onto · a member's flag «kept» is false just where its rows
    have no slot · an unkept member's first row is the typed corner R.oM a.
  `main_table`: **R.Good · LaysFit · a yes of layMembers from the blank tables · each member's
    column has R.nM a main symbols, and symbol j reads as sym ⟨a, j⟩ ⊢ at every vertex b: where
    `ord b` names the row r the table's entry rowNo b reads as sym r; where it names none, as 0.**
Limits. `LaysFit` is a premise on the state's layout (kin of `CubeFits` with
`ShapesAre`, Johnson/Desc/First/Close/Law/CubeAt.lean, LayoutOfShapes.lean): not paid here. That a
column's symbol reads as what `view` shows is a premise. The main table alone. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WordJoin
import Johnson.Desc.First.Link.Law.LongMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Top.H
open VerifiableInference.Desc.Own (Tables layMember layMembers)
open VerifiableInference.Desc.First.Close (foldedAt)

theorem rowAt_spec {S : Sig GE} (R : RowsK S) {i : ℕ} {r : Σ a : R.G.A, Fin (R.nM a)}
    (h : R.rowAt i = some r) : R.slot r = none ∧ R.atM r = i := by
  unfold RowsK.rowAt at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact hex.choose_spec
  · exact nomatch h

theorem lay_cols (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' →
      ∀ w ∈ ws, ∃ c, colAt opened i w = some c
  | [], _, _, _, _, hw => nomatch hw
  | v :: ws, t, t', h, w, hw => by
    unfold layMembers at h
    obtain ⟨col, hc, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, _, h3⟩ := Option.bind_eq_some_iff.1 h2
    rcases List.mem_cons.1 hw with rfl | hw'
    · exact ⟨col, hc⟩
    · exact lay_cols L opened i ws t₁ t' h3 w hw'

/-- The layout fits the typed group, member by member. -/
structure LaysFit {S : Sig GE} (R : RowsK S) (L : GroupLayout) (ix : R.G.A → ℕ) : Prop where
  lt : ∀ a, ix a < L.members.size
  inj : Function.Injective ix
  onto : ∀ w, w < L.members.size → ∃ a, ix a = w
  unkept : ∀ r, R.slot r = none → L.kept.getD (ix r.1) false = false
  free : ∀ a, L.kept.getD (ix a) false = false → ∀ j, R.slot ⟨a, j⟩ = none
  first : ∀ a, L.kept.getD (ix a) false = false → L.mainFirst.getD (ix a) none = some (R.oM a)

section
variable {S : Sig GE} (R : RowsK S) {L : GroupLayout} {ix : R.G.A → ℕ}

/-- A number that lies in an unkept member's block of real rows is a row's without a slot. -/
theorem off_of_ne (Ft : LaysFit R L ix) {a' : R.G.A} {n i : ℕ} (hn : n = R.nM a')
    (hi : ∀ j : Fin (R.nM a'), R.slot ⟨a', j⟩ = none → R.atM ⟨a', j⟩ ≠ i) :
    OffMain L n (ix a') i := by
  by_cases hk : L.kept.getD (ix a') false = true
  · exact Or.inl hk
  · have hk' : L.kept.getD (ix a') false = false := by simpa using hk
    refine Or.inr fun f hf => ?_
    obtain rfl : R.oM a' = f := Option.some.inj ((Ft.first a' hk').symm.trans hf)
    by_contra hc
    have h1 : R.oM a' ≤ i := by omega
    have h2 : i - R.oM a' < R.nM a' := by omega
    exact hi ⟨i - R.oM a', h2⟩ (Ft.free a' hk' _) (by
      show R.oM a' + (i - R.oM a') = i
      omega)

/-- **THE TEXT's MAIN TABLE IS THE TYPED CUBE.** -/
theorem main_table (hg : R.Good) (Ft : LaysFit R L ix) {opened : Array (Array Column)} {i : ℕ}
    {t : Tables}
    (hl : layMembers L opened i (List.range L.members.size) (blankTables L) = some t)
    (sym : (Σ a : R.G.A, Fin (R.nM a)) → GE)
    (hz : ∀ a c, colAt opened i (ix a) = some c → c.main.size = R.nM a)
    (hs : ∀ a c (j : Fin (R.nM a)), colAt opened i (ix a) = some c →
      readV c.main j.val = sym ⟨a, j⟩) :
    (∀ b r, R.Sh.ord b = some r → readV t.main (Sz.rowNo b) = sym r) ∧
      ∀ b, R.Sh.ord b = none → readV t.main (Sz.rowNo b) = 0 := by
  refine ⟨fun b r hb => ?_, fun b hb => ?_⟩
  · obtain ⟨h1, h2⟩ := rowAt_spec R (show R.rowAt (Sz.rowNo b) = some r from hb)
    obtain ⟨a, j⟩ := r
    obtain ⟨c, hc⟩ := lay_cols L opened i _ _ _ hl (ix a) (List.mem_range.2 (Ft.lt a))
    have hk := Ft.unkept ⟨a, j⟩ h1
    have e := main_laid L opened i _ _ _ hl List.nodup_range (ix a)
      (List.mem_range.2 (Ft.lt a)) hk (R.oM a) (Ft.first a hk) c hc j.val
      (by rw [hz a c hc]; exact j.isLt) fun w' hw' hne c' hc' => by
        obtain ⟨a', rfl⟩ := Ft.onto w' (List.mem_range.1 hw')
        refine off_of_ne R Ft (hz a' c' hc') fun j' hj' e' => hne ?_
        have := hg.injM ⟨a', j'⟩ ⟨a, j⟩ hj' h1 e'
        rw [(Sigma.mk.inj_iff.1 this).1]
    rw [← h2]
    show readE (t.main.getD (R.oM a + j.val) zeroE) = _
    rw [e]
    exact hs a c j hc
  · have e := main_off L opened i _ _ _ hl (Sz.rowNo b) fun w' hw' c' hc' => by
      obtain ⟨a', rfl⟩ := Ft.onto w' (List.mem_range.1 hw')
      refine off_of_ne R Ft (hz a' c' hc') fun j' hj' e' => ?_
      have h3 := R.rowAt_atM hg ⟨a', j'⟩ hj'
      rw [e'] at h3
      exact nomatch (show R.rowAt (Sz.rowNo b) = none from hb).symm.trans h3
    show readE (t.main.getD (Sz.rowNo b) zeroE) = 0
    rw [e]
    show readE ((Array.replicate (2 ^ L.k) zeroE).getD (Sz.rowNo b) zeroE) = 0
    have : (Array.replicate (2 ^ L.k) zeroE).getD (Sz.rowNo b) zeroE = zeroE := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [this, readE_zero]

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowAt_spec
#print axioms VerifiableInference.Desc.LinkJoin.lay_cols
#print axioms VerifiableInference.Desc.LinkJoin.off_of_ne
#print axioms VerifiableInference.Desc.LinkJoin.main_table
