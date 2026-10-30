-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/FillFits.lean: THE PILE's FILLER `pileBySites`
(Johnson/Desc/K13/Honest/PileDefs.lean) MEETS THE PREMISE hfill OF THE THREE GUARDS UNDER THE THREAD
(`k13_guardsLeft_of_rows`, GuardsLeft.lean of this folder), FROM FOUR PUBLIC FACTS. One conditional
statement with its proof.

hfill asks: wherever the filler yields a row at all, its pile passes the test `pileFits`
(GuardsLeft.lean): the plan's number of rows, at least one; more than one column; each row with kCol
coordinates, a weight, and kRow variables in each weight.
  `pileBySites_hfill`: **hfill at `pileBySites lay S sites claims`, at every instance and all
    challenges**, from: sites.length = P.rows · lay.lk = P.lin.kCol · S.kRow = P.lin.kRow · 1 ≤
    P.lin.kCol. None of the four reads the instance or a challenge. By `pileBySites_fits`
    (Johnson/Desc/K13/Honest/RowReadsFits.lean).

What is not claimed. Any of the four facts at any plan. That the filler yields a row anywhere.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.GuardsLeft
import Johnson.Desc.K13.Honest.RowReadsFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Honest (rowReads MergeSite SiteClaims pileBySites
  pileBySites_fits)

/-- **THE FILLER `pileBySites` MEETS THE PREMISE hfill OF `k13_guardsLeft_of_rows`**, from four
public facts: there are as many sites as the plan has rows; the layout has as many column bits as
the plan's shape; the filler's shape has as many row bits as the plan's; the matrix has more than
one column. -/
theorem pileBySites_hfill {Xi : Type} (P : Where) (lay : WsLay) (S : LinShape)
    (sites : List MergeSite) (claims : SiteClaims Xi) (h1 : sites.length = P.rows)
    (h2 : lay.lk = P.lin.kCol) (h3 : S.kRow = P.lin.kRow) (h4 : 1 ≤ P.lin.kCol) :
    ∀ x heard, pileBySites lay S sites claims x heard ≠ [] →
      pileFits P ((pileBySites lay S sites claims x heard).map rowReads) = true := by
  intro x heard hne
  obtain ⟨hl, hr⟩ := pileBySites_fits lay S sites claims x heard hne
  unfold pileFits
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, decide_eq_true h4⟩, ?_⟩
  · rw [List.length_map, hl, h1]
    exact beq_self_eq_true _
  · cases hp : pileBySites lay S sites claims x heard with
    | nil => exact absurd hp hne
    | cons _ _ => rfl
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hq
    obtain ⟨a, b, c⟩ := hr row hrow
    have a' : row.psi.length = lay.lk := a
    have b' : row.g ≠ [] := b
    have c' : ∀ t ∈ row.g, t.vars = S.kRow := c
    show (row.psi.length == P.lin.kCol && !row.g.isEmpty && row.g.all (·.vars == P.lin.kRow)) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨by rw [a', h2]; exact beq_self_eq_true _, ?_⟩, ?_⟩
    · cases hg : row.g with
      | nil => exact absurd hg b'
      | cons _ _ => rfl
    · rw [List.all_eq_true]
      intro t ht
      rw [c' t ht, h3]
      exact beq_self_eq_true _

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.pileBySites_hfill
