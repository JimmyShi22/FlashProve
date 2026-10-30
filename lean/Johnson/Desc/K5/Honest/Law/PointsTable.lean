-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PointsTable.lean: the fields of two lists of named points that the
weights of an attention segment's tables read (TableFields,
Johnson/Desc/K5/Honest/Law/PointsFields.lean) are the same where the two lists are the same as far
as all parts of the segment's own rounds make them (PtsTo,
Johnson/Desc/K5/Honest/Law/PointsIs.lean). One statement with its proof, and a corollary.

  table_fields   CONDITIONAL: PtsTo at every number of a part gives TableFields
  points_laid    CONDITIONAL: so the two lists give every table the same matrix, run of rows,
                 weights and number of entries (PointsSame, Johnson/Desc/K5/Honest/Law/U3Law.lean)

Limits. That two lists meet PtsTo is shown elsewhere, under premises of its own. No property is
claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PointsIs
import Johnson.Desc.K5.Honest.Law.PointsFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open VerifiableInference.Desc.First.Att.P (Pts Geo LookIn)

/-- **The fields that the tables' weights read are the same.** CONDITIONAL: the two lists of points
are the same as far as the parts in front of part q make them, for every q. -/
theorem table_fields {x : OnBytes.Params.AttentionRounds} {p₀ p : Pts}
    (K : ∀ q, PtsTo x q p₀ p) : TableFields p₀ p := by
  have A := K (iHB x + 1)
  have hd := A.key.d
  simp only [divKey, Prod.mk.injEq] at hd
  have lt : ∀ j, j ≤ 10 → x.score.length + j < iHB x + 1 := fun j hj => by
    unfold iHB
    omega
  exact
    { scores := by
        apply List.ext_getElem?
        intro i
        have hk := congrArg (fun l => l[i]?) A.key.scores
        simp only [List.getElem?_map, Array.getElem?_toList] at hk ⊢
        cases a : p₀.scores[i]? with
        | none =>
          cases b : p.scores[i]? with
          | none => rfl
          | some k' =>
            rw [a, b] at hk
            cases hk
        | some k =>
          cases b : p.scores[i]? with
          | none =>
            rw [a, b] at hk
            cases hk
          | some k' =>
            rw [a, b] at hk
            have e : unitKey k = unitKey k' := Option.some.inj hk
            simp only [unitKey, Prod.mk.injEq] at e
            have r := (K (i + 1)).scR i (Nat.lt_succ_self i) k k' a b
            show some (unitView k) = some (unitView k')
            unfold unitView
            rw [e.2.2.2.2.2.2.2.2, e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2.1, e.2.2.1, r]
      ziW := hd.2.2.2.2.2.2.1
      zcW := hd.2.2.2.2.2.2.2.1
      ziX := hd.2.2.2.2.2.2.2.2.2.1
      wJv := A.wJv (lt 2 (by omega))
      scE := A.scE (lt 0 (by omega))
      vpm := A.vpm (lt 2 (by omega))
      vpd := A.vpd (lt 3 (by omega))
      ti := A.ti (lt 4 (by omega))
      scF := A.scF (lt 6 (by omega))
      scd := A.scd (lt 8 (by omega))
      scH := A.scH (lt 10 (by omega)) }

/-- So the two lists lay the same tables. CONDITIONAL: as `table_fields`. -/
theorem points_laid {x : OnBytes.Params.AttentionRounds} {p₀ p : Pts} (K : ∀ q, PtsTo x q p₀ p)
    (g : Geo) (lk : LookIn) : PointsSame g lk p₀ p :=
  pointsSame_of_fields g lk (table_fields K)

end H2K5.Honest

#print axioms H2K5.Honest.table_fields
#print axioms H2K5.Honest.points_laid
