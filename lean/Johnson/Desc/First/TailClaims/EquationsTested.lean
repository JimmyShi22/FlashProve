-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsTested.lean: K08Claims with its premise RawRows replaced by five:
the description's own two plain steps behind the adding say yes (the weights of the virtual rows are
laid: coefficientsP, Coefficients.lean; the test by a second computation: rkSelfTestP, SelfTests.lean);
ReadsRaw at the ledger with the weights laid; two premises on public numbers. ReadsRaw is RawRows' whole
half on the world: RawRows is ReadsRaw with the ledger's written weights replaced by powers of the
batching element and by 1; what the two steps' yes adds is just that replacement.

Statements and proofs. After OnBytes/Tie/Pv/Tail/EndCoef.lean (coefficientsF_inv), which says the like
of the routine coefficientsF in a context. No routine of `verify-on-bytes` is named. USED OF THE FILES
UNDER OnBytes/, ON RECORDS AND PLAIN DATA ALONE: onRow, forIn_id_mem, id_bind_inv, ReadsRaw, UnitRow,
Fits, rowsForm, batchAt, topOf, readsList, posOf, uOf, colsU, Lay, Lay.cellAt, Reading, World.
Main names:
  coefBody_inv: a property of the ledger that every change of one virtual row keeps holds behind
    coefBody. coef_theta: so the batching element stays.
  **K08Tested** (a closed Prop), **k08_tested**: K08Claims' conclusion, from nine premises: one
    coefficient a slot, the two yeses, Fits, the two plain steps' yes behind the adding, ReadsRaw at the
    ledger with the weights laid, and two on public numbers.
Limits: those of K08Claims. ReadsRaw is a condition on the world: whoever makes the world of the
committed entries pays it. The two premises on public numbers stay. The weights' step is taken at the
ledger behind the adding itself; K08Raw (EquationsRaw.lean) takes any ledger with that batching element.

-/
import Johnson.Desc.First.TailClaims.EquationsRaw
import Johnson.Desc.First.TailClaims.Coefficients
import OnBytes.Tie.Pv.Tail.EndCoef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow)

/-- A property of the ledger that every change of one virtual row keeps holds behind coefBody. After
coefficientsF_inv. -/
theorem coefBody_inv (P : Fork → Prop)
    (hP : ∀ (r : Fork) (t' r' : Nat) (f : HRow → HRow), P r → P (HTailF2.onRow r t' r' f))
    (tl : HTailF2) (g : Forest.Heard) (F : Fork) (h0 : P F) : P (coefBody tl g F) := by
  unfold coefBody
  simp only [Id.run]
  refine id_bind_inv P P _ _ ?_ (fun r1 h1 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ h0
    intro n _ r hr
    cases tl.ix.U.getD n none with
    | none => exact hr
    | some t =>
      by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
      · simp only [hk, if_true]; exact hP _ _ _ _ hr
      · simp only [hk]; exact hr
  refine id_bind_inv P P _ _ ?_ (fun r2 h2 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ h1
    intro q _ r hr
    show P (forIn (tl.zOf q).pieces r _ : Id Fork)
    rw [← Array.forIn_toList]
    refine forIn_id_mem P _ _ _ ?_ hr
    intro p _ r' hr'
    exact hP _ _ _ _ hr'
  refine id_bind_inv P P _ _ ?_ (fun r3 h3 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ (hP _ _ _ _ (hP _ _ _ _ h2))
    intro e _ r hr
    exact hP _ _ _ _ hr
  refine id_bind_inv P P _ _ ?_ (fun r4 h4 => h4)
  refine forIn_id_mem P _ _ _ ?_ (hP _ _ _ _ h3)
  intro mu _ r hr
  exact hP _ _ _ _ hr

/-- The step that lays the weights keeps the batching element. -/
theorem coef_theta {tl : HTailF2} {G Fc : Fork} (h : coefficientsP tl G = .ok Fc) :
    Fc.theta = G.theta := by
  unfold coefficientsP at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact coefBody_inv (fun r => r.theta = G.theta) (fun _ _ _ _ hr => hr) _ _ _ rfl

/-- **K08Claims, with RawRows replaced by the two plain steps' yes behind the adding, ReadsRaw and two
premises on public numbers.** The steps are asked at the record that "K8.equations" returned, with any
lsTail laid. -/
def K08Tested : Prop :=
  ∀ (K : Type) [Field K] (J : Type) [Fintype J] (Y : Lay J) (ρ : Reading K) (W : World K)
    (m : J → K) (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 G Fc : Fork)
    (look cls : List Claim) (ls : Array E),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    addAll F1 (look ++ cls) = some G → Fits tl →
    coefficientsP { tl' with lsTail := ls } G = .ok Fc →
    rkSelfTestP { tl' with lsTail := ls } Fc = .ok () →
    ReadsRaw ρ { tl' with lsTail := ls } funs Fc W (fun t r c => Y.cellAt m t r c) →
    (Fc.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2 →
    (∀ x ∈ readsList tl funs, UnitRow Fc (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU F1 (uOf tl x.1)) →
    ((rowsForm Y ρ tl funs F.planClaimsF).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ p.1 ∧ p.1 ≤ F.planClaimsF + topOf tl funs - 1) ∧
    ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length ∧ addAll F1 look = some X ∧
      addAll X four = some X4 ∧ addAll X4 rest = some G ∧
      G.total ρ W = X4.total ρ W +
        (batchAt (ρ.val F.theta) (rowsForm Y ρ tl funs F.planClaimsF)).gap m

theorem k08_tested : K08Tested := by
  intro K _ J _ Y ρ W m front tl tl' funs F F1 G Fc look cls ls hs h hadd hfit hco hrk hW hrows hU
  have hth : Fc.theta = F.theta := (coef_theta hco).trans (eq_link hs h hadd).2.2.1
  exact k08_claims K J Y ρ W m front tl tl' funs F F1 G look cls hs h hadd hfit
    (k08_raw K ρ W _ front tl tl' funs F F1 Fc cls ls h hth hrk hW hrows hU)

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.coefBody_inv
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_tested
