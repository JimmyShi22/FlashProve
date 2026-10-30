-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsTests.lean: the smallness test's three steps behind the adding AS ONE
(testsP, SelfRows.lean): what its yes hands out; and K08Tested with that one yes in place of the two steps'.

Statements and proofs. No routine of `verify-on-bytes` is named. USED OF THE FILES UNDER OnBytes/, ON
RECORDS AND PLAIN DATA ALONE: excBind_ok; what K08Tested's statement names (EquationsTested.lean).
Main names:
  tests_ok: testsP nU tl F = .ok Fc gives: the first test's yes at F; the weights' step returns Fc at F; the
    test by a second computation says yes at Fc.
  **K08Tests** (a closed Prop), **k08_tests**: K08Tested's statement, its two premises on the two steps
    replaced by testsP's yes at the ledger behind the adding.
Limits: those of K08Tested. From a yes alone. That a block of the description calls testsP at that record and
that ledger is not said here.

-/
import Johnson.Desc.First.TailClaims.EquationsTested
import Johnson.Desc.First.TailClaims.SelfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow)

/-- **What a yes of the three in a row hands out.** -/
theorem tests_ok {nU : Array Nat} {tl : HTailF2} {F Fc : Fork} (h : testsP nU tl F = .ok Fc) :
    selfTestP tl nU F = .ok () ∧ coefficientsP tl F = .ok Fc ∧ rkSelfTestP tl Fc = .ok () := by
  unfold testsP at h
  obtain ⟨_, h1, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨F', h2, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h3, h⟩ := (excBind_ok _ _ _).1 h
  obtain rfl : F' = Fc := Except.ok.inj h
  exact ⟨h1, h2, h3⟩

/-- **K08Tested, with the three steps behind the adding as one.** -/
def K08Tests : Prop :=
  ∀ (K : Type) [Field K] (J : Type) [Fintype J] (Y : Lay J) (ρ : Reading K) (W : World K)
    (m : J → K) (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 G Fc : Fork)
    (look cls : List Claim) (ls : Array E) (nU : Array Nat),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    addAll F1 (look ++ cls) = some G → Fits tl →
    testsP nU { tl' with lsTail := ls } G = .ok Fc →
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

theorem k08_tests : K08Tests := by
  intro K _ J _ Y ρ W m front tl tl' funs F F1 G Fc look cls ls nU hs h hadd hfit ht hW hrows hU
  exact k08_tested K J Y ρ W m front tl tl' funs F F1 G Fc look cls ls hs h hadd hfit
    (tests_ok ht).2.1 (tests_ok ht).2.2 hW hrows hU

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.tests_ok
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_tests
