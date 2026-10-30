-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsFitAttStatement.lean: THE PUBLIC TEST `rowsFitB` ("the rows fit",
Johnson/Desc/First/Link/K9RowsAsk.lean) AT THE TWELVE ATTENTION SEGMENTS, 2 g + 1: ITS YES, UNDER
ONE NAMED PREMISE: "each attention plan's own rounds count at most 14,166,783 rows" (a.own.rows ≤
14166783). STATEMENTS ALONE: three definitions of propositions; no definition of another kind.
NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

WHAT IT IS NOT. CONDITIONAL: THE NAMED PREMISE IS NOT PAID IN THIS FILE. UNDER THE HEAD it is paid
in RowsAskedOfHead.lean of this folder (`rowsFit_att_paid`, by `planRows_by_plan`,
PlanRowsAtHead.lean): there the third statement's end stands with no premise more. IN SCOPE ALONE,
as the second statement takes it, it is not paid there: the library's `own_at_places`
(Johnson/Desc/First/Att/Row/K5OwnAtPlaces.lean) has every field of a.own in scope but rows. So of
the sentence `RowsAsked Z` (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean) these twelve clauses are
not paid by this file alone. No verifier asks the test. At the format's second hash function alone
(OnBytes.secondHashFunction).

  `AttLeftAtMost`      where `publicOf` returns X, no scope, at each stored attention plan a: the
                       test's left side is at most a.own.rows
  `RowsFitAttInScope`  in scope, at the plain road's public part Z and a blank ground, g below 12:
                       K9's numbers at 2 g + 1 with 14,166,783 rows, and the named premise at g:
                       the test's yes at 2 g + 1
  `RowsFitAttOfHead`   under the library's head (`P5J.AtMg OnBytes.secondHashFunction`) and the named premise at
                       every g below 12: the test's yes at every 2 g + 1

IT STANDS OVER A FILE THAT IS ANOTHER GROUP OF AUTHORS' WORK:
Johnson/Desc/First/Link/Law/K9RowsParts.lean (`reads_att`, `rows_join`).

NEAR. `rows_att` (K9RowsParts.lean): the first statement at what `Attention.plan` returns, under two
premises; here these are paid and the plan is the stored one. `posAsked_att` (K9PosAttPaid.lean): a
sister test's yes at these segments.

Limits. A test's yes on public data, under a premise. The full size alone. Nothing on any property.
-/
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K9Asks (rowsFitB firstB readsB attPairs)

/-- The statement on the left side. Not proved here; a lemma's statement, none of the library's
goals. -/
def AttLeftAtMost : Prop :=
  ∀ (pol KL : ByteArray) (lay : Option ByteArray) (X : Verify.Public),
    Verify.publicOf pol KL lay = .ok X → ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
    a.nLin + (firstB a.seam.tl + readsB a.seam.tl.NM a.seam.tl.mats (attPairs a.S) *
      a.seam.tl.stepF) ≤ a.own.rows

/-- The statement in scope. Not proved here; a lemma's statement, none of the library's goals. -/
def RowsFitAttInScope : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (ly : ByteArray) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground),
    VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z →
    ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ →
    Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X →
    ∀ g, g < 12 → (∃ p, IM.k9At Z (2 * g + 1) = some p ∧ p.rows = 14166783) →
    (∀ a, Z.p.X.A[g]? = some a → a.own.rows ≤ 14166783) →
    ∃ X, Z.p.built.links[2 * g + 1]? = some X ∧
      rowsFitB (ProofFile.k9Stretches Z) Z (2 * g + 1) X = true

/-- The statement under the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def RowsFitAttOfHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF →
    (∀ g, g < 12 → ∀ a, Zp.p.X.A[g]? = some a → a.own.rows ≤ 14166783) →
    ∀ g, g < 12 → ∃ X, Zp.p.built.links[2 * g + 1]? = some X ∧
      rowsFitB (ProofFile.k9Stretches Zp) Zp (2 * g + 1) X = true

end P1K8

#print axioms P1K8.AttLeftAtMost
#print axioms P1K8.RowsFitAttInScope
#print axioms P1K8.RowsFitAttOfHead
