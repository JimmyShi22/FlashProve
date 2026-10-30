-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsAskedOfHeadStatement.lean: UNDER THE LIBRARY's HEAD THE PUBLIC SENTENCE `RowsAsked
Zp` (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean: at each of the 25 segments' numbers a built
segment stands, and the test `rowsFitB`, "the rows fit", says yes of it) HOLDS. STATEMENTS ALONE:
four definitions of propositions; no definition of another kind. NOTHING IS PROVED IN THIS FILE, and
none is one of the library's goals: they are lemmas' statements.

WHAT IT IS NOT. UNDER THE HEAD (`P5J.AtMg`), NOT IN THE GOALS' SCOPE ALONE. AT THE FORMAT's EARLIER
HASH ALONE (OnBytes.secondHashFunction). The full size alone. No verifier asks the test. Nothing on soundness,
on an honest prover or on hiding.

WHAT THE SENTENCE IS FOR. It is the premise of the laws `rows_fit_layers`, `rows_fit_att`,
`rows_fit_head` (K9RowsAskLaw.lean).

  `LayLeftAtMost`      in scope, where `publicOf` returns X, at each stored layers' plan hp: the
                       segment's tables can be laid, and the test's left side is at most hp.nBatched
  `RowsFitLayOfHead`   under the head: the test's yes at every 2 g, g below 12
  `RowsFitAttPaid`     under the head: the test's yes at every 2 g + 1, g below 12, with no premise
                       more
  `RowsAskedOfHead`    under the head: `RowsAsked Zp`

THE PROOFS' FILE RowsAskedOfHead.lean STANDS, AMONG OTHERS, OVER THESE SIXTEEN FILES, NONE OF WHICH
THIS FILE IMPORTS: Johnson/Desc/First/Link/Law/K9RowsParts.lean, another group of authors' work;
and, under Johnson/P1K8R/: RowsAtLink; and K9RowsByLink, HeadRowsInScope, RowsFitHead, RowsFitAtt,
SigmaBat, PlanRowsAtHead, ReadsLay, each with its statements' file.

NEAR. `k9Entry_gives` (Johnson/Desc/First/Link/Law/K9AsksLaw.lean) hands each of the sentence's
clauses out of an accept of what its own head calls the candidate row `k9Entry`. `nuAsked_of_head`
(K9NuPaid.lean), `posAsked_of_head` (LayTablesInScope.lean): the two sister sentences from the head.

Limits. A test's yes on public data. Nothing on any property.
-/
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K9Asks (rowsFitB firstB readsB layPairs RowsAsked)

/-- The statement on the left side. Not proved here; a lemma's statement, none of the library's
goals. -/
def LayLeftAtMost : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (X : Verify.Public) (g : Nat)
    (hp : Layer.HPlan2), VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    Verify.publicOf Pb.pol Pb.KL lay = .ok X → X.G[g]? = some hp →
    ∃ ps, layPairs X.layers g = some ps ∧
      hp.nLin + (firstB hp.tl + readsB hp.tl.NM hp.tl.mats ps * hp.tl.stepF) ≤ hp.nBatched

/-- The statement at the layers' segments. Not proved here; a lemma's statement, none of the
library's goals. -/
def RowsFitLayOfHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF →
    ∀ g, g < 12 → ∃ X, Zp.p.built.links[2 * g]? = some X ∧
      rowsFitB (ProofFile.k9Stretches Zp) Zp (2 * g) X = true

/-- The statement at the attention segments. Not proved here; a lemma's statement, none of the
library's goals. -/
def RowsFitAttPaid : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF →
    ∀ g, g < 12 → ∃ X, Zp.p.built.links[2 * g + 1]? = some X ∧
      rowsFitB (ProofFile.k9Stretches Zp) Zp (2 * g + 1) X = true

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def RowsAskedOfHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF → RowsAsked Zp

end P1K8

#print axioms P1K8.LayLeftAtMost
#print axioms P1K8.RowsFitLayOfHead
#print axioms P1K8.RowsFitAttPaid
#print axioms P1K8.RowsAskedOfHead
