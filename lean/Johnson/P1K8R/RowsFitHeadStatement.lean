-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsFitHeadStatement.lean: THE PUBLIC TEST `rowsFitB` ("the rows fit",
Johnson/Desc/First/Link/K9RowsAsk.lean) SAYS YES AT THE OUTPUT HEAD's SEGMENT, NUMBER 24: in the
goals' scope, where the declared round of the head's batching has 24,653,737 rows; and so under the
library's head. THE END IS THE CLAUSE AT l = 24 OF THE SENTENCE `RowsAsked Z`
(Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean), TO THE LETTER. STATEMENTS ALONE: three definitions
of propositions; no definition of another kind. NOTHING IS PROVED IN THIS FILE, and none is one of
the library's goals: they are lemmas' statements.

WHAT IT IS NOT. ONE CLAUSE OF THE 25 OF `RowsAsked`: NOTHING AT THE 24 OTHER SEGMENTS. No verifier
asks the test. AT THE FORMAT's EARLIER HASH ALONE (OnBytes.secondHashFunction): of the two sister tests' payers
`nuAsked_of_head` (K9NuPaid.lean) and `posAsked_whole` (LayTablesInScope.lean) are general in that
letter.

  `BuiltHeadTl`         in scope, at the plain road's public part Z and a blank ground: a built
                        segment X stands at 24, and its data of the smallness test are the head's
                        plan's: X.tl = Z.p.X.H.tl
  `RowsFitHeadInScope`  the same premises, `publicOf`'s return, and K9's numbers at 24 with
                        24,653,737 rows: the test's yes at 24
  `RowsFitHeadOfHead`   the test's yes at 24 at the head's Zp (`P5J.AtMg OnBytes.secondHashFunction`)

NEAR. `reads_head_eq` (Law/K9ReadsHeadPaid.lean) is called: by its own head "of the test's clause at
segment 24 this is the third". `posAsked_head` (K9PosHeadPaid.lean): in its proof the built segment
at 24 is found by another road, at every earlier hash; it does not hand out the first statement.
`built_plan` (FitsMsBuilt.lean), by two of the three calls by which the first statement goes here:
the data of the blank ground's built segment at l are a layers' plan's, an attention plan's or the
head's: which of the three at which l it does not say. `rows_join`
(Johnson/Desc/First/Link/Law/K9RowsParts.lean, another group of authors' work): claims, ties'
indices and reads' indices are together at most the plan's rows, general in the sort of plan; the
second statement's proof adds up the same three at the head's plan, where they are just its rows;
`rows_join` is not called here.

Limits. A test's yes on public data. The full size alone. Nothing on any property.
-/
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K9Asks (rowsFitB)

/-- The statement on the built segment. Not proved here; a lemma's statement, none of the library's
goals. -/
def BuiltHeadTl : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (ly : ByteArray) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground),
    VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z →
    ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ →
    ∃ X, Z.p.built.links[24]? = some X ∧ X.tl = Z.p.X.H.tl

/-- The statement in scope. Not proved here; a lemma's statement, none of the library's goals. -/
def RowsFitHeadInScope : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (ly : ByteArray) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground),
    VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z →
    ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ →
    Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X →
    (∃ p, IM.k9At Z 24 = some p ∧ p.rows = 24653737) →
    ∃ X, Z.p.built.links[24]? = some X ∧ rowsFitB (ProofFile.k9Stretches Z) Z 24 X = true

/-- The statement under the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def RowsFitHeadOfHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
    P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF →
    ∃ X, Zp.p.built.links[24]? = some X ∧ rowsFitB (ProofFile.k9Stretches Zp) Zp 24 X = true

end P1K8

#print axioms P1K8.BuiltHeadTl
#print axioms P1K8.RowsFitHeadInScope
#print axioms P1K8.RowsFitHeadOfHead
