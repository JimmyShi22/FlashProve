--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/WFoldSpec.lean: W IS THE COMMITTED FOLD: THE SENTENCE, AND TWO STATEMENTS. NO
PROOF HERE: each statement is a definition of a proposition; the proofs stand in WFoldSame.lean and
WFold.lean.

IN PLAIN WORDS. THE STEP WITHOUT CHANCE, AT ONE DRAWN POINT: if the point is of neither lost sort,
then near, RecAll and DotU of the message to come give that the table tab decodes under the key's
record, within the radius eM, to one matrix M; and that each entry of the vector that lies in the
request's message W is the sum of M's rows at that column, weighted by the g of the claim that the
record keeps.

  WFold            the sentence: tab decodes (DecX2), and W's message holds g^T M (the first part's
                   own WIs) at M := what it decodes to (TabX2), laid out as the matrix.
  Spec.same        WIs at that matrix IS VIs, the claim in front of "LIN point", where g is the
                   claim's weights and V is what W's message holds. Algebra; no challenge.
  Spec.fold        **the statement**.
OBJECT: b1, the first of blocks P: its own decide. USER: claim_at_yes (WFoldCaller.lean). FIELD:
none to the letter; the nearest: shared_joint_count, block 1's share.
LETTERS, ALL FREE, ALL BEHIND ONE "FOR ALL": P, b1 to b8, err, eM, rank, tab, s, s', rs, gs, psi, D,
m, rgw, g, V. tab IS A LETTER: no root, no oracle's string and no item of a statement is read here:
that tab is the stored table's columns is the caller's to say.
NOT THE ROUND's LAW. NO COUNT STANDS IN Spec.fold. That the point is not lost for this very vector
(not BadO ... V psi) is a premise AT the point: against a W chosen after psi the statement is
silent. What a round's law wants beside it: that W is fixed before the point is drawn, and the two
counts; the key's sort is counted by no theorem without a premise on codes.
ONE RADIUS: eM is the decoder's, near's and the bad points'.
What is not claimed. Anything: nothing is proved here.

-/
import Johnson.Desc.K14.Law.PointLift
import Johnson.Desc.K14.Law.PointKey2
import Johnson.Desc.K13.Law.StepBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K13.Law (EvalAt WIs matBy)

/-- **The sentence.** tab: a table's columns. D: a claim's row, a message's number and layout. m:
the words. -/
def WFold (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (key : TableKey) (D : EvalAt) (m : Words GE) : Prop :=
  DecX2 p err eM rank tab key ∧
    WIs (nR := p.S.matrixRows) (matBy p.S.kCol (matOf p.S.kLo (TabX2 p err eM rank tab key))) m
      D.row.g D.w D.lay

namespace Spec

/-- The two houses' sentences are one. -/
def same : Prop :=
  ∀ (S : LinShape) (D : EvalAt) (m : Words GE) (Tab : Nat → Nat → GE) (g V : Nat → GE),
    (∀ y < S.matrixRows,
      g y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum) →
    (∀ c < 2 ^ S.kCol, m D.w .main (D.lay.index c) = V c) →
    (WIs (nR := S.matrixRows) (matBy S.kCol (matOf S.kLo Tab)) m D.row.g D.w D.lay ↔
      VIs S g Tab V)

/-- **W is the committed fold.** -/
def fold : Prop :=
  ∀ (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit),
    blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] →
    P.par.S.fold.index.code.logN ≤ 32 →
  ∀ (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64)
    -- a yes of the block, and the point that it has drawn
    (s s' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (psi : Fin P.par.S.kCol → GE),
    b1.decide s rs gs = .ok s' →
    s'.loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn psi →
    s.loc.key.fits P.par.S.fold.index = true →
  ∀ (D : EvalAt) (m rgw : Words GE) (g V : Nat → GE),
    (∀ y < P.par.S.matrixRows,
      g y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum) →
    (∀ c < 2 ^ P.par.S.kCol, m D.w .main (D.lay.index c) = V c) →
    -- the point is of neither lost sort
    ¬ BadX2 P.par err eM rank eM tab s.loc.key (gamOf P.par.S.kLo P.par.S.fold.index.v psi) →
    ¬ BadO P.par.S g (TabX2 P.par err eM rank tab s.loc.key) V psi →
    -- what stands behind the block, still to be shown by the later blocks
    NearAt OnBytes.Model.Reading.gl P.par (withNext P.par s') rgw tab eM →
    RecAll OnBytes.Model.Reading.gl P.par (withNext P.par s') rgw →
    DotUAt P.par.S g (withNext P.par s').loc rgw V →
    WFold P.par err eM rank tab s.loc.key D m

end Spec

end Desc.K14.Law
