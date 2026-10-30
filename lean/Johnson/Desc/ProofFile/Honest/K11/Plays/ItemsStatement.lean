-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ItemsStatement.lean: THE TWO SENTENCES OF THE TABLE OF
JOINTS THAT THE MERGE OF THE CLAIMS ON THE WEIGHTS OWES BEHIND ITS STEP, AT THE ROUNDS THAT THE ROW
PLAYS: ONE STATEMENT: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is none
of the library's goals: a lemma's statement.

What is said. The row is played at challenges that fit the declared rounds
(Honest/K11/Plays/Statement.lean), and THE VERIFIER's OWN DECISION SAYS YES ON THESE ROUNDS, from s
to s'. Under the premises below, at s':
  the table's sentence on the run "the merge" holds (`formsQ`, Johnson/Desc/Sound/FormsQ.lean), and
  every row that the reader off the verifier's state gives holds in the sense of the law on the pile
  of pending rows (`Holds`, Johnson/Desc/K13/Law/Means.lean): the conclusion of `woAt`
  (Johnson/Top/H0/Fill/FillP1.lean).

The premises, by sort.
  THE STATE IN FRONT: it stands inside the head's link, with a claim and what the head heard; the
    ledger is ready for the call; the claim's value is laid; the claim's unit is in order.
  THE TIES BETWEEN THE HONEST SIDE AND THE VERIFIER's STATE: the part's claims are that one claim;
    the part's weights are the cells.
  THE TIES BETWEEN THE COINS AND THE WITNESS's READINGS: the mask row, as the table's sentence reads
    it at s', has the first run's coins under the sumcheck's own slots; the index masks' next entry
    at s' is the second run's first coin.
  THE CLAIM IS TRUE, at these cells and at the mask row AS IT IS READ AT s, the state in front: what
    was shown under the slot of its value, less the factor there times the mask entry there, is the
    claim's value. (That the decision leaves what the mask row is read off is shown in the proof.)
  THE PUBLIC TEST `formsIn` holds at s'.
  THE PILE's WITNESS: its matrix is the cells; its mask entries of the index masks' message are idx.

Limits. Every premise is a premise: none is shown of a run. The reader is the run itself, not the
readers of a link of the description. No letter of a thread stands here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.InnerStatement
import Johnson.Desc.K11.Exchange.Statement
import Johnson.Desc.K11.Exchange.RowStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E zeroE oneE TensorRow)
open OnBytes.Slice (GE)
open OnBytes.Model (Reading WsClaim wsClaimShape wsForkStart)
open OnBytes.Road (Wm UnitOK claimVal)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.First.MergeLaw (mergeStates)
open VerifiableInference.Desc.K9 (segAt? formsIn Readers)
open VerifiableInference.Desc.K13.Law (Wit Holds lowBits)
open VerifiableInference.Desc.Sound (formsQ dataQ MsgQ)
open VerifiableInference.Desc.Part.MaskedSum (LedgerReady)
open Johnson.Desc.First.Walk.Law (rowAt ledgerAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries headMergeDecide)
open ProofFile.Honest.SumLaw (SumCoins firstRun endRun)

/-- The statement. s, s': the verifier's states in front of the decision and behind it. own, rd, a9:
the seats that the table's sentence may read, the witness's reader, the open segment's part at s';
b9: that part at s. cells, idx: the witness's cells and the index masks' entries. n, lin: the plan's
number of claims on the weights and the shape of the test on the matrix. wK: the pile's witness. Not
proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeItems : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X) (s s' : S)
    (a : HeadOwn) (claim : WsClaim) (x0 : OnBytes.Model.Head.Heard) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → MsgQ) (b9 a9 : VerifiableInference.Desc.K9.Part)
    (cells : Wm GE) (idx : ℕ → GE) (n : ℕ) (lin : OnBytes.Params.LinShape) (nR kC : ℕ)
    (wK : Wit GE nR kC),
    -- the row is played, and the verifier's own decision says yes on its rounds
    drawsFit ((mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }) (d₀ :: ds) = true →
    headMergeDecide P s ((headMergeSaid P claims weights c m d₀ ds).map noDigest) = .ok s' →
    -- the state in front
    s.here = .head a → a.claim = some claim → a.x = some x0 →
    LedgerReady (wsForkStart #[x0.sV] #[oneE]) (headMergeShape P.lay.lk) a.F →
    OnBytes.PscRun.Filled a.F x0.sV →
    (∃ un, P.lay.U[claim.ui]? = some un ∧ wsClaimShape P.lay claim = .ok () ∧
      UnitOK P.lay.lk un ∧ un.off + un.rows ≤ P.lay.m0) →
    -- the honest side and the verifier's state
    claims m.st.input.x m.st.heard = [claim] →
    (∀ r k, r < P.lay.m0 → k < 2 ^ P.lay.lk →
      Reading.gl.val (eOfF ((weights m.st.input.w₀).entry r k)) = cells r k) →
    -- the coins and the witness's readings
    segAt? s' = some a9 →
    (∀ i, i < 2 * P.lay.lk + 2 →
      (dataQ own a9 rd).mask (a.F.next + i) = Reading.gl.val ((firstRun c).getD i zeroE)) →
    (∀ l c' l', ledgerAt s' = some l → takeEntry l = some (c', l') →
      idx c' = Reading.gl.val ((endRun c).headD zeroE)) →
    -- the claim is true: at the mask row as it is read AT THE STATE IN FRONT
    segAt? s = some b9 →
    Reading.gl.val (a.F.vp.getD x0.sV zeroE) -
        Reading.gl.val (a.F.mf.getD x0.sV zeroE) * (dataQ own b9 rd).mask x0.sV =
      claimVal Reading.gl P.lay cells claim →
    -- the public test
    formsIn (Readers.ofStates (mergeStates "the merge")) own 8 "the merge" s' = true →
    -- the pile's witness
    P.lay.lk = kC → nR ≤ 2 ^ lin.kRow → (∀ j, nR ≤ j → ∀ C, cells j C = 0) →
    (∀ (i : Fin nR) (C : ℕ), C < 2 ^ kC → wK.mat i (lowBits kC C) = cells i C) →
    (∀ c', wK.mask ⟨s'.out.indexMasks, c'⟩ = idx c') →
    formsQ (Readers.ofStates (mergeStates "the merge")) own 8 "the merge" s' rd ∧
      ∀ r : TensorRow, rowAt P.lay n lin s' = some r → Holds Reading.gl wK r

end ProofFile.Honest.K11
