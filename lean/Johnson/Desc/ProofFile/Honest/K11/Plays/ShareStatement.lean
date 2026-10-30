-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ShareStatement.lean: THE SHARE OF THE MERGE OF THE CLAIMS ON
THE WEIGHTS IN A THREAD's DEBT `Exchange` (Honest/Thread/Pays.lean), AT THE TWO ITEMS THAT ARE ITS
TO FILL: STATEMENTS ALONE: three definitions that are needed, and one definition of a proposition.
NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: a lemma's statement.

THE THREAD T IS A VARIABLE. Every fact on its letters that is spent is a named premise: a field of
`K11Seated`.

  `ExchangeAt T b i`   `Exchange T b`'s own sentence at one item i
  `MergeTiesAt`        the ties AT ONE WITNESS: there are cells and entries of the index masks such
                       that: the part's weights are the cells; the mask row off the witness has the
                       first run's coins under the sumcheck's own slots; the index masks' next entry
                       is the second run's first coin; THE CLAIM IS TRUE; the pile's own reading of
                       the witness has these cells and these entries
  `K11Seated`          THE PREMISES, in four sorts:
                       THE MEMBER AND ITS HALF: the member number b is the kind's block as it stands
                         alone at a seat; the steps that the frame lays for it are the row's, at
                         coins that are a function of the run's;
                       THE TABLE: what the two items mean follows from the two fields of the
                         composed meaning of the table of joints at some data
                         (`mgAll`, Johnson/Desc/Sound/MgAll.lean), through a map of what was handed
                         to the chain and a map of the witness; the data's segment, link and numbers
                         are the kind's;
                       FROM THE THREAD IN FRONT: the verifier's state is ready for the merge, and
                         the part's claims are the state's one claim;
                       FROM THE THREAD IN FRONT AND THE MEMBER's STEP: the public test holds behind;
                         the ties hold at the thread's witness at every continuation
  `HeadMergeShare`     under `K11Seated`: `ExchangeAt` at both items

Limits. `member` AND `hears` NAME THE KIND's BLOCK AT THE LETTER P; what the kind's lot lays is
`K11.blkAt` (Johnson/Desc/ProofFile/Lot/K11.lean): unfolding alone will not meet these two fields:
`lotBlockIs` (Johnson/Desc/K11/Exchange/AtSeat.lean) lies between, where the step under the name
that the lot looks up is found. THE COINS' TYPE HANGS ON THE KIND's OWN PLACE (`headMergePlace P`),
while pl is free: `steps` can be met with a return only where pl is that place; elsewhere the share
holds for nothing. The last two sorts are debts, not facts on letters: who pays each is not said
here. The row owes three pins beside the two items. Every premise is a premise: none is shown at any
thread. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.K11.Plays.ItemsStatement
import Johnson.Desc.K11.Exchange.AtSeatStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E zeroE oneE)
open OnBytes.Slice (GE)
open OnBytes.Model (Reading WsClaim wsClaimShape wsForkStart)
open OnBytes.Road (Wm UnitOK claimVal)
open VerifiableInference.Desc (Block Link Claim Place Wit)
open VerifiableInference.Desc.First (S HeadOwn Meaning)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.First.MergeLaw (mergeStates)
open VerifiableInference.Desc.K9 (segAt? formsIn Readers)
open VerifiableInference.Desc.K13.Law (lowBits)
open VerifiableInference.Desc.Sound (dataQ MgData mgAll seatTab CellsQ MsgT)
open VerifiableInference.Desc.Part.MaskedSum (LedgerReady)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open ProofFile.Honest.SumLaw (SumCoins firstRun endRun)

/-- `Exchange T b`'s own sentence at one item. -/
def ExchangeAt {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk St Cl V W X Pb) (b : Nat)
    (i : T.ι) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items [i] k s' y.2 (E.add y.1)

/-- The ties at one witness v. P: the kind's public data. D, seg: the composed meaning's data and
the segment. z: what was handed to the chain. s': the verifier's state behind the decision; a,
claim, x0: the head's own part, the claim and what the head heard in front of it; b9, a9: the open
segment's part in front and behind. Wt: the part's weights. c: the coins. -/
def MergeTiesAt (P : HeadMergeP) {Xi' Pp Tok : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public} (D : MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ) (z : Pp)
    (s' : S) (a : HeadOwn) (claim : WsClaim) (x0 : OnBytes.Model.Head.Heard)
    (b9 a9 : VerifiableInference.Desc.K9.Part) (Wt : Weights) {n₁ n₂ : String}
    (c : SumCoins n₁ n₂ (headMergeJob P.lay)) (v : Wit (CellsQ rows cols) Tok MsgT) : Prop :=
  ∃ (cells : Wm GE) (idx : ℕ → GE),
    (∀ r k, r < P.lay.m0 → k < 2 ^ P.lay.lk → Reading.gl.val (eOfF (Wt.entry r k)) = cells r k) ∧
    (∀ i, i < 2 * P.lay.lk + 2 →
      (dataQ (D.N.group seg) a9 (seatTab D.cs D.arr D.ms v)).mask (a.F.next + i) =
        Reading.gl.val ((firstRun c).getD i zeroE)) ∧
    (∀ l c' l', ledgerAt s' = some l → takeEntry l = some (c', l') →
      idx c' = Reading.gl.val ((endRun c).headD zeroE)) ∧
    Reading.gl.val (a.F.vp.getD x0.sV zeroE) - Reading.gl.val (a.F.mf.getD x0.sV zeroE) *
        (dataQ (D.N.group seg) b9 (seatTab D.cs D.arr D.ms v)).mask x0.sV =
      claimVal Reading.gl P.lay cells claim ∧
    (∀ j, nR ≤ j → ∀ C, cells j C = 0) ∧
    (∀ (i : Fin nR) (C : ℕ), C < 2 ^ D.P13.lin.kCol →
      (D.rw13 (z, s') v).mat i (lowBits D.P13.lin.kCol C) = cells i C) ∧
    ∀ c', (D.rw13 (z, s') v).mask ⟨s'.out.indexMasks, c'⟩ = idx c'

/-- **THE PREMISES.** T, b: the thread and the member's number. P, claims, weights: the row's
letters. name, pl: the seat's name and place. coins: the coins of the sumcheck's part, of a run's
coins. i₁, i₂: the two items. toP, toW: what was handed to the chain, and the witness, as the
composed meaning takes them. Dof, Mg₀, seg, l: the composed meaning's data at an input, the meaning
beneath, the segment and its link. -/
structure K11Seated {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (i₁ i₂ : T.ι) (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) (seg : ℕ) (l : Link S Claim) : Prop where
  /-- the member is the kind's block as it stands alone at a seat -/
  member : T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl)
  /-- the steps that the frame lays for the member are the row's -/
  steps : ∀ k w st,
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w)
        [IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl] T.hs = .ok st →
      ∃ v q, st = (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).steps
        (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) v ((q, (), ()), coins k, ())
  /-- what the two items mean follows from the composed meaning's two fields -/
  merged : ∀ w a y v, (mgAll (Dof w) Mg₀).forms seg 9 "merged" (toP a.1, a.2) y (toW v) →
    T.means w i₁ a y v
  wo : ∀ w a y v, (mgAll (Dof w) Mg₀).wo seg (toP a.1, a.2) y (toW v) → T.means w i₂ a y v
  /-- the data's segment, its link, the kind's block in it; the data's numbers are the kind's -/
  head : ∀ w, T.valid w → (Dof w).links[seg]? = some .head
  link : ∀ w, T.valid w → (Dof w).lk seg = some l
  hears : l.hear[8]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl)
  lay : ∀ w, T.valid w → (Dof w).d1.lay = P.lay
  colBits : ∀ w, T.valid w → P.lay.lk = (Dof w).P13.lin.kCol
  rowsFit : ∀ w, T.valid w → nR ≤ 2 ^ (Dof w).d1.lin.kRow
  /-- FROM THE THREAD IN FRONT: each "there is" is the one value of a reader at the state -/
  front : ∀ k s m E, Thr T b k s m E →
    ∃ a claim x0 b9, s.here = .head a ∧ a.claim = some claim ∧ a.x = some x0 ∧
      segAt? s = some b9 ∧
      LedgerReady (wsForkStart #[x0.sV] #[oneE]) (headMergeShape P.lay.lk) a.F ∧
      OnBytes.PscRun.Filled a.F x0.sV ∧
      (∃ un, P.lay.U[claim.ui]? = some un ∧ wsClaimShape P.lay claim = .ok () ∧
        UnitOK P.lay.lk un ∧ un.off + un.rows ≤ P.lay.m0) ∧
      claims m.st.input.x m.st.heard = [claim]
  /-- FROM THE THREAD IN FRONT AND THE MEMBER's STEP: the public test behind -/
  pubTest : ∀ blk k s m E ds y cols s', Thr T b k s m E → T.Stepped blk k s m E ds y cols s' →
    T.bs[b]? = some blk →
    formsIn (Readers.ofStates (mergeStates "the merge")) ((Dof m.st.input).N.group seg) 8
      "the merge" s' = true
  /-- the ties, at the thread's witness at every continuation -/
  ties : ∀ blk k s m E ds y cols s' a claim x0 b9 a9, Thr T b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk → s.here = .head a →
    a.claim = some claim → a.x = some x0 → segAt? s = some b9 → segAt? s' = some a9 →
    ∀ ds', MergeTiesAt P (Dof m.st.input) seg (toP (T.seat k y.2 s').1) s' a claim x0 b9 a9
      (weights m.st.input.w₀) (coins k) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeShare : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type) (rows cols nR : ℕ)
    (Xp : OnBytes.Model.Verify.Public)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (i₁ i₂ : T.ι) (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) (seg : ℕ) (l : Link S Claim),
    K11Seated T b P claims weights name pl coins i₁ i₂ toP toW Dof Mg₀ seg l →
    ExchangeAt T b i₁ ∧ ExchangeAt T b i₂

end ProofFile.Honest.K11
