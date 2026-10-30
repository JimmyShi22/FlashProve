-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ShareSStatement.lean: THE MERGE's SHARE OF THE THREAD's DEBT
`ExchangeS`, AT ITS TWO ITEMS, IN THE FRAME's OWN FORM `ExchangeAtS` (Honest/Thread/SharesS.lean),
WITH ITS THREE PREMISES ON THE STATE STATED FROM THE PAIR OF THE THREAD AND WHAT IS SAID: A
STRUCTURE OF PREMISES AND A STATEMENT: NOTHING IS PROVED IN THIS FILE, and it is none of the
library's goals: it is a lemma's statement.

Why. `HeadMergeShare` (ShareStatement.lean of this folder) ends in a definition of that file's own,
typed before the frame's, and takes three of its thirteen premises (front · pubTest · ties) at every
stand at which the thread holds (`Thr`). The frame asks such a premise from the pair (`ThrS T
Said`), and its share by its own name.

  `K11SeatedS`        `K11Seated`'s text, made by program: one letter more (Said), and the pair for
                      the thread at its three places; the ten other fields to the letter
  `HeadMergeShareS`   under it: `ExchangeAtS T Said b i₁ ∧ ExchangeAtS T Said b i₂`

Limits. Those of ShareStatement.lean: ALL THIRTEEN ARE PREMISES; front, pubTest and ties are debts,
shown at no thread: "the claim is true" stands among the ties. The coins' type hangs on the kind's
own place while pl is free. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareStatement
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

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

/-- **THE PREMISES, FROM THE PAIR.** The letters: as at `K11Seated`; Said: the chain's sentence on
what earlier rounds showed. -/
structure K11SeatedS {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
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
  front : ∀ k s m E, ThrS T Said b k s m E →
    ∃ a claim x0 b9, s.here = .head a ∧ a.claim = some claim ∧ a.x = some x0 ∧
      segAt? s = some b9 ∧
      LedgerReady (wsForkStart #[x0.sV] #[oneE]) (headMergeShape P.lay.lk) a.F ∧
      OnBytes.PscRun.Filled a.F x0.sV ∧
      (∃ un, P.lay.U[claim.ui]? = some un ∧ wsClaimShape P.lay claim = .ok () ∧
        UnitOK P.lay.lk un ∧ un.off + un.rows ≤ P.lay.m0) ∧
      claims m.st.input.x m.st.heard = [claim]
  /-- FROM THE THREAD IN FRONT AND THE MEMBER's STEP: the public test behind -/
  pubTest : ∀ blk k s m E ds y cols s', ThrS T Said b k s m E → T.Stepped blk k s m E ds y cols s' →
    T.bs[b]? = some blk →
    formsIn (Readers.ofStates (mergeStates "the merge")) ((Dof m.st.input).N.group seg) 8
      "the merge" s' = true
  /-- the ties, at the thread's witness at every continuation -/
  ties : ∀ blk k s m E ds y cols s' a claim x0 b9 a9, ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk → s.here = .head a →
    a.claim = some claim → a.x = some x0 → segAt? s = some b9 → segAt? s' = some a9 →
    ∀ ds', MergeTiesAt P (Dof m.st.input) seg (toP (T.seat k y.2 s').1) s' a claim x0 b9 a9
      (weights m.st.input.w₀) (coins k) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeShareS : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type) (rows cols nR : ℕ)
    (Xp : OnBytes.Model.Verify.Public)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (i₁ i₂ : T.ι) (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) (seg : ℕ) (l : Link S Claim),
    K11SeatedS T Said b P claims weights name pl coins i₁ i₂ toP toW Dof Mg₀ seg l →
    ExchangeAtS T Said b i₁ ∧ ExchangeAtS T Said b i₂

end ProofFile.Honest.K11
