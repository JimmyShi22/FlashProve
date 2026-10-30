-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ScriptStatement.lean: WHAT THE KIND K11 ASKS OF THE THREAD's
WITNESS AT THE MERGE's MEMBER, IN ONE STRUCTURE: `K11Script`: a named premise on the frame's Script,
in the form that the frame asks of each kind; AND THE FIELD ties OF `K11SeatedS`
(ShareSStatement.lean of this folder) FROM IT AND TWO MORE PREMISES: three definitions, and A
STATEMENT: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the
library's goals: it is a lemma's statement.

  `K11Script`      three ties, each at every stand of the pair in front of the member, behind the
                   member's step, at the thread's witness at every continuation: maskTie: under the
                   slots that the merge's sumcheck takes, the segment's mask row holds the coins of
                   the row's first run · indexTie: at the entry that the ledger behind takes, the
                   index-mask message holds the one coin of the run "ends" · matTie: the committed
                   matrix holds the prover's weights' entries, below nR rows
  `weightCells`    the cells of which the claim's value is taken: the weights' entries below nR
                   rows; 0 from there on
  `K11ClaimTrue`   THE CLAIM IS TRUE: the shown value under the claim's slot, less its factor times
                   the mask row's entry there, is the claim's value on these cells
  `TiesOfScript`   `K11Script` · the layout has at most nR rows · `K11ClaimTrue`: the field ties, in
                   its own words

Why. `MergeTiesAt` (ShareStatement.lean of this folder) has seven clauses. Three of them, with the
two that tie the letters through which they speak, say nothing but: the witness's tables hold the
prover's coins and weights: at a free Script these are no theorems: they stand here as ONE NAMED
PREMISE, which whoever lays the Script pays. The two others stay the kind's: that the cells are 0
from row nR on holds by the choice of `weightCells`; that the claim is true is `K11ClaimTrue`.

Limits. ALL THREE ARE DEFINITIONS: PREMISES' FORMS: NOTHING IS CLAIMED OF THEM, AND NOTHING SHOWS
THAT THEY CAN BE MET: no Script is laid anywhere. THE LETTER coins IS FREE HERE: AT AN ARBITRARY ONE
NOBODY CAN PAY maskTie OR indexTie: they are meant at what the book lends the kind's row
(`headMergeCoins`, SeatFieldsStatement.lean of this folder). matTie ASKS A LITTLE MORE THAN THE TWO
CLAUSES FOR WHICH IT STANDS, WHERE THE LAYOUT HAS FEWER THAN nR ROWS: on the rows from m0 to nR
these ask nothing of the weights; matTie asks that the matrix holds the weights' entries there too.
`K11ClaimTrue` READS THE WITNESS's MASK ROW TOO: it is shown nowhere. General in the thread: no head
stands here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareSStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E zeroE oneE)
open OnBytes.Slice (GE)
open OnBytes.Model (Reading WsClaim)
open OnBytes.Road (Wm claimVal)
open VerifiableInference.Desc (Claim Wit)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K13.Law (lowBits)
open VerifiableInference.Desc.Sound (dataQ MgData seatTab CellsQ MsgT)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (SumCoins firstRun endRun)

/-- **What the kind asks of the thread's witness at the merge's member.** It is a definition: a
premise's form. Nothing is claimed of it, and nothing shows that it can be met. -/
structure K11Script {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP) (weights : W₀ → Weights)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ) : Prop where
  /-- under the slots that the sumcheck takes the segment's mask row holds the first run's coins. a:
  the head's own part in front; a9: the open segment's part behind -/
  maskTie : ∀ blk k s m E ds y cols s' a a9, ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    s.here = .head a → segAt? s' = some a9 → ∀ ds' i, i < 2 * P.lay.lk + 2 →
      (dataQ ((Dof m.st.input).N.group seg) a9
        (seatTab (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
          (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))).mask (a.F.next + i) =
        Reading.gl.val ((firstRun (coins k)).getD i zeroE)
  /-- at the entry that the ledger behind takes the index-mask message holds the one coin of the run
  "ends" -/
  indexTie : ∀ blk k s m E ds y cols s', ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    ∀ ds' l c' l', ledgerAt s' = some l → takeEntry l = some (c', l') →
      ((Dof m.st.input).rw13 (toP (T.seat k y.2 s').1, s')
        (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
          ⟨s'.out.indexMasks, c'⟩ = Reading.gl.val ((endRun (coins k)).headD zeroE)
  /-- the committed matrix holds the prover's weights' entries -/
  matTie : ∀ blk k s m E ds y cols s', ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    ∀ ds' (i : Fin nR) (C : ℕ), C < 2 ^ (Dof m.st.input).P13.lin.kCol →
      ((Dof m.st.input).rw13 (toP (T.seat k y.2 s').1, s')
        (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mat i
          (lowBits (Dof m.st.input).P13.lin.kCol C) =
        Reading.gl.val (eOfF ((weights m.st.input.w₀).entry i C))

/-- **The cells of which the claim's value is taken.** -/
def weightCells (nR : ℕ) (Wt : Weights) : Wm GE :=
  fun r k => if r < nR then Reading.gl.val (eOfF (Wt.entry r k)) else 0

/-- **The claim is true.** It is a definition: a premise's form. Nothing is claimed of it, and
nothing shows that it can be met. -/
def K11ClaimTrue {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP) (weights : W₀ → Weights)
    (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ) : Prop :=
  ∀ blk k s m E ds y cols s' a claim x0 b9, ThrS T Said b k s m E →
    T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk →
    s.here = .head a → a.claim = some claim → a.x = some x0 → segAt? s = some b9 → ∀ ds',
      Reading.gl.val (a.F.vp.getD x0.sV zeroE) - Reading.gl.val (a.F.mf.getD x0.sV zeroE) *
          (dataQ ((Dof m.st.input).N.group seg) b9
            (seatTab (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
              (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))).mask x0.sV =
        claimVal Reading.gl P.lay (weightCells nR (weights m.st.input.w₀)) claim

/-- The statement. Its end is the field ties of `K11SeatedS`, in that field's own words. Not proved
here; a lemma's statement, none of the library's goals. -/
def TiesOfScript : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb Pp Tok Xi' : Type) (rows cols nR : ℕ)
    (Xp : OnBytes.Model.Verify.Public)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (P : HeadMergeP) (weights : W₀ → Weights)
    (coins : Coins Bk → SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (toP : T.P → Pp) (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp) (seg : ℕ),
    K11Script (Xp := Xp) T Said b P weights coins toP toW Dof seg → P.lay.m0 ≤ nR →
    K11ClaimTrue (Xp := Xp) T Said b P weights toW Dof seg →
    ∀ blk k s m E ds y cols s' a claim x0 b9 a9, ThrS T Said b k s m E →
      T.Stepped blk k s m E ds y cols s' → T.bs[b]? = some blk → s.here = .head a →
      a.claim = some claim → a.x = some x0 → segAt? s = some b9 → segAt? s' = some a9 →
      ∀ ds', MergeTiesAt P (Dof m.st.input) seg (toP (T.seat k y.2 s').1) s' a claim x0 b9 a9
        (weights m.st.input.w₀) (coins k) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))

end ProofFile.Honest.K11
