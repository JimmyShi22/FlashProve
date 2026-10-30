-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Holds2.lean: kind K14: THE LETTER holds OF THE SHARED CHAIN's
THREAD (Honest/K14/Thread2.lean: Others.holds) LAID: what an honest prover holds in front of the
eight sub-protocols, as a function of a run's coins and the input. Where the letter holds is holds2,
the premise SpOneCoin (Honest/K14/MuPaid.lean) follows under Plan2 from a premise on the book's
entries (he).

Main names:
  coinAt, coinsOfMsg  the reader by which a sentence names a coin: the coin number i of the
                      extension field among the shared chain's coins at an address; a message's
                      coins from its first on. BEYOND THE COUNT coinAt IS 0: it is no move of a
                      prover; spOneCoin_of_book shows first that the one number it names is below
                      the count; holds2 reads coinAt at every number, and no premise of holds2_rows
                      or exchange8_book bounds these numbers
  holds2              **the prover's holdings**: the rows whole, as the two sendings' halves are
                      handed them (Honest/K14/Parts.lean: rowsOf); each message's random values as
                      its sender's part reads them off its own coins
                      (Honest/K14/SendingsTables.lean: readCoins, readFresh;
                      Honest/K14/Sendings.lean: offsetOf); no word in front. FOR THE FIRST MASK WHAT
                      THE PROVER HOLDS IS DEFINED AS THE CODED TABLE, READ: no text at the field's
                      level of a fold's fresh table stands beside it. ITS TOTAL MOVES: the shapes of
                      the first sending's two messages are read with a default (where the sending
                      has no such message: the default shape); where the proximity test on G_u has
                      no first stage the first mask is read as a plain message's coins are; the
                      chain's number is 1 and "LIN point" is the chain's round number 0, both typed
  holds2_rows         at the places that hold the matrix these rows are the rows that the part at
                      "SPLIT" is handed
  spOneCoin_of_book   **SpOneCoin**, under Plan2 and where the letter holds is holds2, from: every
                      entry of the book by which the part at "SPLIT" spends coins (its field once
                      is true: spent, not carried) names the second sending's part as the owner and
                      starts at o_sp's first coin (Honest/K14/SplitCoin.lean: split_lent)
  exchange8_book      «Exchange» at "SPLIT", all joined, under all the premises listed below

What is assumed, as premises: beside MuPaid.lean's (AtSplit; the public data has the plan's shape
and the round numbers 0 and 6; no two messages have one tenant, hN): Plan2; the letter holds is
holds2 (hO); the book's entries (he): public data. That there is such an entry is not asked: at a
book with none he holds for nothing. That o_sp has no main row and has a mask row, and where the
member number 8 stands, come from Plan2.

WITH holds := holds2 THE COMMITTER's TWO LAWS (hAns, hTab: Exchange2.lean) BECOME SENTENCES ON
rowsOf, ITS UNSETTLED PLACES INCLUDED: hTab sets each column's word beside the code symbol of a row,
which reads every place of the row's message; rowsOf lays 0 from the matrix's last entry to the
pads: a choice of this kind's own files, compared with no description of the format, and tied to a
committer's table by no statement here. If a committer lays anything else there, hTab cannot be met
at these holdings: a remark, which no theorem bears.

What is not claimed. THAT THE TWO SENDINGS' PARTS SEND WHAT holds2 SAYS: the premises ShowsU and
ShowsO are not shown here (two files above this one show them, each from premises of its own:
Honest/K14/SendingsShows.lean, Honest/K14/SendingsViaShows.lean). That a book has such an entry.
How the coins are distributed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.MuPaid
import Johnson.Desc.ProofFile.Honest.K14.SplitCoin
import Johnson.Desc.ProofFile.Honest.K14.PartsCoin
import Johnson.Desc.ProofFile.Honest.K14.PaidAt
import Johnson.Desc.ProofFile.Honest.K14.SendingsTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open Desc.K14 (P14)
open Desc.K14.Honest

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **The coin number i of the extension field among the shared chain's coins at an address**, as
the program's element. Beyond the count: 0. This is no move of a prover: it is the reader by which a
sentence names a coin. spOneCoin_of_book shows, for the one number that it names, that the number is
below the count; holds2 reads coinAt at every number, so beyond the count its random values are 0.
The chain's number is the typed 1 (k.look 1). -/
def coinAt (k : Coins Bk) (a : Addr) (i : Nat) : E :=
  if h : i < (k.look 1 a).1.e then E.ofTriple (Slice.ofE ((k.look 1 a).2.e ⟨i, h⟩)) else zeroE

/-- The coins of the message number n of a sending at a place, from the message's first on. -/
def coinsOfMsg (k : Coins Bk) (J : SendJob) (pl : VerifiableInference.Desc.Place) (n i : Nat) : E :=
  coinAt k ⟨pl, 0⟩ (offsetOf J.Q.codes J.Q.sent J.sort n + i)

/-- **WHAT AN HONEST PROVER HOLDS IN FRONT OF THE EIGHT, of a run's coins and the input**: the rows
whole, as the two sendings' halves are handed them; each message's random values as its sender's
part reads them off its own coins. No word in front (w₀ is 0 everywhere). Total moves: the shapes of
"send o_u"'s messages number 0 and 1 are read with getD: where the sending has no such message, the
default shape is read. Where the proximity test on G_u has no first stage (testU is empty) the first
mask's values are read by readCoins in place of readFresh. A coin beyond the count is read as 0
(coinAt). The chain's number 1 (in coinAt) and "LIN point"'s round number 0 (jobU ⟨Q, 0⟩,
jobOmega ⟨Q, 0⟩) are typed. -/
noncomputable def holds2 (Q : P14) (weights : W₀ → Weights) (rand : Rc → TableRand) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) : Inputs where
  w₀ := fun _ _ _ => 0
  Rw := fun r j => rdE.val (rowsOf Q.S (weights w.w₀) (rand w.rc) r j)
  cU := readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape
    (coinsOfMsg k (jobU ⟨Q, 0⟩) (sendPlace 2) 0)
  cMask :=
    match Q.S.testU.head? with
    | some s => readFresh Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
        (coinsOfMsg k (jobU ⟨Q, 0⟩) (sendPlace 2) 1) s.k s.h
    | none => readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
        (coinsOfMsg k (jobU ⟨Q, 0⟩) (sendPlace 2) 1)
  cOmega := readCoins Q.codes Q.S.omega (coinsOfMsg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) 0)
  cSp := readCoins Q.codes Q.S.sharedSplit (coinsOfMsg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) 1)

/-- At the places that hold the matrix the rows held are the rows that the part at "SPLIT" is
handed. -/
theorem holds2_rows (Q : P14) (weights : W₀ → Weights) (rand : Rc → TableRand) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (r j : Nat) (hj : j < Q.S.matrixRows * 2 ^ Q.S.kLo) :
    (holds2 Q weights rand k w).Rw r j = rdE.val (entriesOf Q.S (weights w.w₀) r j) := by
  show rdE.val (rowsOf Q.S (weights w.w₀) (rand w.rc) r j) = _
  unfold rowsOf
  rw [if_pos hj]

/-- **SpOneCoin, under Plan2, where the letter holds is holds2 (hO), from the book's entries (he).**
he: every entry of the book whose spender is the part at "SPLIT" and whose field once is true names
the second sending's part as the owner, and starts at o_sp's first coin. That o_sp has no main row
and has a mask row, and where the member stands, come from the plan. -/
theorem spOneCoin_of_book (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (A : Data) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (hO : O.holds = holds2 Q weights rand)
    (he : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨Q, 0⟩).Q.codes
        (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1⟩) :
    SpOneCoin Q sentU O Cl A weights := by
  obtain ⟨B⟩ := hQ.eight
  have hsh := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.par.S).1 hQ.facts.lin
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits Q.par.S.sharedSplit
      Q.par.S.sharedMaskCode := by
    rcases hsh.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hQ.facts.two] at e
      cases e
    · exact e
  have hno : Q.S.sharedSplit.mainRows = 0 := hSp.1
  have hone : Q.S.sharedSplit.maskRows ≠ 0 := hSp.2.1
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  intro k w blk c hblk hc
  have hpl : blk.place = place 8 :=
    (F.at8 hblk).place.trans (places4 Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made).2.2.2
  rw [hpl] at hc
  obtain ⟨e, hl, -, -, hcut⟩ := split_lent A weights hc
  have hm : e ∈ (Bk.ahead.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once) := by
    rw [hl]
    exact List.mem_cons_self ..
  obtain ⟨hm1, honce⟩ := List.mem_filter.1 hm
  obtain ⟨hm2, hsp⟩ := List.mem_filter.1 hm1
  obtain ⟨ho, hst⟩ := he e hm2 (by simpa using hsp) honce
  rw [ho, hst] at hcut
  rw [coin_there, hO]
  unfold Cs.cut at hcut
  split at hcut
  · rename_i hle
    rw [← Option.some.inj hcut]
    have hidx : Q.S.sharedSplit.mainRows * (Q.codes.base.getD Q.S.sharedSplit.code default).r +
        (if Q.S.sharedSplit.maskRows == 0 then Q.S.sharedSplit.answers else 0) +
        0 / 2 ^ ceilLog2 Q.S.sharedSplit.maskRows * Q.S.sharedSplit.maskRows +
        0 % 2 ^ ceilLog2 Q.S.sharedSplit.maskRows = 0 := by
      rw [hno]
      simp [hone]
    show rdE.val (coinsOfMsg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) 1
      (Q.S.sharedSplit.mainRows * (Q.codes.base.getD Q.S.sharedSplit.code default).r +
        (if Q.S.sharedSplit.maskRows == 0 then Q.S.sharedSplit.answers else 0) +
        0 / 2 ^ ceilLog2 Q.S.sharedSplit.maskRows * Q.S.sharedSplit.maskRows +
        0 % 2 ^ ceilLog2 Q.S.sharedSplit.maskRows)) = _
    rw [hidx]
    have hle2 : offsetOf (jobOmega ⟨Q, 0⟩).Q.codes (jobOmega ⟨Q, 0⟩).Q.sent
        (jobOmega ⟨Q, 0⟩).sort 1 + 1 ≤ (k.look 1 ⟨sendPlace 5, 0⟩).1.e := hle.2
    unfold coinsOfMsg coinAt
    rw [dif_pos (by omega)]
    rfl
  · cases hcut

/-- **«Exchange» at "SPLIT", at the prover's holdings as laid here** (hO), under Plan2, AtSplit at
the member 8, public data of the plan's shape with the round numbers 0 and 6, and where no two
messages have one tenant (hN): no premise on what is shown, and none on a coin but the book's
entries (he). -/
theorem exchange8_book (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (A : Data) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (hAt : AtSplit (letters2 Q sentU O Cl).thread 8 A weights)
    (hS : A.S = Q.par.S) (h0 : A.atPoint = 0) (h6 : A.atZeta = 6)
    (hO : O.holds = holds2 Q weights rand)
    (he : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨Q, 0⟩).Q.codes
        (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1⟩) :
    Exchange (letters2 Q sentU O Cl).thread 8 :=
  exchange8_of hQ O Cl hN A weights hAt hS h0 h6
    (fun k w r j hj => by
      rw [hO, hS]
      exact holds2_rows Q weights rand k w r j hj)
    (spOneCoin_of_book hQ O Cl A weights rand hO he)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.holds2_rows
#print axioms ProofFile.Honest.K14.spOneCoin_of_book
#print axioms ProofFile.Honest.K14.exchange8_book
