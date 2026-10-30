--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ItemsEach.lean: the eight sub-protocols of the linear claim's shared rounds:
behind EACH of the eight, from the run up to that sub-protocol alone, ALL that the verifier's
statement claims holds of one family of honest words.

Johnson/Desc/K14/Honest/ChainHolds.lean shows it behind the eighth, from the whole run. Here each of
its eight parts is a theorem of its own, and its premise on the run is the run up to that part
(Johnson/Desc/K14/Honest/RunsTo.lean).

THESE THEOREMS SPEAK OF THE WHOLE STATEMENT, the sample rows of earlier sendings among it. So from
the third sub-protocol on they ask that what an EARLIER sending showed was honest. Whoever has only
the run and the claims that are open in front of a sub-protocol takes
Johnson/Desc/K14/Honest/ItemsHold.lean, where each claim asks of what is shown only what its own
sub-protocol shows.

All are said at the last family of words (words2): a function of what the prover holds, of the first
round's challenge and of public data (the parameters; the first state's numbers of messages and
groups). It agrees with the earlier families at every message that the earlier statements have.

Main names:
  Start8              Public8, and: AllMet holds at the first statement of the words in front. At
                      the shared chain's first state that holds of all words (first_kept); at a
                      first state that has messages it is a premise on what was sent and shown in
                      front of the eight
  OwnAnswers, OwnColumns   the two premises on the committed table (no committer is in Lean)
  ShownU, ShownO, ShownMu   what is shown at the two sendings and at "SPLIT" is the honest value
  words1_old, words2_old, fold1_of   the families of words agree at the older messages; o_u's table
                      holds the rows' fold
  Start8.kept1, …, kept4   at the words as they grow
  Start8.met0, …, met8   **AllMet behind each of the eight.** Asked beside Start8 and the run up to
                      there: from the second on, ShownU; from the third on, OwnAnswers; from the
                      fourth on, OwnColumns; from the fifth on, ShownO; at the eighth, ShownMu

What is not claimed. That a run is there: eight_return. That a decision accepts (from the format's
step: StepsBack.lean, StepsTwins.lean). That a committer's key and columns meet OwnAnswers and
OwnColumns. Nothing on the two proximity tests, on soundness or on hiding. This is not completeness
of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.ChainHolds
import Johnson.Desc.K14.Honest.RunsTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (held_old)
open Desc.K14.Law (locations genK uOf on4_of_seatedUB parK1_sent parU parO)

/-- **What stands in front of the eight**: the public half, and: all that the first statement claims
holds of the words in front. At the shared chain's first state that holds of all words. At a first
state that has messages it is a premise on what was sent and shown in front of the eight. -/
structure Start8 (P : P14) (sentU : Array OracleNotice) (layO : TreeLay) (d0 : St) (H : Inputs) :
    Prop where
  pub : Public8 P sentU layO d0
  met : Means.AllMet rdE d0.st H.w₀

/-! ## The premises on the committed table, and on what is shown -/

/-- Each answer of the key is its row's own. -/
def OwnAnswers (P : P14) (key : TableKey) (H : Inputs) : Prop :=
  ∀ x ∈ key.seeds.zipIdx, ∀ r < P.par.S.fold.index.rows,
    RowAnswer P.par.S.fold.index (x.1.z.map rdE.val) (rdE.val x.1.beta)
      (fun t => rdE.val (thetaE t)) x.2 (H.Rw r)
      (rdE.val (key.record.getD (r * P.par.S.fold.index.answers + x.2) zeroE))

/-- Each opened column holds the rows' own symbols. -/
def OwnColumns (P : P14) (V : View8) (H : Inputs) : Prop :=
  ∀ x ∈ locations P.par V.r4, ∀ col, V.cols.lookup x = some col →
    ∀ q < P.par.S.fold.index.rows,
      rdE.val (ofF (col.toArray.getD q 0)) = genK rdE P.par.S.fold x (H.Rw q)

/-- The first sending's OOD answers are the honest ones, at the state that the run has reached. -/
def ShownU (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8)
    (H : Inputs) : Prop :=
  V.r2b.vals = answersAt (parU P sentU) D.d1.st V.r2a H.w₀ (rowsU P d0 V.r1 H)

/-- The second sending's OOD answers are the honest ones, at the state that the run has reached. -/
def ShownO (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8)
    (H : Inputs) : Prop :=
  V.r5b.vals = answersAt (parO P) D.d4.st V.r5a (words1 P sentU d0 V.r1 H) (rowsO P d0 V.r1 H)

/-- The scalar shown is the honest one. -/
def ShownMu (P : P14) (d0 : St) (V : View8) (H : Inputs) : Prop :=
  V.r8.vals = [.e (Slice.ofE (muRun P d0 V.r1 V.r7 H))]

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {V : View8}
  {D : States8} {H : Inputs}

/-! ## The families of words agree at the older messages -/

/-- Behind the first sending the words in front stand at the older messages. -/
theorem words1_old (P : P14) (sentU : Array OracleNotice) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    (o : Nat) (ho : o < d0.st.oracles.size) (part : Part) (i : Nat) :
    H.w₀ o part i = words1 P sentU d0 r1 H o part i :=
  (held_old H.w₀ d0.st.oracles.size (parU P sentU) (rowsU P d0 r1 H) o part i
    (fun e => by omega)).symm

/-- Behind the second sending the words behind the first stand at the older messages. -/
theorem words2_old (P : P14) (sentU : Array OracleNotice) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    (o : Nat) (ho : o < d0.st.oracles.size + 2) (part : Part) (i : Nat) :
    words1 P sentU d0 r1 H o part i = words2 P sentU d0 r1 H o part i :=
  (held_old (words1 P sentU d0 r1 H) (d0.st.oracles.size + 2) (parO P) (rowsO P d0 r1 H) o part i
    (fun e => by omega)).symm

/-! ## At the words as they grow -/

/-- Behind "LIN point", at the words in front. -/
theorem Start8.kept1 (S : Start8 P sentU layO d0 H) (u : To1 P d0 V D) :
    Means.AllMet rdE D.d1.st H.w₀ :=
  linPoint_kept rdE P.par d0 D.d1 [V.r1] H.w₀ u.k1 S.met

/-- Behind the sending of o_u, at the words behind it. -/
theorem Start8.kept2 (S : Start8 P sentU layO d0 H) (u : To2 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) : Means.AllMet rdE D.d2.st (words1 P sentU d0 V.r1 H) := by
  have K := sendU_kept P "send o_u" (parU P sentU) none [] D.d1 D.d2 V.r2a V.r2b [] H.w₀
    (rowsU P d0 V.r1 H) (sendSays _) S.pub.planU u.fitsU (u.s2.decides P "send o_u" none [] []) hU
    (S.kept1 u.front).1 (S.kept1 u.front).2
  rw [(S.pub.at1 u.front).size] at K
  exact K

/-- o_u's table, read as the state notes it behind its sending, holds the rows' fold. -/
theorem fold1_of (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs)
    (l : Lin) (hl : l = locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1) :
    IsFold P.par.S.fold (wOf rdE P.par.S l) H.Rw (uOf l (words1 P sentU d0 r1 H)) := by
  subst hl
  have sU : (parU P sentU).sent = sentU := parK1_sent P 2 _ sentU
  exact isFold_held H.w₀ d0.st.oracles.size (parU P sentU) P.codes P.par.S (wRun P d0 r1) H.Rw
    H.cU H.cMask _ hP.lin (by rw [sU, hP.goesTwo]; omega)
    (shapeAt_of_get (parU P sentU) 0 ⟨P.par.S.fold.u, P.par.S.fold.leafClass⟩
      (by rw [sU]; exact withU_zero hP.goes)).1 rfl

/-- Behind "(rec_gamma)", at the words behind the first sending. -/
theorem Start8.kept3 (S : Start8 P sentU layO d0 H) (u : To3 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) :
    Means.AllMet rdE D.d3.st (words1 P sentU d0 V.r1 H) := by
  have A := S.pub.at2 u.front
  obtain ⟨hi, hP2⟩ := on4_of_seatedUB P.par D.d2 (A.stands S.pub.facts)
  exact laysRec_kept rdE P.par D.d2 D.d3 V.rs3 _ H.Rw u.k3 hi hP2
    (fold1_of S.pub.facts d0 V.r1 H _ A.loc) (by rw [A.carried.key]; exact hA) (S.kept2 u.front hU)

/-- Behind "LOC", at the words behind the first sending. -/
theorem Start8.kept4 (S : Start8 P sentU layO d0 H) (u : To4 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) (hC : OwnColumns P V H) :
    Means.AllMet rdE D.d4.st (words1 P sentU d0 V.r1 H) := by
  have A := S.pub.at3 u.front
  obtain ⟨hi, hP3⟩ := on4_of_seatedUB P.par D.d3 (A.stands S.pub.facts)
  exact loc_kept rdE P.par D.d3 D.d4 V.r4 V.cols _ H.Rw u.k4 hi hP3
    (fold1_of S.pub.facts d0 V.r1 H _ A.loc) (weights_size P.par D.d3 A.carried.psi) hC
    (S.kept3 u.front hU hA)

/-! ## At one family of words -/

/-- **In front of the eight** all that the statement claims holds of the last family of words. -/
theorem Start8.met0 (S : Start8 P sentU layO d0 H) (r1 : Fmt.RoundView) :
    Means.AllMet rdE d0.st (words2 P sentU d0 r1 H) :=
  Means.allMet_agree rdE S.met fun o ho part i =>
    (words1_old P sentU d0 r1 H o ho part i).trans (words2_old P sentU d0 r1 H o (by omega) part i)

/-- **Behind "LIN point"** all that the statement claims holds of the honest words. Nothing is asked
of the key or of what is shown. -/
theorem Start8.met1 (S : Start8 P sentU layO d0 H) (u : To1 P d0 V D) :
    Means.AllMet rdE D.d1.st (words2 P sentU d0 V.r1 H) :=
  Means.allMet_agree rdE (S.kept1 u) fun o ho part i => by
    rw [(S.pub.at1 u).size] at ho
    exact (words1_old P sentU d0 V.r1 H o ho part i).trans
      (words2_old P sentU d0 V.r1 H o (by omega) part i)

/-- **Behind the sending of o_u** all that the statement claims holds of the honest words, where the
OOD answers shown are the honest ones. Nothing is asked of the key. -/
theorem Start8.met2 (S : Start8 P sentU layO d0 H) (u : To2 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) : Means.AllMet rdE D.d2.st (words2 P sentU d0 V.r1 H) :=
  Means.allMet_agree rdE (S.kept2 u hU) fun o ho part i =>
    words2_old P sentU d0 V.r1 H o (by rw [(S.pub.at2 u).size] at ho; exact ho) part i

/-- **Behind "(rec_gamma)"** all that the statement claims holds of the honest words, where each
answer of the key is its row's own. -/
theorem Start8.met3 (S : Start8 P sentU layO d0 H) (u : To3 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) :
    Means.AllMet rdE D.d3.st (words2 P sentU d0 V.r1 H) :=
  Means.allMet_agree rdE (S.kept3 u hU hA) fun o ho part i =>
    words2_old P sentU d0 V.r1 H o (by rw [(S.pub.at3 u).size] at ho; exact ho) part i

/-- **Behind "LOC"** all that the statement claims holds of the honest words, where each opened
column holds the rows' own symbols. -/
theorem Start8.met4 (S : Start8 P sentU layO d0 H) (u : To4 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) (hC : OwnColumns P V H) :
    Means.AllMet rdE D.d4.st (words2 P sentU d0 V.r1 H) :=
  Means.allMet_agree rdE (S.kept4 u hU hA hC) fun o ho part i =>
    words2_old P sentU d0 V.r1 H o (by rw [(S.pub.at4 u).size] at ho; exact ho) part i

/-- **Behind the sending of o_omega and o_sp** all that the statement claims holds of the honest
words, where the OOD answers shown there are the honest ones too. -/
theorem Start8.met5 (S : Start8 P sentU layO d0 H) (u : To5 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) (hC : OwnColumns P V H)
    (hO : ShownO P sentU d0 V D H) : Means.AllMet rdE D.d5.st (words2 P sentU d0 V.r1 H) := by
  have K4 := S.kept4 u.front hU hA hC
  have K := sendOmega_kept P "send o_omega" (parO P) none [] D.d4 D.d5 V.r5a V.r5b []
    (words1 P sentU d0 V.r1 H) (rowsO P d0 V.r1 H) (sendSays _) S.pub.planO u.fitsO
    (u.s5.decides P "send o_omega" none [] []) hO K4.1 K4.2
  rw [(S.pub.at4 u.front).size] at K
  exact K

/-- **Behind the joinings** all that the statement claims holds of the honest words. -/
theorem Start8.met6 (S : Start8 P sentU layO d0 H) (u : To6 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) (hC : OwnColumns P V H)
    (hO : ShownO P sentU d0 V D H) : Means.AllMet rdE D.d6.st (words2 P sentU d0 V.r1 H) :=
  joins_kept rdE P.par D.d5 D.d6 V.rs6 _ u.k6 (S.met5 u.front hU hA hC hO)

/-- **Behind "LIN zeta"** all that the statement claims holds of the honest words. -/
theorem Start8.met7 (S : Start8 P sentU layO d0 H) (u : To7 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) (hC : OwnColumns P V H)
    (hO : ShownO P sentU d0 V D H) : Means.AllMet rdE D.d7.st (words2 P sentU d0 V.r1 H) :=
  linZeta_kept rdE D.d6 D.d7 V.r7 _ u.k7 (S.met6 u.front hU hA hC hO)

/-- **Behind "SPLIT"** all that the statement claims holds of the honest words, where the scalar
shown is the honest one too. -/
theorem Start8.met8 (S : Start8 P sentU layO d0 H) (u : To8 P sentU d0 V D)
    (hU : ShownU P sentU d0 V D H) (hA : OwnAnswers P d0.loc.key H) (hC : OwnColumns P V H)
    (hO : ShownO P sentU d0 V D H) (hM : ShownMu P d0 V H) :
    Means.AllMet rdE D.d8.st (words2 P sentU d0 V.r1 H) :=
  returned_holds P sentU layO S.pub.facts d0 V.r1 V.r2a V.r2b V.r4 V.r5a V.r5b V.r7 V.r8 V.cols
    V.rs3 V.rs6 D.d1 D.d2 D.d3 D.d4 D.d5 D.d6 D.d7 D.d8 D.x2 D.x5 D.ids2 D.ids5
    (S.pub.returned u) H S.pub.planU S.pub.planO u.front.front.front.front.front.front.fitsU
    u.front.front.front.fitsO S.met hA hC hU hO hM

end Desc.K14.Honest

#print axioms Desc.K14.Honest.words1_old
#print axioms Desc.K14.Honest.words2_old
#print axioms Desc.K14.Honest.Start8.kept1
#print axioms Desc.K14.Honest.Start8.kept2
#print axioms Desc.K14.Honest.fold1_of
#print axioms Desc.K14.Honest.Start8.kept3
#print axioms Desc.K14.Honest.Start8.kept4
#print axioms Desc.K14.Honest.Start8.met0
#print axioms Desc.K14.Honest.Start8.met1
#print axioms Desc.K14.Honest.Start8.met2
#print axioms Desc.K14.Honest.Start8.met3
#print axioms Desc.K14.Honest.Start8.met4
#print axioms Desc.K14.Honest.Start8.met5
#print axioms Desc.K14.Honest.Start8.met6
#print axioms Desc.K14.Honest.Start8.met7
#print axioms Desc.K14.Honest.Start8.met8
