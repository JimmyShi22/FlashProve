-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OTie.lean: the tie of the words at the two members of the test on
G_omega, member by member: on a table of a member, the honest words at the thread's holdings (`words2`, `holds2`,
Honest/K14/) are the words that the job's own rows make at the lent coins (`wordsAt`, `plainMany`). General in the
parameters Q, the place p, the door and the readers.

  `AO`             the job at a place, as a ManyJob
  `ellOmegaB`      the code of o_omega's main rows has the message length that its logarithm says
  `tie_omega`, `tie_sp`   the two members: o_omega, table 2; o_sp, table 3

By what. `wordsAt_member` (K12/WordsOfMember.lean), `cuts_atOmega` (K12/CutOfBookAt.lean), `rowsO_read`
(Honest/K14/SendingsRows.lean), `msg_eq`, `first_read`, `askR` (TieAtMembers.lean).

The premises, each a public line. hQf, hE, hb, c5, n5: the sendings fit, their lengths, the book's cuts, the book's
row at the sending. hP, hSh: the plan and the shapes of the sendings. hpt, hf, hy, hys, hcd: what a state on entry
must be like: the point's length, the layout's places, the member's shape, the codes: a caller's, at a stand.

Limits. A tie of the words to the lent coins: no fold is called here. At the job's rows at the members alone: off
the members nothing is said. NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, on soundness or on what is
hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TieAtMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle)
open OnBytes.Slice (rdE ofE)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (P14 St first withU)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light

/-- The code of o_omega's main rows has the message length that its logarithm says. -/
def ellOmegaB (A : SendPub) : Bool :=
  ((jobOmega A).Q.codes.base.getD (shapeAt (jobOmega A) 0).code default).ell ==
    2 ^ ((jobOmega A).Q.codes.base.getD (shapeAt (jobOmega A) 0).code default).logEll

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type} (Q : P14) (p : P12)
  (door : Common W₀ Rc TableKey → Front X₀ → VerifiableInference.Desc.K12.T12)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)

/-- The job at G_omega, as a ManyJob. -/
abbrev AO : ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobAtOmega ⟨Q, 0⟩ p door (fun c => wts c.w₀) (fun c => rnd c.rc) none

/-- **The tie at o_omega.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_omega (hQf : sendingsFit Q = true) (hE : ellOmegaB ⟨Q, 0⟩ = true)
    (hb : bookCutsOmega Bk ⟨Q, 0⟩ p = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨Q, 0⟩) = true)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e)
    {layO}
    (hP : Plan2 Q (sentOf Q.S) layO) (hSh : SendShapes Q)
    (k : Coins Bk) (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.place, 1⟩
      (restPart (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = Q.par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 2 = some 0) (y : Oracle)
    (hy : S.oracles[2]? = some y) (hys : y.shape = shapeAt (jobOmega ⟨Q, 0⟩) 0)
    (hcd : S.codes = Q.codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 2 pt) :
    words2 Q (sentOf Q.S) (first Q.codes w.key) (firstRv l)
        (holds2 Q wts rnd k w) 2 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (AO (X₀ := X₀) Q p door wts rnd) w fr
              (carriedCoins (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2))) 2 pt i := by
  have hU := hP.facts.goes
  unfold ellOmegaB at hE
  rw [beq_iff_eq] at hE
  obtain ⟨ownO, cO⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c5)
  have nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e := by
    rw [AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 5, 0⟩]
    exact n5
  obtain ⟨sc0, -⟩ := cuts_atOmega Bk (Bk.rowsOf 1) (k.look 1) ⟨Q, 0⟩ p _ _ _ none ownO cO c hlp hb
  have hw : (Desc.K14.withOmega Q.S).size = 2 ∧
      (Desc.K14.withOmega Q.S)[0]? =
        some ⟨Q.S.omega, Q.S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega Q.S)[1]? =
        some ⟨Q.S.sharedSplit, Q.S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.facts.two
  have sOs : (jobOmega ⟨Q, 0⟩).Q.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0O : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 0
      ⟨Q.par.S.omega, Q.par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hs1O : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape =
      Q.par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 1
      ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sOs]; exact hw.2.2)).1
  have hnoSp : Q.par.S.sharedSplit.mainRows = 0 := sp_noMain hP
  have hk0 : 0 < (jobOmega ⟨Q, 0⟩).Q.sent.size := by
    rw [sOs, hw.1]
    decide
  have hv : vecAt (jobOmega ⟨Q, 0⟩) 0 (askR Q wts rnd) none w fr =
      (jobOmega ⟨Q, 0⟩).data (⟨askR Q wts rnd w, l, ()⟩ : State Ask Unit) 0 :=
    congrFun (data_same (jobOmega_readsBelow ⟨Q, 0⟩) _ _ _ hfr) 0
  have wM := wordsAt_member Q hQf (jobOmega ⟨Q, 0⟩) (Or.inr ⟨rfl, rfl⟩) 0 hk0 _
    rfl ⟨sendPlace 5, 0⟩ _ (askR Q wts rnd) none w fr (⟨askR Q wts rnd w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownO).toArray (AO (X₀ := X₀) Q p door wts rnd) 0 rfl
    (carriedCoins (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2)) sc0 S L 2 hf y hy hys
    (by rw [hcd]; rfl) (fun _ => hE)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows
      rw [hs0O, hSh.omega.noMask]
      exact Nat.lt_irrefl 0)) pt i hi
  have mO := fun n => msg_eq k (jobOmega ⟨Q, 0⟩) (sendPlace 5) n ownO cO nO
  have rO := rowsO_read Q (first Q.codes w.key) (firstRv l)
    (holds2 Q wts rnd k w) (askR Q wts rnd w) l (coinsE ownO).toArray
    (by rw [sOs, hw.1]) hs0O hs1O hSh.omega hnoSp (first_read _ l hl) hpt (fun _ _ => rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 0) = _
      rw [mO 0]
      rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 1) = _
      rw [mO 1]
      rfl) 0 hk0 pt i
  refine Eq.trans ?_ wM.symm
  rw [rO]
  show (if 0 + 2 ≤ 2 ∧ 2 < 0 + 2 + (parO Q).sent.size then _ else _) = _
  rw [if_pos ⟨by omega, by
    have e' : (parO Q).sent.size = 2 := by
      rw [Desc.K14.Law.parK1_sent]
      exact hw.1
    rw [e']
    decide⟩]
  rfl

/-- **The tie at o_sp.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_sp (hQf : sendingsFit Q = true) (hE : ellsB ⟨Q, 0⟩ = true)
    (hb : bookCutsOmega Bk ⟨Q, 0⟩ p = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨Q, 0⟩) = true)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e)
    {layO}
    (hP : Plan2 Q (sentOf Q.S) layO) (hSh : SendShapes Q)
    (k : Coins Bk) (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.place, 1⟩
      (restPart (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = Q.par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 3 = some 1) (y : Oracle)
    (hy : S.oracles[3]? = some y) (hys : y.shape = shapeAt (jobOmega ⟨Q, 0⟩) 1)
    (hcd : S.codes = Q.codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 3 pt) :
    words2 Q (sentOf Q.S) (first Q.codes w.key) (firstRv l)
        (holds2 Q wts rnd k w) 3 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (AO (X₀ := X₀) Q p door wts rnd) w fr
              (carriedCoins (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2))) 3 pt i := by
  have hU := hP.facts.goes
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨-, zO1⟩ := hE
  obtain ⟨ownO, cO⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c5)
  have nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e := by
    rw [AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 5, 0⟩]
    exact n5
  obtain ⟨-, sc1⟩ := cuts_atOmega Bk (Bk.rowsOf 1) (k.look 1) ⟨Q, 0⟩ p _ _ _ none ownO cO c hlp hb
  have hw : (Desc.K14.withOmega Q.S).size = 2 ∧
      (Desc.K14.withOmega Q.S)[0]? =
        some ⟨Q.S.omega, Q.S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega Q.S)[1]? =
        some ⟨Q.S.sharedSplit, Q.S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.facts.two
  have sOs : (jobOmega ⟨Q, 0⟩).Q.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0O : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 0
      ⟨Q.par.S.omega, Q.par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hs1O : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape =
      Q.par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 1
      ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sOs]; exact hw.2.2)).1
  have hnoSp : Q.par.S.sharedSplit.mainRows = 0 := sp_noMain hP
  have hk1 : 1 < (jobOmega ⟨Q, 0⟩).Q.sent.size := by
    rw [sOs, hw.1]
    decide
  have hv : vecAt (jobOmega ⟨Q, 0⟩) 1 (askR Q wts rnd) none w fr =
      (jobOmega ⟨Q, 0⟩).data (⟨askR Q wts rnd w, l, ()⟩ : State Ask Unit) 1 :=
    congrFun (data_same (jobOmega_readsBelow ⟨Q, 0⟩) _ _ _ hfr) 1
  have wM := wordsAt_member Q hQf (jobOmega ⟨Q, 0⟩) (Or.inr ⟨rfl, rfl⟩) 1 hk1 _
    rfl ⟨sendPlace 5, 0⟩ _ (askR Q wts rnd) none w fr (⟨askR Q wts rnd w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownO).toArray (AO (X₀ := X₀) Q p door wts rnd) 1 rfl
    (carriedCoins (AO (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2)) sc1 S L 3 hf y hy hys
    (by rw [hcd]; rfl)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows
      rw [hs1O, hnoSp]
      exact Nat.lt_irrefl 0)) (fun _ => zO1) pt i hi
  have mO := fun n => msg_eq k (jobOmega ⟨Q, 0⟩) (sendPlace 5) n ownO cO nO
  have rO := rowsO_read Q (first Q.codes w.key) (firstRv l)
    (holds2 Q wts rnd k w) (askR Q wts rnd w) l (coinsE ownO).toArray
    (by rw [sOs, hw.1]) hs0O hs1O hSh.omega hnoSp (first_read _ l hl) hpt (fun _ _ => rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 0) = _
      rw [mO 0]
      rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 1) = _
      rw [mO 1]
      rfl) 1 hk1 pt i
  refine Eq.trans ?_ wM.symm
  rw [rO]
  show (if 0 + 2 ≤ 3 ∧ 3 < 0 + 2 + (parO Q).sent.size then _ else _) = _
  rw [if_pos ⟨by omega, by
    have e' : (parO Q).sent.size = 2 := by
      rw [Desc.K14.Law.parK1_sent]
      exact hw.1
    rw [e']
    decide⟩]
  rfl

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.ellOmegaB
#print axioms ProofFile.Honest.K12.AtFile.tie_omega
#print axioms ProofFile.Honest.K12.AtFile.tie_sp
