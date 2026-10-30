-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/TieAtMembers.lean: the tie of the words at the two members of the
test on G_u, member by member: on a table of a member, the honest words at the thread's holdings
(`words2`, `holds2`, Honest/K14/) are the words that the job's own rows make at the lent coins (`wordsAt`,
`plainMany`). General in the parameters Q, the place p, the door and the readers.

  `coin_eq`, `msg_eq`   `coinsOfMsg` is what the cut hands: `holds2` reads the senders' own coins
  `AM`, `askR`     the job at a place, and the reader of the input
  `cuts_both`    where a sending's row covers what it takes, and holds no more, the cut takes all
  `first_read`   the first challenge, read off a list that is not empty
  `tie_U`, `tie_O`   the two members: o_u, table 0; o_sp, table 3

By what. `wordsAt_member`, `cuts_atU` (K12/TieAtRun.lean, K12/CutOfBookAt.lean), `rowsU_read`, `rowsO_read`
(Honest/K14/SendingsRows.lean).

The premises, each a public line. hQf, hE, hb, hfit, c2, c5, n2, n5: the sendings fit, their lengths, the
book's cuts, the fresh table, the book's rows at the two sendings. hP, hSh: the plan and the shapes of
the sendings. hpt, hf, hy, hys, hcd: what a state on entry must be like: the point's length, the layout's
places, the member's shape, the codes: a caller's, at a stand.

Limits. A tie of the words to the lent coins: no fold is called here. At the job's rows at the members
alone: off the members nothing is said. NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesSentBeforeTestAtU
import Johnson.Desc.ProofFile.Honest.K12.TieAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle)
open OnBytes.Slice (rdE ofE)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (P14 St first withU)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light

/-- The book's coin at a number is what the cut from 0 hands, where the cut takes all. -/
theorem coin_eq {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr) (n : Due) (own : Cs n)
    (h : (k.look 1 a).2.cut ⟨0, 0⟩ n = some own) (hc : (k.look 1 a).1.e = n.e) (i : ℕ) :
    coinAt k a i = (coinsE own).toArray.getD i zeroE := by
  have hs : (coinsE own).length = n.e := by
    unfold coinsE
    exact List.length_ofFn
  unfold coinAt
  by_cases hi : i < (k.look 1 a).1.e
  · rw [dif_pos hi]
    have hi' : i < n.e := hc ▸ hi
    have hx := ProofFile.Honest.K12.Light.cut_at _ _ _ _ h i hi'
    simp only [stretchOf, dif_pos hi', Nat.zero_add] at hx
    rw [dif_pos (show i < (k.look 1 a).1.e from hi)] at hx
    rw [Array.getD_eq_getD_getElem?]
    simp only [List.getElem?_toArray, coinsE, List.getElem?_ofFn, dif_pos hi', Option.getD_some]
    rw [hx]
  · rw [dif_neg hi]
    have hi' : ¬ i < (coinsE own).length := by
      rw [hs, ← hc]
      exact hi
    rw [Array.getD_eq_getD_getElem?]
    simp only [List.getElem?_toArray, List.getElem?_eq_none (Nat.le_of_not_lt hi'), Option.getD_none]

theorem msg_eq {Bk : ProverCoinCounts} (k : Coins Bk) (J : SendJob) (pl : VerifiableInference.Desc.Place) (n : ℕ)
    (own : Cs (sendingPart J).takes)
    (h : (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart J).takes = some own)
    (hc : (k.look 1 ⟨pl, 0⟩).1.e = (sendingPart J).takes.e) :
    coinsOfMsg k J pl n = msgCoins J (coinsE own).toArray n :=
  funext fun i => coin_eq k ⟨pl, 0⟩ _ own h hc _

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type} (Q : P14) (p : P12)
  (door : Common W₀ Rc TableKey → Front X₀ → VerifiableInference.Desc.K12.T12)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)

/-- The job at G_u, as a ManyJob. -/
abbrev AM : ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobAtU ⟨Q, 0⟩ p door (fun c => wts c.w₀) (fun c => rnd c.rc) none

/-- The reader of the input. -/
abbrev askR : Common W₀ Rc TableKey → Ask :=
  askOf ⟨Q, 0⟩ (fun c => wts c.w₀) (fun c => rnd c.rc)

/-- Where a sending's row holds just what it takes, the cut returns, and takes all. -/
theorem cuts_both (k : Coins Bk)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨Q, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨Q, 0⟩) = true)
    (n2 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 2, 0⟩).e = (sendingPart (jobU ⟨Q, 0⟩)).takes.e)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e) :
    ∃ (ownU : Cs (sendingPart (jobU ⟨Q, 0⟩)).takes) (ownO : Cs (sendingPart (jobOmega ⟨Q, 0⟩)).takes),
      (k.look 1 ⟨sendPlace 2, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobU ⟨Q, 0⟩)).takes = some ownU ∧
      (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega ⟨Q, 0⟩)).takes = some ownO ∧
      (k.look 1 ⟨sendPlace 2, 0⟩).1.e = (sendingPart (jobU ⟨Q, 0⟩)).takes.e ∧
      (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e := by
  obtain ⟨ownU, hU⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c2)
  obtain ⟨ownO, hO⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c5)
  have dU : (k.look 1 ⟨sendPlace 2, 0⟩).1 = dueAt (Bk.rowsOf 1) ⟨sendPlace 2, 0⟩ :=
    AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 2, 0⟩
  have dO : (k.look 1 ⟨sendPlace 5, 0⟩).1 = dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩ :=
    AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 5, 0⟩
  exact ⟨ownU, ownO, hU, hO, by rw [dU]; exact n2, by rw [dO]; exact n5⟩

/-- The first challenge read off a list that is not empty. -/
theorem first_read (a : Ask) (l : List Fmt.Drawn) (hl : l ≠ []) :
    elems (heardFrom ({ input := a, heard := l, own := () } : State Ask Unit) 0 1) =
      Desc.K14.drawn (firstRv l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons d t => exact elems_one d

/-- **The tie at o_u.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_U (hQf : sendingsFit Q = true) (hE : ellsB ⟨Q, 0⟩ = true)
    (hb : bookCutsU Bk ⟨Q, 0⟩ p = true) (hfit : freshFitsU ⟨Q, 0⟩ p = true)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨Q, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨Q, 0⟩) = true)
    (n2 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 2, 0⟩).e = (sendingPart (jobU ⟨Q, 0⟩)).takes.e)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e)
    {layO}
    (hP : Plan2 Q (sentOf Q.S) layO) (hSh : SendShapes Q)
    (k : Coins Bk) (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.place, 1⟩
      (restPart (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = Q.par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 0 = some 0) (y : Oracle)
    (hy : S.oracles[0]? = some y) (hys : y.shape = shapeAt (jobU ⟨Q, 0⟩) 0)
    (hcd : S.codes = Q.codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 0 pt) :
    words2 Q (sentOf Q.S) (first Q.codes w.key) (firstRv l)
        (holds2 Q wts rnd k w) 0 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (AM (X₀ := X₀) Q p door wts rnd) w fr
              (carriedCoins (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2))) 0 pt i := by
  have hU := hP.facts.goes
  have h2 : (sentOf Q.S).size = 2 := hP.facts.goesTwo
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨lU0, -⟩ := hE
  obtain ⟨ownU, ownO, cU, cO, nU, -⟩ := cuts_both Q k c2 c5 n2 n5
  obtain ⟨sc0, -, -⟩ := cuts_atU Bk (Bk.rowsOf 1) (k.look 1) ⟨Q, 0⟩ p _
    _ _ none ownU cU ownO cO c hlp hb hfit
  have eQ := jobU_par (Q := Q) hU 0
  have sUs : (jobU ⟨Q, 0⟩).Q.sent = sentOf Q.S := by
    rw [eQ]
    exact Desc.K14.Law.parK1_sent _ 2 _ _
  have hs0U : ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.fold.u := by
    rw [eQ]
    exact (shapeAt_of_get (parU Q (sentOf Q.S)) 0
      ⟨Q.par.S.fold.u, Q.par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hU)).1
  have hk0 : 0 < (jobU ⟨Q, 0⟩).Q.sent.size := by
    rw [sUs, h2]
    decide
  have hv : vecAt (jobU ⟨Q, 0⟩) 0 (askR Q wts rnd) none w fr =
      (jobU ⟨Q, 0⟩).data (⟨askR Q wts rnd w, l, ()⟩ : State Ask Unit) 0 :=
    congrFun (data_same (jobU_readsBelow ⟨Q, 0⟩) _ _ _ hfr) 0
  have wM := wordsAt_member Q hQf (jobU ⟨Q, 0⟩) (Or.inl ⟨rfl, rfl⟩) 0 hk0 _ rfl
    ⟨sendPlace 2, 0⟩ _ (askR Q wts rnd) none w fr (⟨askR Q wts rnd w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownU).toArray (AM (X₀ := X₀) Q p door wts rnd) 0 rfl
    (carriedCoins (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2)) sc0 S L 0 hf y hy hys
    (by rw [hcd, eQ]; rfl) (fun _ => lU0)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows
      rw [hs0U, hSh.u.noMask]
      exact Nat.lt_irrefl 0)) pt i hi
  have mU := fun n => msg_eq k (jobU ⟨Q, 0⟩) (sendPlace 2) n ownU cU nU
  have rU := rowsU_read Q (first Q.codes w.key) (firstRv l)
    (holds2 Q wts rnd k w) (askR Q wts rnd w) l (coinsE ownU).toArray
    (by rw [sUs, h2]) hs0U hSh.u hSh.mask (first_read _ l hl) hpt (fun _ _ => rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 0) = _
      rw [mU 0, hs0U])
    (by
      show (match Q.S.testU.head? with
        | some s => readFresh _ _ (coinsOfMsg k _ _ 1) s.k s.h
        | none => readCoins _ _ (coinsOfMsg k _ _ 1)) = _
      rw [mU 1]
      rfl) 0 hk0 pt i
  refine Eq.trans ?_ wM.symm
  rw [rU, eQ]
  show (if 0 ≤ 0 ∧ 0 < 0 + (parU Q (sentOf Q.S)).sent.size then _ else _) = _
  rw [if_pos ⟨Nat.le_refl _, by
    rw [Desc.K14.Law.parK1_sent, h2]
    decide⟩]
  rfl

/-- **The tie at o_sp.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_O (hQf : sendingsFit Q = true) (hE : ellsB ⟨Q, 0⟩ = true)
    (hb : bookCutsU Bk ⟨Q, 0⟩ p = true) (hfit : freshFitsU ⟨Q, 0⟩ p = true)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨Q, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨Q, 0⟩) = true)
    (n2 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 2, 0⟩).e = (sendingPart (jobU ⟨Q, 0⟩)).takes.e)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e)
    {layO}
    (hP : Plan2 Q (sentOf Q.S) layO) (hSh : SendShapes Q)
    (k : Coins Bk) (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.place, 1⟩
      (restPart (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = Q.par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 3 = some 1) (y : Oracle)
    (hy : S.oracles[3]? = some y) (hys : y.shape = shapeAt (jobOmega ⟨Q, 0⟩) 1)
    (hcd : S.codes = Q.codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 3 pt) :
    words2 Q (sentOf Q.S) (first Q.codes w.key) (firstRv l)
        (holds2 Q wts rnd k w) 3 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (AM (X₀ := X₀) Q p door wts rnd) w fr
              (carriedCoins (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2))) 3 pt i := by
  have hU := hP.facts.goes
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨-, zO1⟩ := hE
  obtain ⟨ownU, ownO, cU, cO, -, nO⟩ := cuts_both Q k c2 c5 n2 n5
  obtain ⟨-, sc1, -⟩ := cuts_atU Bk (Bk.rowsOf 1) (k.look 1) ⟨Q, 0⟩ p _
    _ _ none ownU cU ownO cO c hlp hb hfit
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
    (coinsE ownO).toArray (AM (X₀ := X₀) Q p door wts rnd) 1 rfl
    (carriedCoins (AM (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2)) sc1 S L 3 hf y hy hys
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

#print axioms ProofFile.Honest.K12.AtFile.coin_eq
#print axioms ProofFile.Honest.K12.AtFile.msg_eq
#print axioms ProofFile.Honest.K12.AtFile.cuts_both
#print axioms ProofFile.Honest.K12.AtFile.first_read
#print axioms ProofFile.Honest.K12.AtFile.tie_U
#print axioms ProofFile.Honest.K12.AtFile.tie_O
