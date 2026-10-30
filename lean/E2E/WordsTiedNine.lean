-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/WordsTiedNine.lean: THE TIE OF THE WORDS AT MEMBER 9, by the text of
tie_at_run (K12/TieAtRun.lean), at the key, member by member: what needs no fold in front. On a table of the
test on G_u's two members, the honest words at the thread's holdings are the words that the job's own rows make
at the lent coins. The stand enters here by premises alone: that a statement's shape, codes and first
challenge's length are what the plain eight leave: the fold's part comes later.

  count_two, count_five   the senders' rows hold just what they take, by the kernel at keyBook
  coin_eq, msg_eq   coinsOfMsg is what the cut hands: holds2 reads the senders' own coins
  tie_U, tie_O   the two members

Limits. At keyBook, at the real readers. Premises hpt, hf, hy, hys, hcd are the stand's: no fold is called here.
NOT IN FRONT OF A LAW OVER COINS: a tie of the words to the lent coins. Nothing on completeness, on soundness or
on what is hidden.
-/
import E2E.TreesSentBeforeTestAtNine
import Johnson.Desc.ProofFile.Honest.K12.TieAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.Light.WordsTiedNine
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle)
open OnBytes.Slice (rdE ofE)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St first withU)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open ProofFile.Honest
open ProofFile.Honest.K14
open AtPublicFiles.KeySharedThread (parKey randKey sentKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull atFull)
open AtPublicFiles.KeyDepthsAt (fit_two fit_five)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.HalvesAreJobs (pU)
open AtPublicFiles.KeyLay (jobKU)
open VerifiableInference.Desc.Key (Source)
open H2K.Member (piKUFull)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (ells_U sendings_U col_fit fresh_fit cuts_fit)

/-- The senders' rows hold just what they take. By the kernel. -/
theorem count_two : atFull (fun K => decide ((dueAt ((keyBook K).rowsOf 1) ⟨sendPlace 2, 0⟩).e =
    (sendingPart (jobU ⟨QK, 0⟩)).takes.e)) = true := by
  decide +kernel

theorem count_five : atFull (fun K => decide ((dueAt ((keyBook K).rowsOf 1) ⟨sendPlace 5, 0⟩).e =
    (sendingPart (jobOmega ⟨QK, 0⟩)).takes.e)) = true := by
  decide +kernel

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
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk : Type}
  (Xs : Source) (K₁ : KeyParts W₀ Rc X₀ X Wk) (B : Eight (parKey Xs PF))

/-- The job at G_u, as a ManyJob. -/
abbrev AM : ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobKU (X := X₀) ⟨parKey Xs PF, 0⟩ pU [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
    (keyProver K₁).storedWords (fun c => K₁.weights c.w₀) (fun c => randKey K₁ c.rc)

/-- The reader of the input. -/
abbrev askR : Common W₀ Rc TableKey → Ask :=
  askOf ⟨parKey Xs PF, 0⟩ (fun c => K₁.weights c.w₀) (fun c => randKey K₁ c.rc)

include hK₀ in
theorem cuts_both (e : parKey Xs PF = QK) (k : Coins (keyBook K₀)) :
    ∃ (ownU : Cs (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes)
      (ownO : Cs (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes),
      (k.look 1 ⟨sendPlace 2, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes = some ownU ∧
      (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes =
        some ownO ∧
      (k.look 1 ⟨sendPlace 2, 0⟩).1.e = (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes.e ∧
      (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.e := by
  have fU : (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes.f ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩).f ∧
      (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes.e ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩).e := by
    rw [e]
    exact fit_two K₀ hK₀
  have fO : (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.f ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).f ∧
      (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.e ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).e := by
    rw [e]
    exact fit_five K₀ hK₀
  obtain ⟨ownU, hU⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (by omega) ⟨sendPlace 2, 0⟩ _ fU)
  obtain ⟨ownO, hO⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (by omega) ⟨sendPlace 5, 0⟩ _ fO)
  have c2 := of_decide_eq_true (of_atFull count_two hK₀)
  have c5 := of_decide_eq_true (of_atFull count_five hK₀)
  rw [← e] at c2 c5
  have dU : (k.look 1 ⟨sendPlace 2, 0⟩).1 = dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩ :=
    AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 2, 0⟩
  have dO : (k.look 1 ⟨sendPlace 5, 0⟩).1 = dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩ :=
    AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 5, 0⟩
  exact ⟨ownU, ownO, hU, hO, by rw [dU]; exact c2, by rw [dO]; exact c5⟩

/-- The first challenge read off a list that is not empty. -/
theorem first_read (a : Ask) (l : List Fmt.Drawn) (hl : l ≠ []) :
    elems (heardFrom ({ input := a, heard := l, own := () } : State Ask Unit) 0 1) =
      Desc.K14.drawn (firstRv l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons d t => exact elems_one d

include hK₀ in
/-- **The tie at o_u.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_U (e : parKey Xs PF = QK) {layO}
    (hP : Plan2 (parKey Xs PF) (sentOf (parKey Xs PF).S) layO) (hSh : SendShapes (parKey Xs PF))
    (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (AM Xs K₁ B).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) ⟨pU.place, 1⟩
      (restPart (AM Xs K₁ B).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = (parKey Xs PF).par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 0 = some 0) (y : Oracle)
    (hy : S.oracles[0]? = some y) (hys : y.shape = shapeAt (jobU ⟨parKey Xs PF, 0⟩) 0)
    (hcd : S.codes = (parKey Xs PF).codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 0 pt) :
    words2 (parKey Xs PF) (sentOf (parKey Xs PF).S) (first (parKey Xs PF).codes w.key) (firstRv l)
        (holds2 (parKey Xs PF) K₁.weights (randKey K₁) k w) 0 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (AM Xs K₁ B) w fr
              (carriedCoins (AM Xs K₁ B).toRun.toTest (stretches _ c.2.2))) 0 pt i := by
  have hP' : pU = piKUFull := place_full
  have hU := hP.facts.goes
  have h2 : (sentOf (parKey Xs PF).S).size = 2 := hP.facts.goesTwo
  have hQf : sendingsFit (parKey Xs PF) = true := by
    rw [e]
    exact sendings_U
  have hE : ellsB ⟨parKey Xs PF, 0⟩ = true := by
    rw [e]
    exact ells_U
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨lU0, -⟩ := hE
  have hb : bookCutsU (keyBook K₀) ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP']
    exact of_atFull cuts_fit hK₀
  have hfit : freshFitsU ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP']
    exact fresh_fit
  obtain ⟨ownU, ownO, cU, cO, nU, -⟩ := cuts_both K₀ hK₀ Xs e k
  obtain ⟨sc0, -, -⟩ := cuts_atU (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) ⟨parKey Xs PF, 0⟩ pU _
    _ _ none ownU cU ownO cO c hlp hb hfit
  have eQ := jobU_par (Q := parKey Xs PF) hU 0
  have sUs : (jobU ⟨parKey Xs PF, 0⟩).Q.sent = sentOf (parKey Xs PF).S := by
    rw [eQ]
    exact Desc.K14.Law.parK1_sent _ 2 _ _
  have hs0U : ((jobU ⟨parKey Xs PF, 0⟩).Q.sent.getD 0 default).shape = (parKey Xs PF).par.S.fold.u := by
    rw [eQ]
    exact (shapeAt_of_get (parU (parKey Xs PF) (sentOf (parKey Xs PF).S)) 0
      ⟨(parKey Xs PF).par.S.fold.u, (parKey Xs PF).par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hU)).1
  have hk0 : 0 < (jobU ⟨parKey Xs PF, 0⟩).Q.sent.size := by
    rw [sUs, h2]
    decide
  have hv : vecAt (jobU ⟨parKey Xs PF, 0⟩) 0 (askR Xs K₁) none w fr =
      (jobU ⟨parKey Xs PF, 0⟩).data (⟨askR Xs K₁ w, l, ()⟩ : State Ask Unit) 0 :=
    congrFun (data_same (jobU_readsBelow ⟨parKey Xs PF, 0⟩) _ _ _ hfr) 0
  have wM := wordsAt_member (parKey Xs PF) hQf (jobU ⟨parKey Xs PF, 0⟩) (Or.inl ⟨rfl, rfl⟩) 0 hk0 _ rfl
    ⟨sendPlace 2, 0⟩ _ (askR Xs K₁) none w fr (⟨askR Xs K₁ w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownU).toArray (AM Xs K₁ B) 0 rfl
    (carriedCoins (AM Xs K₁ B).toRun.toTest (stretches _ c.2.2)) sc0 S L 0 hf y hy hys
    (by rw [hcd, eQ]; rfl) (fun _ => lU0)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobU ⟨parKey Xs PF, 0⟩).Q.sent.getD 0 default).shape.maskRows
      rw [hs0U, hSh.u.noMask]
      exact Nat.lt_irrefl 0)) pt i hi
  have mU := fun n => msg_eq k (jobU ⟨parKey Xs PF, 0⟩) (sendPlace 2) n ownU cU nU
  have rU := rowsU_read (parKey Xs PF) (first (parKey Xs PF).codes w.key) (firstRv l)
    (holds2 (parKey Xs PF) K₁.weights (randKey K₁) k w) (askR Xs K₁ w) l (coinsE ownU).toArray
    (by rw [sUs, h2]) hs0U hSh.u hSh.mask (first_read _ l hl) hpt (fun _ _ => rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 0) = _
      rw [mU 0, hs0U])
    (by
      show (match (parKey Xs PF).S.testU.head? with
        | some s => readFresh _ _ (coinsOfMsg k _ _ 1) s.k s.h
        | none => readCoins _ _ (coinsOfMsg k _ _ 1)) = _
      rw [mU 1]
      rfl) 0 hk0 pt i
  refine Eq.trans ?_ wM.symm
  rw [rU, eQ]
  show (if 0 ≤ 0 ∧ 0 < 0 + (parU (parKey Xs PF) (sentOf (parKey Xs PF).S)).sent.size then _ else _) = _
  rw [if_pos ⟨Nat.le_refl _, by
    rw [Desc.K14.Law.parK1_sent, h2]
    decide⟩]
  rfl

include hK₀ in
/-- **The tie at o_sp.**
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_O (e : parKey Xs PF = QK) {layO}
    (hP : Plan2 (parKey Xs PF) (sentOf (parKey Xs PF).S) layO) (hSh : SendShapes (parKey Xs PF))
    (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (AM Xs K₁ B).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) ⟨pU.place, 1⟩
      (restPart (AM Xs K₁ B).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = (parKey Xs PF).par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 3 = some 1) (y : Oracle)
    (hy : S.oracles[3]? = some y) (hys : y.shape = shapeAt (jobOmega ⟨parKey Xs PF, 0⟩) 1)
    (hcd : S.codes = (parKey Xs PF).codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 3 pt) :
    words2 (parKey Xs PF) (sentOf (parKey Xs PF).S) (first (parKey Xs PF).codes w.key) (firstRv l)
        (holds2 (parKey Xs PF) K₁.weights (randKey K₁) k w) 3 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (AM Xs K₁ B) w fr
              (carriedCoins (AM Xs K₁ B).toRun.toTest (stretches _ c.2.2))) 3 pt i := by
  have hP' : pU = piKUFull := place_full
  have hU := hP.facts.goes
  have hQf : sendingsFit (parKey Xs PF) = true := by
    rw [e]
    exact sendings_U
  have hE : ellsB ⟨parKey Xs PF, 0⟩ = true := by
    rw [e]
    exact ells_U
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨-, zO1⟩ := hE
  have hb : bookCutsU (keyBook K₀) ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP']
    exact of_atFull cuts_fit hK₀
  have hfit : freshFitsU ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP']
    exact fresh_fit
  obtain ⟨ownU, ownO, cU, cO, -, nO⟩ := cuts_both K₀ hK₀ Xs e k
  obtain ⟨-, sc1, -⟩ := cuts_atU (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) ⟨parKey Xs PF, 0⟩ pU _
    _ _ none ownU cU ownO cO c hlp hb hfit
  have hw : (Desc.K14.withOmega (parKey Xs PF).S).size = 2 ∧
      (Desc.K14.withOmega (parKey Xs PF).S)[0]? =
        some ⟨(parKey Xs PF).S.omega, (parKey Xs PF).S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega (parKey Xs PF).S)[1]? =
        some ⟨(parKey Xs PF).S.sharedSplit, (parKey Xs PF).S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.facts.two
  have sOs : (jobOmega ⟨parKey Xs PF, 0⟩).Q.sent = Desc.K14.withOmega (parKey Xs PF).S :=
    Desc.K14.Law.parK1_sent (parKey Xs PF) 5 _ _
  have hs0O : ((jobOmega ⟨parKey Xs PF, 0⟩).Q.sent.getD 0 default).shape = (parKey Xs PF).par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨parKey Xs PF, 0⟩).Q 0
      ⟨(parKey Xs PF).par.S.omega, (parKey Xs PF).par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hs1O : ((jobOmega ⟨parKey Xs PF, 0⟩).Q.sent.getD 1 default).shape =
      (parKey Xs PF).par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨parKey Xs PF, 0⟩).Q 1
      ⟨(parKey Xs PF).par.S.sharedSplit, (parKey Xs PF).par.S.sharedSplitLeafClass⟩
      (by rw [sOs]; exact hw.2.2)).1
  have hnoSp : (parKey Xs PF).par.S.sharedSplit.mainRows = 0 := sp_noMain hP
  have hk1 : 1 < (jobOmega ⟨parKey Xs PF, 0⟩).Q.sent.size := by
    rw [sOs, hw.1]
    decide
  have hv : vecAt (jobOmega ⟨parKey Xs PF, 0⟩) 1 (askR Xs K₁) none w fr =
      (jobOmega ⟨parKey Xs PF, 0⟩).data (⟨askR Xs K₁ w, l, ()⟩ : State Ask Unit) 1 :=
    congrFun (data_same (jobOmega_readsBelow ⟨parKey Xs PF, 0⟩) _ _ _ hfr) 1
  have wM := wordsAt_member (parKey Xs PF) hQf (jobOmega ⟨parKey Xs PF, 0⟩) (Or.inr ⟨rfl, rfl⟩) 1 hk1 _
    rfl ⟨sendPlace 5, 0⟩ _ (askR Xs K₁) none w fr (⟨askR Xs K₁ w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownO).toArray (AM Xs K₁ B) 1 rfl
    (carriedCoins (AM Xs K₁ B).toRun.toTest (stretches _ c.2.2)) sc1 S L 3 hf y hy hys
    (by rw [hcd]; rfl)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobOmega ⟨parKey Xs PF, 0⟩).Q.sent.getD 1 default).shape.mainRows
      rw [hs1O, hnoSp]
      exact Nat.lt_irrefl 0)) (fun _ => zO1) pt i hi
  have mO := fun n => msg_eq k (jobOmega ⟨parKey Xs PF, 0⟩) (sendPlace 5) n ownO cO nO
  have rO := rowsO_read (parKey Xs PF) (first (parKey Xs PF).codes w.key) (firstRv l)
    (holds2 (parKey Xs PF) K₁.weights (randKey K₁) k w) (askR Xs K₁ w) l (coinsE ownO).toArray
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
  show (if 0 + 2 ≤ 3 ∧ 3 < 0 + 2 + (parO (parKey Xs PF)).sent.size then _ else _) = _
  rw [if_pos ⟨by omega, by
    have e' : (parO (parKey Xs PF)).sent.size = 2 := by
      rw [Desc.K14.Law.parK1_sent]
      exact hw.1
    rw [e']
    decide⟩]
  rfl

end

end ProofFile.Honest.K12.Light.WordsTiedNine

end

#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.count_two
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.count_five
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.coin_eq
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.msg_eq
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.AM
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.askR
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.cuts_both
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.first_read
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.tie_U
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.tie_O
