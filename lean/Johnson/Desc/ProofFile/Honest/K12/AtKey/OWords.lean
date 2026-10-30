-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OWords.lean: `WordsTied` at the test on G_omega of the filled key thread: on a
table of its two members the honest words at the thread's holdings are the words that the job's own rows make at
the lent coins.

  `ell_omega_at_key`, `orc_two`, `orc_three`, `orc_one_is_other`   closed lines, by the kernel
  `ellOmegaB`, `omegaJob`, `askAt`   the Bool of the first line; the job; the reader of the input
  `tie_at_omega`, `tie_at_split`   the two members, general in the parameters and the place
  `decls_ten`, `point_at_ten`     at a stand something is heard, and the first challenge has the point's length
  `words_tied_at_ten`             the statement

Limits. NOT IN FRONT OF A LAW OVER COINS: `tie_at_omega`, `tie_at_split`, `point_at_ten`, `words_tied_at_ten` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
Their ground: a tie of the words to the lent coins, behind Thr as a premise. Thr at 10 and the lent row are premises. At the readers that the parts
hold. Off the members nothing is said. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OAccepted
import E2E.WordsTiedTop

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle Group)
open OnBytes.Slice (rdE ofE begun)
open OnBytes.Means (tableSize layoutOf)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (P14 St first withU)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.Sh (TestSh testSh)
open AtPublicFiles.KeySharedThread (parKey randKey sentKey threadKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull)
open AtPublicFiles.AtFiles (flat₂)
open AtPublicFiles.AtFiles.Full (QK PF omega_full)
open AtPublicFiles.KeyTreesKey (declOf tbKey)
open AtPublicFiles.KeyFixedLines (pre_rounds)
open AtPublicFiles.KeyDepthsAt (fit_five)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.TableFilled (TR ttF)
open VerifiableInference.Desc.Key (Source)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeOm AQ sentK ells_U sendings_U cuts_O codes_O)
open ProofFile.Honest.K12.Light.WordsTiedNine (msg_eq first_read count_five orc_of_shape draw_first)

/-- The code of o_omega's main rows has the message length that its logarithm says. -/
def ellOmegaB (A : SendPub) : Bool :=
  ((jobOmega A).Q.codes.base.getD (shapeAt (jobOmega A) 0).code default).ell ==
    2 ^ ((jobOmega A).Q.codes.base.getD (shapeAt (jobOmega A) 0).code default).logEll

theorem ell_omega_at_key : ellOmegaB AQ = true := by decide +kernel

theorem orc_two : (shapeOm.core.st.oracles[2]?).map (·.shape) = some (shapeAt (jobOmega AQ) 0) := by
  decide +kernel

theorem orc_three : (shapeOm.core.st.oracles[3]?).map (·.shape) = some (shapeAt (jobOmega AQ) 1) := by
  decide +kernel

/-- Control: message 1 is not o_sp. -/
theorem orc_one_is_other :
    (shapeOm.core.st.oracles[1]?).map (·.shape) ≠ some (shapeAt (jobOmega AQ) 1) := by
  decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type} (Q : P14) (p : P12)
  (door : Common W₀ Rc TableKey → Front X₀ → VerifiableInference.Desc.K12.T12)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)

/-- The job at G_omega, as a ManyJob. -/
abbrev omegaJob : ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobAtOmega ⟨Q, 0⟩ p door (fun c => wts c.w₀) (fun c => rnd c.rc) none

/-- The reader of the input. -/
abbrev askAt : Common W₀ Rc TableKey → Ask :=
  askOf ⟨Q, 0⟩ (fun c => wts c.w₀) (fun c => rnd c.rc)

/-- **The tie at o_omega.** -/
theorem tie_at_omega (hQf : sendingsFit Q = true) (hE : ellOmegaB ⟨Q, 0⟩ = true)
    (hb : bookCutsOmega Bk ⟨Q, 0⟩ p = true) {layO}
    (hP : Plan2 Q (sentOf Q.S) layO) (hSh : SendShapes Q)
    (k : Coins Bk) (ownO : Cs (sendingPart (jobOmega ⟨Q, 0⟩)).takes)
    (cO : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega ⟨Q, 0⟩)).takes = some ownO)
    (nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.place, 1⟩
      (restPart (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = Q.par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 2 = some 0) (y : Oracle)
    (hy : S.oracles[2]? = some y) (hys : y.shape = shapeAt (jobOmega ⟨Q, 0⟩) 0)
    (hcd : S.codes = Q.codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 2 pt) :
    words2 Q (sentOf Q.S) (first Q.codes w.key) (firstRv l)
        (holds2 Q wts rnd k w) 2 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (omegaJob (X₀ := X₀) Q p door wts rnd) w fr
              (carriedCoins (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2))) 2 pt i := by
  have hU := hP.facts.goes
  unfold ellOmegaB at hE
  rw [beq_iff_eq] at hE
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
  have hv : vecAt (jobOmega ⟨Q, 0⟩) 0 (askAt Q wts rnd) none w fr =
      (jobOmega ⟨Q, 0⟩).data (⟨askAt Q wts rnd w, l, ()⟩ : State Ask Unit) 0 :=
    congrFun (data_same (jobOmega_readsBelow ⟨Q, 0⟩) _ _ _ hfr) 0
  have wM := wordsAt_member Q hQf (jobOmega ⟨Q, 0⟩) (Or.inr ⟨rfl, rfl⟩) 0 hk0 _
    rfl ⟨sendPlace 5, 0⟩ _ (askAt Q wts rnd) none w fr (⟨askAt Q wts rnd w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownO).toArray (omegaJob (X₀ := X₀) Q p door wts rnd) 0 rfl
    (carriedCoins (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2)) sc0 S L 2 hf y hy hys
    (by rw [hcd]; rfl) (fun _ => hE)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape.maskRows
      rw [hs0O, hSh.omega.noMask]
      exact Nat.lt_irrefl 0)) pt i hi
  have mO := fun n => msg_eq k (jobOmega ⟨Q, 0⟩) (sendPlace 5) n ownO cO nO
  have rO := rowsO_read Q (first Q.codes w.key) (firstRv l)
    (holds2 Q wts rnd k w) (askAt Q wts rnd w) l (coinsE ownO).toArray
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

/-- **The tie at o_sp.** -/
theorem tie_at_split (hQf : sendingsFit Q = true) (hE : ellsB ⟨Q, 0⟩ = true)
    (hb : bookCutsOmega Bk ⟨Q, 0⟩ p = true) {layO}
    (hP : Plan2 Q (sentOf Q.S) layO) (hSh : SendShapes Q)
    (k : Coins Bk) (ownO : Cs (sendingPart (jobOmega ⟨Q, 0⟩)).takes)
    (cO : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega ⟨Q, 0⟩)).takes = some ownO)
    (nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨Q, 0⟩)).takes.e)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) (l : List Fmt.Drawn)
    (hl : l ≠ []) (hfr : fr.heard.take (0 + 1) = l.take (0 + 1))
    (c : (restPart (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.place, 1⟩
      (restPart (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest : Part Empty _ _) = .ok c)
    (hpt : (Desc.K14.drawn (firstRv l)).length = Q.par.S.kCol)
    (S : Statement) (L : GroupLayout) (hf : L.find 3 = some 1) (y : Oracle)
    (hy : S.oracles[3]? = some y) (hys : y.shape = shapeAt (jobOmega ⟨Q, 0⟩) 1)
    (hcd : S.codes = Q.codes) (pt : OnBytes.Part) (i : ℕ) (hi : i < tableSize S 3 pt) :
    words2 Q (sentOf Q.S) (first Q.codes w.key) (firstRv l)
        (holds2 Q wts rnd k w) 3 pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany (omegaJob (X₀ := X₀) Q p door wts rnd) w fr
              (carriedCoins (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2))) 3 pt i := by
  have hU := hP.facts.goes
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨-, zO1⟩ := hE
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
  have hv : vecAt (jobOmega ⟨Q, 0⟩) 1 (askAt Q wts rnd) none w fr =
      (jobOmega ⟨Q, 0⟩).data (⟨askAt Q wts rnd w, l, ()⟩ : State Ask Unit) 1 :=
    congrFun (data_same (jobOmega_readsBelow ⟨Q, 0⟩) _ _ _ hfr) 1
  have wM := wordsAt_member Q hQf (jobOmega ⟨Q, 0⟩) (Or.inr ⟨rfl, rfl⟩) 1 hk1 _
    rfl ⟨sendPlace 5, 0⟩ _ (askAt Q wts rnd) none w fr (⟨askAt Q wts rnd w, l, ()⟩ : State Ask Unit) hv
    (coinsE ownO).toArray (omegaJob (X₀ := X₀) Q p door wts rnd) 1 rfl
    (carriedCoins (omegaJob (X₀ := X₀) Q p door wts rnd).toRun.toTest (stretches _ c.2.2)) sc1 S L 3 hf y hy hys
    (by rw [hcd]; rfl)
    (fun hpos => absurd hpos (by
      show ¬ 0 < ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows
      rw [hs1O, hnoSp]
      exact Nat.lt_irrefl 0)) (fun _ => zO1) pt i hi
  have mO := fun n => msg_eq k (jobOmega ⟨Q, 0⟩) (sendPlace 5) n ownO cO nO
  have rO := rowsO_read Q (first Q.codes w.key) (firstRv l)
    (holds2 Q wts rnd k w) (askAt Q wts rnd w) l (coinsE ownO).toArray
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

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- The rounds in front of member 10 are the eight's and the test on G_u's. -/
theorem decls_ten :
    declsTo (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs 10 =
      declOf (parKey Xs PF) ++ (H2K.JointK.keyGu PF).rounds := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w
  have hp : (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]).length = 10 := by
    unfold H2K.JointK.keySharedPre
    rw [List.length_append, List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : flat₂ Xs.chains PF = (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]) ++
      H2K.JointK.keyOmega (PF.O.getD PF.U) :: [H2K.JointK.keySharedEnd Xs.chains PF] :=
    H2K.JointK.keyShared_cut_omega _ _ _ omega_full
  unfold declsTo
  rw [hO.bs]
  show ((flat₂ Xs.chains PF).take 10).flatMap (·.rounds) = _
  rw [hc, List.take_left' hp, List.flatMap_append, pre_rounds]
  simp

/-- **At a stand something is heard, and the first challenge has the point's length.** -/
theorem point_at_ten (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E) (ds : List Fmt.Drawn) :
    m.st.heard ≠ [] ∧ (m.st.heard ++ ds).take (0 + 1) = m.st.heard.take (0 + 1) ∧
      (Desc.K14.drawn (firstRv (m.st.heard ++ ds))).length = (parKey Xs PF).par.S.kCol := by
  have hd : drawsFit (declsTo (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs 10) m.st.heard = true :=
    u.2.1
  rw [decls_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀] at hd
  have hf := draw_first
  rw [← e] at hf
  cases hD : declOf (parKey Xs PF) with
  | nil =>
    rw [hD] at hf
    cases hf
  | cons d tl =>
    rw [hD] at hd hf
    have hdraw : d.entry.drawE = (parKey Xs PF).par.S.kCol := Option.some.inj hf
    cases hh : m.st.heard with
    | nil =>
      rw [hh] at hd
      simp [drawsFit] at hd
    | cons x t =>
      rw [hh, List.cons_append] at hd
      simp only [drawsFit, Bool.and_eq_true] at hd
      have h1 := hd.1
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
      have hlen : x.elems.length = d.entry.drawE := h1.1.1.1.1.1.1.1
      refine ⟨by simp, by simp, ?_⟩
      show (Desc.K14.drawn (rvOf x)).length = _
      rw [← elems_one x, ← hdraw, ← hlen]
      show (x.elems.map OnBytes.E.ofTriple ++ []).length = _
      simp

include hK₀ in
/-- **`WordsTied` at the test on G_omega, at a stand.** -/
theorem words_tied_at_ten (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E) (ds : List Fmt.Drawn)
    (c : (restPart (manyAtTen Xs K₁ B (X₀ := X₀)).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) ⟨pO.place, 1⟩
      (restPart (manyAtTen Xs K₁ B (X₀ := X₀)).toRun.toTest : Part Empty _ _) = .ok c) :
    ∀ G, ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st.groups[
        ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g]? = some G →
      WordsTied ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st
        ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g G
        (ℓ.get ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).wit k m.st.input (m.st.heard ++ ds)))
        (layoutOf ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st G)
        (plainMany (manyAtTen Xs K₁ B (X₀ := X₀)) m.st.input (frontOf m)
          (carriedCoins (manyAtTen Xs K₁ B (X₀ := X₀)).toRun.toTest (stretches _ c.2.2))) := by
  intro G hG oM ho pt i hi
  obtain ⟨hne, ht1, hpt⟩ := point_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e u ds
  have hSh : SendShapes (parKey Xs PF) := by
    rw [e]
    exact sendShapes_of_fit sendings_U
  have hQf : sendingsFit (parKey Xs PF) = true := by
    rw [e]
    exact sendings_U
  have hsh : testSh ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)) = shapeOm := by
    have e1 := accepted_shape_written (W := Common W₀ Rc TableKey) (X := X₀) e place_full
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (by rw [B.made]) (fun v => v.key)
      colsOpened m.st.input (frontOf m)
    exact e1
  have hcodes : ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st.codes =
      (parKey Xs PF).codes := by
    have h1 : (testSh ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m))).core.st.codes =
        ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st.codes := rfl
    rw [← h1, hsh, e]
    exact codes_O
  have hmem : G.members.toList = [2, 3] := (group_at_door _ hsh G hG).2
  have hmemA : G.members = #[2, 3] := Array.toList_inj.1 hmem
  obtain ⟨hf2, hf3⟩ := VerifiableInference.Desc.K12.Coin.find_two
    (layoutOf ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st G) 2 3 (by decide)
    (show G.members = #[2, 3] from hmemA)
  have hts : ∀ o' pt', tableSize (begun ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st
      ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g G) o' pt' =
      tableSize ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st o' pt' :=
    fun o' pt' => by
      unfold tableSize OnBytes.Statement.tableBits
      rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]
  have hcd := (OnBytes.Slice.begun_codes ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st
    ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g G).trans hcodes
  have hcuts : bookCutsOmega (keyBook K₀) ⟨parKey Xs PF, 0⟩ pO = true := by
    rw [e, pO_full]
    exact of_atFull cuts_O hK₀
  have hEo : ellOmegaB ⟨parKey Xs PF, 0⟩ = true := by
    rw [e]
    exact ell_omega_at_key
  have hEs : ellsB ⟨parKey Xs PF, 0⟩ = true := by
    rw [e]
    exact ells_U
  have fO : (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.f ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).f ∧
      (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.e ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).e := by
    rw [e]
    exact fit_five K₀ hK₀
  obtain ⟨ownO, cO⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (by omega) ⟨sendPlace 5, 0⟩ _ fO)
  have n5 := of_decide_eq_true (of_atFull count_five hK₀)
  rw [← e] at n5
  have nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e = (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.e := by
    rw [AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 5, 0⟩]
    exact n5
  have hWit : ℓ.get ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).wit k m.st.input
      (m.st.heard ++ ds)) = witAll (parKey Xs PF) (sentKey Xs PF)
        (holds2 (parKey Xs PF) K₁.weights (randKey K₁)) (fun k w h => ℓ.get (rest k w h)) k m.st.input
        (m.st.heard ++ ds) :=
    get_witL ℓ _ _ _ rest k m.st.input (m.st.heard ++ ds)
  rw [hWit]
  unfold witAll
  have hw2 : (Desc.K14.withOmega (parKey Xs PF).S).size = 2 :=
    (Desc.K14.Honest.withOmega_two hQ.facts.two).1
  have hoo : oM = 2 ∨ oM = 3 := by
    have h' : oM ∈ G.members.toList := ho
    rw [hmem] at h'
    simpa using h'
  rcases hoo with rfl | rfl
  · have hy2 : ((begun ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st
        ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g G).oracles[2]?).map (·.shape) =
        some (shapeAt (jobOmega ⟨parKey Xs PF, 0⟩) 0) := by
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh, e]
      exact orc_two
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy2
    rw [words2_ours (parKey Xs PF) (sentKey Xs PF) _ _ _ _ 2
      (Or.inr ⟨by omega, by rw [hw2]; omega⟩) pt i]
    exact tie_at_omega (parKey Xs PF) pO _ K₁.weights (randKey K₁) hQf hEo hcuts hQ hSh k ownO cO nO
      m.st.input (frontOf m) (m.st.heard ++ ds) (by simp [hne]) ht1.symm c hlp hpt _ _ hf2 y hy hys hcd
      pt i (by rw [hts]; exact hi)
  · have hy3 : ((begun ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).st
        ((manyAtTen Xs K₁ B (X₀ := X₀)).rec₀ m.st.input (frontOf m)).g G).oracles[3]?).map (·.shape) =
        some (shapeAt (jobOmega ⟨parKey Xs PF, 0⟩) 1) := by
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh, e]
      exact orc_three
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy3
    rw [words2_ours (parKey Xs PF) (sentKey Xs PF) _ _ _ _ 3
      (Or.inr ⟨by omega, by rw [hw2]; omega⟩) pt i]
    exact tie_at_split (parKey Xs PF) pO _ K₁.weights (randKey K₁) hQf hEs hcuts hQ hSh k ownO cO nO
      m.st.input (frontOf m) (m.st.heard ++ ds) (by simp [hne]) ht1.symm c hlp hpt _ _ hf3 y hy hys hcd
      pt i (by rw [hts]; exact hi)

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.ell_omega_at_key
#print axioms ProofFile.Honest.K12.AtKey.orc_two
#print axioms ProofFile.Honest.K12.AtKey.orc_three
#print axioms ProofFile.Honest.K12.AtKey.orc_one_is_other
#print axioms ProofFile.Honest.K12.AtKey.tie_at_omega
#print axioms ProofFile.Honest.K12.AtKey.tie_at_split
#print axioms ProofFile.Honest.K12.AtKey.decls_ten
#print axioms ProofFile.Honest.K12.AtKey.point_at_ten
#print axioms ProofFile.Honest.K12.AtKey.words_tied_at_ten
