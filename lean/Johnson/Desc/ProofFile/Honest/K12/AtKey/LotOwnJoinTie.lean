-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnJoinTie.lean: THE TIE OF THE WORDS AT THE LAST THREAD OF THE KEY FILE: the premise `htie` of
`say_stand` (E2E/KeyOwnSayThread.lean) and of `last_done` (E2E/KeyLastDone.lean), at the thread `threadOwn` (E2E/KeyLastAll.lean) with the
first half's filling `fillH` (E2E/FirstHFill.lean) and the letter `mlKey`, at the own test's job at the parts' own senders, AT THE COINS THAT
THE BOOK LENDS THE TEST's ROW: on the tables of the own group's members the words that the thread's witness holds are the words that the
job makes of its plain rows.

  `written_stages`, `omega_at_written_shape`   closed lines: the ranges' test has four stages; Omega's copy has the number 11. By the kernel
  `written_shape_is_the_run's`     the written shape `A2` is what `ZW` returns behind two members
  `plan_message_of_index_masks`, `plan_message_of_vector_w`   `ho₀`, `ho₂` of `say_stand`: the plan's numbers of messages 0 and 2
  `first_chain_has_its_rounds`     the first chain has 18,851 rounds, in scope
  `filled_words_premises_in_scope`   `FilledWordsPremises` (LotOwnJoinWords.lean), in scope
  `tie_at_last_thread`             THE TIE, behind `Thr` at border 2 and the lending
  `tie_at_last_thread_said`        the same behind `ThrS` at any letter: `htie`'s text, with the lending in front

THE PREMISES OF `tie_at_last_thread`, BY NAME.
  public              hs, scope, hK₀
  `third_shaped`'s     hfit (the key fits, at the shared thread's valid inputs), hd (the default pair names no W): `last_done` has both
  on the letters      hw: the thread's input is the filling's instance: w = ⟨w₀, rc, x, ()⟩
  ON THE PARTS        `SendersPlansAlike K` · `SendersReadInFront K N` (IT CAN SAY NO) · the two sendings' places
WITH THE LENDING IN FRONT. The right side reads the coins c that the test's row is lent; the left side reads the run's coins k. Without
«lendRow … = .ok c» the equation is asked at every c and cannot be met where two c differ on a member's carried stretch.

By what. `wordsTied_at_key_own_test` (LotOwnTied.lean) with its public premises paid as in `says_clause_of_alike` (LotOwnAlike.lean);
`last_witness_words_are_the_term` (LotOwnJoinWords.lean); `shape_own` (E2E/KeyOwnFront.lean), `third_shaped` (E2E/KeyLastShaped.lean).

Imports. As LotOwnJoinWords.lean's head says. So the count 18,851 is written out.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind `Thr` and `lendRow`'s return.
- That a run reaches a stand of this thread is not said. K, f, Q and the threads' other letters are letters.
- In scope, at the full size, at `keyBook`.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnJoinWords
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnRounds
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstStand
import E2E.KeyLastAll
import E2E.KeyOwnFront
import E2E.KeyLastShaped

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open OnBytes.Means (Words tableSize layoutOf)
open OnBytes.Slice (GE begun)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi FirstState descriptionFromSource)
open VerifiableInference.Desc.Own (keyFits)
open Johnson.RunOne.KeyRows1 (plan₁)
open _root_.Desc.K14 (St)
open Lk6.AtPlan (keyX)
open H2K.Member (piKWFull)
open AtPublicFiles.AtFiles (KeySourced Sh₃ sh₃ SF ZW)
open AtPublicFiles.AtFiles.Full (QK X0 A0 PF x0_some later_sourced par_sourced six_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyLay (pWK)
open AtPublicFiles.KeyThread (one₀)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyDoorItems (wit₃)
open AtPublicFiles.KeyLastChain (wordsKey val₁Key mlKey threadOwn keptOwn tableKey third_shaped shape_own A2)
open AtPublicFiles.FirstH (fillH LaterFill HCells HTab)
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.Light (plainMany)

/-- The ranges' test has four stages, at the written sizes. By the kernel. -/
theorem written_stages : keyX.stages.length = 4 := by decide +kernel

/-- Omega's copy has the number 11 at the written shape in front of the own test. By the kernel. -/
theorem omega_at_written_shape : A2.2.omega = 11 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **The written shape `A2` is what `ZW` returns behind two members.** -/
theorem written_shape_is_the_run's (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {A₂ : Sh₃} (h₂ : ZW.run 2 A0 = .ok A₂) : A2 = A₂ := by
  obtain rfl := later_sourced hs scope
  have hr := AtPublicFiles.AtFiles.ownRounds_full hs scope
  have hp : H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W = piKWFull := written_own
  unfold A2
  rw [hr, hp]
  show (ZW.run 2 A0).toOption.getD A0 = A₂
  rw [h₂]
  rfl

/-- `ho₀` of `say_stand`. -/
theorem plan_message_of_index_masks (Xs : Source) : (plan₁ (one₀ Xs)).orc 0 = some 0 := rfl

/-- In scope the ranges' test has four stages. -/
theorem stages_in_scope (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (one₀ Xs).ranges.stages.length = 4 := by
  have hr : (one₀ Xs).ranges = keyX := (six_sourced hs scope).ranges
  rw [hr]
  exact written_stages

/-- `ho₂` of `say_stand`, in scope. -/
theorem plan_message_of_vector_w (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (plan₁ (one₀ Xs)).orc 2 = some 9 := by
  show some (1 + 2 * (one₀ Xs).ranges.stages.length) = some 9
  rw [stages_in_scope hs scope]

/-- The closed line: the rows of the written list have 18,851 rounds. -/
theorem written_first_chain_rounds : (AtPublicFiles.KeyBook.fullFirst.map (·.2)).sum = 18851 := by
  decide +kernel

/-- **The first chain has 18,851 rounds**, in scope. -/
theorem first_chain_has_its_rounds (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length = 18851 := by
  have r1 : Johnson.RunOne.Sound.rowsOf (descriptionFromSource Xs Nr Pl).first.blocksInOrder = AtPublicFiles.KeyBook.fullFirst :=
    (AtPublicFiles.KeyBook.places_named scope hs.named).1
  have e := rounds_of_front (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length
  rw [List.take_length, r1, List.take_of_length_le (by
    rw [← r1]
    unfold Johnson.RunOne.Sound.rowsOf
    rw [List.length_map])] at e
  rw [e]
  exact written_first_chain_rounds

variable {W₀ Rc X₀ X Wk P₂ Wt₂ : Type} {K₀ : KeyPub}

/-- **`FilledWordsPremises` in scope.** -/
theorem filled_words_premises_in_scope (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀) {K : KeyParts W₀ Rc X₀ X Wk}
    (senders : SendersPlansAlike K) (placeIndexMasks : K.idx.P.place = ⟨1, none, 1, .K1⟩)
    (placeVectorW : K.w.P.place = ⟨1, none, 14, .K1⟩) :
    FilledWordsPremises (Bk := keyBook K₀) Xs Nr Pl K (pWK Pl).place
      challengesBeforeVectorWAtFullSize 18851 := by
  obtain ⟨bw, msg₀, hb, -, -, -, -⟩ := public_samples hs scope
  have written : pWK Pl = piKWFull := by
    rw [later_sourced hs scope]
    exact written_own
  obtain ⟨layO, hP⟩ := (plan_of_alike senders).plan
  have e17 := rounds_in_front_of_vector_w hs scope hb
  rw [vector_w_block_number hs scope hb] at e17
  refine ⟨book_of_alike hK₀ senders written, placeIndexMasks, placeVectorW, ?_, ?_,
    stages_in_scope hs scope, e17, first_chain_has_its_rounds hs scope, by decide,
    senders.sharedPlan.trans (par_sourced hs scope).symm, ?_⟩
  · rw [senders.indexMasksNotices]
    exact written_plans_send.1
  · rw [senders.vectorWNotices]
    exact written_plans_send.2.1
  · have two : (_root_.Desc.K14.withOmega K.send.P.S).size = 2 :=
      (_root_.Desc.K14.Honest.withOmega_two hP.facts.two).1
    rw [two]
    decide

section Thread
variable (Xs) (Nr) (Pl) (K : KeyParts W₀ Rc X₀ X Wk) (f : W₀ → Weights)
  (Q : LaterFill (keyBook K₀) W₀ Rc)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : ℕ → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words Cb.Gl.E))
  (n₁ n₂ : ℕ) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

local notation "NF" =>
  numbersAtFullSize challengesBeforeVectorWAtFullSize 18851

local notation "TO" => threadOwn Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt
  (mlKey (val₁Key Xs (fillH Xs Nr Pl K f Q x))) n₁ n₂ Vd w dfltT dfltM

local notation "AG" => jobAtKeyOwnTest K Xs Nr Pl

/-- **THE TIE AT THE LAST THREAD.** The premises by name: this file's head.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_at_last_thread (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hw : w = ⟨w₀, rc, x, ()⟩)
    (senders : SendersPlansAlike K) (reads : SendersReadInFront K NF)
    (placeIndexMasks : K.idx.P.place = ⟨1, none, 1, .K1⟩)
    (placeVectorW : K.w.P.place = ⟨1, none, 14, .K1⟩) :
    ∀ k st m E (c : RowCoins [(firstPart (AG).toRun.toTest :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X), restPart (AG).toRun.toTest]),
      Thr TO 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (AG).toRun.toTest.p.place
        [(firstPart (AG).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (AG).toRun.toTest] 0 = .ok c →
      ∀ G, st.st.groups[st.loc.own]? = some G →
      ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key Xs (fillH Xs Nr Pl K f Q x)) st
            (Thread.wit TO k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany AG m.st.input (frontOf m) (restCoins (AG).toRun.toTest c.2.1)) o pt i := by
  intro k st m E c hT hc G hG o ho pt i hi
  have hZ := third_shaped Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁
    tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs (fillH Xs Nr Pl K f Q x)))
    (tableKey Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁
      Said₂ d Dt (mlKey (val₁Key Xs (fillH Xs Nr Pl K f Q x))) n₁ n₂ Vd (fun _ _ _ => True) keptOwn w
      dfltT dfltM)
    n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hs scope hfit hd (fun _ _ _ => true)
  have hsh : sh₃ SF st = A2 := AtPublicFiles.KeyLastChain.shape_own hs scope rfl hZ hT
  obtain ⟨A₀, A₂, h₀, h₂, -, -, -⟩ := own_closed
  obtain rfl : A₀ = A0 := Option.some.inj (h₀.symm.trans x0_some)
  have hsh' : sh₃ SF st = A₂ := hsh.trans (written_shape_is_the_run's hs scope h₂)
  have homega : st.loc.omega = 11 :=
    (congrArg (fun a : Sh₃ => a.2.omega) hsh).trans omega_at_written_shape
  have hS := statement_of_alike senders h₀ h₂ hsh' challengesBeforeVectorWAtFullSize
    18851
  have P := filled_words_premises_in_scope hs scope hK₀ senders placeIndexMasks placeVectorW
  have rounds : RoundsInFrontOfOwnTest TO Xs Nr Pl QK.par.S.kCol :=
    rounds_in_front hs scope _ rfl rfl rfl
  obtain ⟨dd, rest, hr, hdraw⟩ := rounds.point
  have hfit' : drawsFit ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds) ++ dd :: rest) m.st.heard =
      true := by
    rw [← hr]
    exact hT.2.1
  have hfirst : 18851 =
      ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length := (first_chain_has_its_rounds hs scope).symm
  have hear := heard_at_own_test K NF _ dd rest m.st.heard hfit' hfirst.symm
    (by rw [senders.sharedPlan]; exact hdraw)
  have hlong : 18851 ≤ m.st.heard.length := by
    have e := ProofFile.Honest.drawsFit_length _ _ hfit'
    rw [List.length_append, ← hfirst] at e
    omega
  have tie := wordsTied_at_key_own_test K Xs Nr Pl NF reads P.book (plan_of_alike senders) hfirst k
    m.st.input (frontOf m) m.st.heard hear c hc st.st st.loc.own hS G hG o ho pt i hi
  have ho' : o ∈ [0, 9, 11] := by
    rw [hS.members G hG, P.indexMasksSends] at ho
    exact ho
  have hv : m.st.input = w ∧ Vd m.st.input := hT.2.2.2.2.2.2
  have hin : m.st.input = ⟨w₀, rc, x, ()⟩ := hv.1.trans hw
  rw [List.append_nil]
  refine Eq.trans ?_ tie
  show wordsKey (val₁Key Xs (fillH Xs Nr Pl K f Q x)) st
    (wit₃ Xs Nr Pl K (fillH Xs Nr Pl K f Q x) ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k m.st.input m.st.heard) o
    pt i = _
  rw [hin]
  exact last_witness_words_are_the_term Xs Nr Pl K f Q x ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ P st homega k w₀
    rc m.st.heard hlong o ho' pt i

/-- **`htie`'s TEXT, WITH THE LENDING IN FRONT**, behind `ThrS` at any letter.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem tie_at_last_thread_said (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hw : w = ⟨w₀, rc, x, ()⟩)
    (senders : SendersPlansAlike K) (reads : SendersReadInFront K NF)
    (placeIndexMasks : K.idx.P.place = ⟨1, none, 1, .K1⟩)
    (placeVectorW : K.w.P.place = ⟨1, none, 14, .K1⟩)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop) :
    ∀ k st m E (c : RowCoins [(firstPart (AG).toRun.toTest :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X), restPart (AG).toRun.toTest]),
      ThrS TO Said 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (AG).toRun.toTest.p.place
        [(firstPart (AG).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (AG).toRun.toTest] 0 = .ok c →
      ∀ G, st.st.groups[st.loc.own]? = some G →
      ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key Xs (fillH Xs Nr Pl K f Q x)) st
            (Thread.wit TO k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany AG m.st.input (frontOf m) (restCoins (AG).toRun.toTest c.2.1)) o pt i :=
  fun k st m E c hT => tie_at_last_thread Xs Nr Pl K f Q ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁
    Said₁ Said₂ d Dt n₁ n₂ Vd w dfltT dfltM hs scope hK₀ hfit hd hw senders reads placeIndexMasks
    placeVectorW k st m E c hT.1

end Thread

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.written_stages
#print axioms ProofFile.Honest.K12.AtKey.omega_at_written_shape
#print axioms ProofFile.Honest.K12.AtKey.written_shape_is_the_run's
#print axioms ProofFile.Honest.K12.AtKey.plan_message_of_index_masks
#print axioms ProofFile.Honest.K12.AtKey.stages_in_scope
#print axioms ProofFile.Honest.K12.AtKey.plan_message_of_vector_w
#print axioms ProofFile.Honest.K12.AtKey.written_first_chain_rounds
#print axioms ProofFile.Honest.K12.AtKey.first_chain_has_its_rounds
#print axioms ProofFile.Honest.K12.AtKey.filled_words_premises_in_scope
#print axioms ProofFile.Honest.K12.AtKey.tie_at_last_thread
#print axioms ProofFile.Honest.K12.AtKey.tie_at_last_thread_said
