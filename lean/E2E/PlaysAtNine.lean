-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/PlaysAtNine.lean

`Plays` AT MEMBER 9 OF THE KEY's SHARED THREAD, AT keyBook, WITH NO `PlaysOn` PREMISE. So wherever Thr
stands at 9, the list fits, nothing stops and `chainSteps` returns, `Moved` is had.

  `words_of_hand`  copied from Honest/K12/RunOfThr.lean
  `noTbl`, `sent_words`   `sentTables`' words read no row
  `cut_some`, `send_words`   where a sending's coins lie within the book, `sendTable`'s words are the
                   shape's, at every coin, input and list
  `tb_own`, `table_words`   so at `tbKey` at own 0 to 2
  `old_nine`       `RunPlays.old` at a stand of Thr at 9
  `plays_at_nine`  the statement

PREMISES, and who pays: as in HalvesAreJobs.lean's and TreesAtNine.lean's heads. hK₀: `full_made`. What
stays: e, B, hs, hsp, own₀, htt.

Limits.
- That Thr stands at 9 at this thread is NOT said: `stand_nine` is at other letters.
- htt, the arm at own 3 to 6, stays a premise; no filling of tt is typed.
- At keyBook, not at a free book: `old` needs the sendings' coins at hand at every k.
- wts, rnd are free here, tied to K₁'s readers by nothing: where they differ from them Thr cannot be
  reached behind member 2 [by reading], and the statement holds for nothing. The real table:
  `plays_nine_real` (PlaysAtLetters.lean).
- Member 9 alone. Nothing on completeness, on soundness or on what is hidden.

NOT IN FRONT OF A LAW OVER COINS: `plays_at_nine` bear this label; the rule is at its home, the head
of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from Thr as the premise
`PlaysOn` is paid at, `Plays` as an end. None: the bar is flat. -/
import E2E.HalvesAreJobs
import E2E.PlaysAtNineGuards
import E2E.KeyDepthsKernel
import Johnson.Desc.ProofFile.Honest.K12.AgreeAtKey
import Johnson.Desc.ProofFile.Honest.K12.PlanAtKeyKernel
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.Thread.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.PlaysAtNine
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey parKey sentKey randKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull look_due seen)
open AtPublicFiles.KeyDoorNine (jobNine seat_nine)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyTblTrial (sendings_count)
open AtPublicFiles.KeyTreesKey (treesOf5)
open AtPublicFiles.KeyFixedLines (trees_key)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega hk_U)
open AtPublicFiles.KeyPlaysAt (memsOf members_closed fresh_closed)
open AtPublicFiles.KeyOpens (takesFit takes_two takes_five)
open AtPublicFiles.TreesAtNine (JN TN)
open AtPublicFiles.HalvesAreJobs (pU pO find_U trees_nine_at)
open H2K.Member (piKUFull)

/-- Copied from Honest/K12/RunOfThr.lean. -/
theorem words_of_hand {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    {σ : Fmt.TreeSource} {k : Coins Bk} {m : Mid W X} {E : Env} (h : T.handAt σ k m E = true) :
    ∃ pt, E.tree σ = some pt ∧ pt.2.words = (T.tableAt σ k m).2.words := by
  obtain ⟨pt, hE, -, hs⟩ := T.handAt_elim h
  unfold Table.same at hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  exact ⟨pt, hE, beq_iff_eq.1 hs.1.2⟩

/-- A table of no words. -/
abbrev noTbl : Table := { logLength := 0, words := 0, sym := fun _ j => j.elim0 }

theorem sent_words (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (L : Nat → K14.Laid)
    (i : Nat) : ((sentTables codes sent L).getD i noTbl).words = (shapeWords codes sent).getD i 0 := by
  unfold sentTables shapeWords
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_zipIdx]
  cases ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList[i]? <;> rfl

theorem cut_some {d : Due} (c : Cs d) (n : Due) (h1 : n.f ≤ d.f) (h2 : n.e ≤ d.e) :
    ∃ x, c.cut ⟨0, 0⟩ n = some x := by
  have h : (⟨0, 0⟩ : Due).f + n.f ≤ d.f ∧ (⟨0, 0⟩ : Due).e + n.e ≤ d.e :=
    ⟨by show 0 + n.f ≤ d.f; omega, by show 0 + n.e ≤ d.e; omega⟩
  unfold Cs.cut
  exact ⟨_, dif_pos h⟩

/-- **Where a sending's coins lie within the book, its table's words are the shape's.** -/
theorem send_words {Bk : ProverCoinCounts} {W : Type} (J : SendJob) (wit : W → Ask) (pl : Place) (i : Nat)
    (k : Coins Bk) (w : W) (h : List Fmt.Drawn) (ht : takesFit Bk ⟨pl, 0⟩ J = true) :
    (sendTable J wit pl 1 i k w h).2.words = (shapeWords J.Q.codes J.Q.sent).getD i 0 := by
  have hd : (k.look 1 ⟨pl, 0⟩).1 = dueAt (Bk.rowsOf 1) ⟨pl, 0⟩ := look_due k 1 ⟨pl, 0⟩
  unfold takesFit at ht
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
  obtain ⟨own, hown⟩ := cut_some (k.look 1 ⟨pl, 0⟩).2 (sendingPart J).takes (by rw [hd]; exact ht.1)
    (by rw [hd]; exact ht.2)
  unfold sendTable
  simp only [hown]
  exact sent_words _ _ _ _

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc : Type}
  (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

omit hK₀ in
/-- `tbKey` at an own tree, at any parameters. -/
theorem tb_own (Q : _root_.Desc.K14.P14) (n : Nat) :
    tbKey Q wts rnd tk tt (.own n) =
      if n < treesU Q then sendTable (jobU ⟨Q, 0⟩) (witOf Q wts rnd) (sendPlace 2) 1 n
      else if n < treesU Q + treesOf5 Q then
        sendTable (jobOmega ⟨Q, 0⟩) (witOf Q wts rnd) (sendPlace 5) 1 (n - treesU Q)
      else tt n := rfl

include hK₀ in
/-- **At own 0 to 2 the trial's table has the width `tblW`, at every coin, input and list.** -/
theorem table_words (n : Nat) (hn : n < 3) (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey)
    (h : List Fmt.Drawn) : (tbKey QK wts rnd tk tt (.own n) k w h).2.words = tblW n := by
  have hc := sendings_count
  rw [tb_own]
  unfold tblW
  by_cases h1 : n < treesU QK
  · rw [if_pos h1, if_pos h1]
    exact send_words _ _ _ _ _ _ _ (of_atFull takes_two hK₀)
  · rw [if_neg h1, if_neg h1, if_pos (by omega)]
    exact send_words _ _ _ _ _ _ _ (of_atFull takes_five hK₀)

end

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

include hK₀ in
/-- **`RunPlays.old` at a stand of Thr at 9.** -/
theorem old_nine (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    {k : Coins (keyBook K₀)} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9 k s m E) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts (JN Xs K₁ B).p : Block T12 Unit).rounds, ∀ o ∈ d.opens,
      oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨⟨-, hH⟩, -, -, -, ⟨-, -, hsent, -⟩, -, -⟩ := u
  have e3 := trees_key Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest
    Kp Vd w e B
  rw [e3] at hsent
  have hp : (JN Xs K₁ B).p = piKUFull := place_full
  intro d hd o ho hO
  rw [hsent] at hO
  rw [hp] at hd
  have a2 := List.all_eq_true.1 (List.all_eq_true.1 wide_U d hd) o ho
  rw [hO] at a2
  cases hσ : o.2 with
  | own n =>
    rw [hσ] at a2 hO
    have hn : n < 3 := of_decide_eq_true hO
    have hw : o.1.W = tblW n := by simpa using a2
    have hin : Fmt.TreeSource.own n ∈
        (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hand 9 := by
      show _ ∈ [] ++ (List.range (treesTo _ 9)).map Fmt.TreeSource.own
      rw [e3]
      exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
    obtain ⟨pt, h1, h2⟩ := words_of_hand _ (hH _ hin)
    refine ⟨pt, h1, h2.trans ?_⟩
    rw [hw]
    show (tbKey (parKey Xs PF) wts rnd tk tt (.own n) k m.st.input _).2.words = _
    rw [e]
    exact table_words K₀ hK₀ wts rnd tk tt n hn k _ _
  | taken a b =>
    rw [hσ] at a2
    simp at a2

include hK₀ in
/-- **`Plays` at member 9, at keyBook, with no `PlaysOn` premise.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem plays_at_nine (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) = testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ) :
    Plays (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9 := by
  have hseat := (seat_nine Xs Nr PF K₁ ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w B).2
  have hblk := (seat_nine Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w B).1
  have hp : (JN Xs K₁ B).p = piKUFull := place_full
  obtain ⟨st0, st1, st2, hst⟩ : ∃ a b r, (JN Xs K₁ B).p.nums.stages = a :: b :: r := by
    have h2 : 2 ≤ (JN Xs K₁ B).p.nums.stages.length := by
      rw [hp]
      exact AtPublicFiles.KeyPlaysAt.stages_two
    cases hh : (JN Xs K₁ B).p.nums.stages with
    | nil =>
      rw [hh] at h2
      simp only [List.length_nil] at h2
      omega
    | cons a t =>
      cases t with
      | nil =>
        rw [hh] at h2
        simp only [List.length_cons, List.length_nil] at h2
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hle : st0.h ≤ st0.k := by
    refine hk_U st0 ?_
    rw [← hp, hst]
    exact List.mem_cons_self
  have hk : st0.k = (H2K.Pub.sgOf st0).h + (H2K.Pub.sgOf st0).g := by
    show st0.k = st0.h + (st0.k - st0.h)
    omega
  have hf : ((TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hs.find? fun g =>
      g.place == (JN Xs K₁ B).p.place) = some (proverSideOfProximityTest (JN Xs K₁ B)) := by
    rw [← hseat.place]
    exact find_U Xs K₁ B hs hsp
  refine plays_of_playsOn _ hblk (A := Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9)
    (B := fun _ _ _ _ => True) ?_ (fun _ _ _ _ h => h)
    (trees_nine_at Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hs hsp own₀ htt)
  refine playsOn_k12 _ (keyBook K₀) _ _ _ (H2K.JointK.keyGu PF) (JN Xs K₁ B) _ _ hseat _ _ st0 st1 st2
    hst hk hf 3 (PlanAtKey.planPlays_KU _ hp rfl st0 (st1 :: st2) hst) ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  intro k st m E ds c hA _ hc
  have e3 := trees_key Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest
    Kp Vd w e B
  have hsent : E.sent = 3 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := hA
    rw [h3, e3]
  refine ⟨?_, hsent, old_nine K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hA⟩
  exact agree_at_U K₀ hK₀ (ProofFile.Honest.K12.Light.jobLocU (X := X₀) ⟨parKey Xs PF, 0⟩
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U) (sentKey Xs PF)
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (keyProver K₁).storedWords
      (fun c => K₁.weights c.w₀) (fun c => randKey K₁ c.rc) none)
    place_full
    (by
      show memsOf (parKey Xs PF) = _
      rw [e]
      exact members_closed)
    (by
      rw [fresh_closed]
      rfl) _ _ c hc _ _

end

end AtPublicFiles.PlaysAtNine

#print axioms AtPublicFiles.PlaysAtNine.words_of_hand
#print axioms AtPublicFiles.PlaysAtNine.noTbl
#print axioms AtPublicFiles.PlaysAtNine.sent_words
#print axioms AtPublicFiles.PlaysAtNine.cut_some
#print axioms AtPublicFiles.PlaysAtNine.send_words
#print axioms AtPublicFiles.PlaysAtNine.tb_own
#print axioms AtPublicFiles.PlaysAtNine.table_words
#print axioms AtPublicFiles.PlaysAtNine.old_nine
#print axioms AtPublicFiles.PlaysAtNine.plays_at_nine
