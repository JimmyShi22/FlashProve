-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UAccepted.lean: the frame's sentence «it is accepted» at member 9 of a
shared thread of the key file, the proximity test on G_u: the five fields of `K12At` (K12/SaysYesK12.lean) put
together.

  `says_at_key`      `SaysAt` where the thread's invariant holds at border 9, at every row of coins that the
                     book lends the test's two parts
  `fields_at_key`    `K12At` there
  `accepted_at_key`  `Accepted` (Honest/Thread/Pays.lean) at member 9, at any falls
  `acceptedS_at_key`   `AcceptedS` (Honest/Thread/PaysS.lean), at any second condition `Said`

The thread: `TU` (E2E/TableFilled.lean), one `threadKey` (E2E/KeySharedThread.lean). What is fixed in it:
  the later places `PF` and, by e, the parameters `QK`: the written key's size alone;
  the book `keyBook K₀`;
  the two tests' halves: `withTestsOnUAndOmega K₁ pU pO` lays them into the parts, whatever the parts held there;
  the table `tbKey` at the parts' own readers `K₁.weights`, `randKey K₁`: the trees 0 to 2 are the two sendings';
  the job has no reader of its own for u;
  one input: the thread's `valid` says v = w and Vd v.
What is free: the types; ℓ, Nm, Mg₀, tk, rest, Kp, Vd, w; the table's letter tt for the tests' own trees, which
nothing at member 9's acceptance reads; B, any eight that the parameters make; `Said`, the falls.

Premises, and what pays them in scope. hK₀: `full_made`. e: `par_sourced` with `later_sourced`. hQ: `plan_key`.
hs, hsp: the parts send at these parameters, and their linear claim's shape splits: by rfl and `hQ.facts.two`
at `keyOf` (E2E/KeyStandMember.lean).

Two steps that hold by unfolding. `words_tied_nine` ends at `carriedCoins`, `saysAt_nine` asks at `restCoins`:
the two part in the field `rest` alone, and `plainMany` reads `mem`, `hide` and `tails`. The job reads of the
parts their stored words, weights and coins' reader; `withTestsOnUAndOmega` writes the two halves alone.

At border 9 the job's state on entry is the verifier's own state: `enters_nine` (E2E/KeyDoorNine.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): the thread's
  invariant is a premise.
- That the invariant holds at border 9 at any run is not said here: UStep.lean.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UAccepts
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtTest
import E2E.WordsTiedTop
import E2E.TreesSentBeforeTestAtNine
import E2E.PlaysAtNine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (SaysAt)
open ProofFile.Honest.K12.Light.ItemLaws (AN saysAt_nine)
open ProofFile.Honest.K12.Light.WordsTiedNine (words_tied_nine)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (opens_U opensAtU)
open ProofFile.Honest.K12.AtFile (acceptedS_at_test)
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
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyDoorNine (jobNine seat_nine enters_nine)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyFixedLines (trees_key)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega hk_U)
open AtPublicFiles.KeyPlaysAt (memsOf members_closed fresh_closed)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.HalvesAreJobs (pU pO find_U)
open AtPublicFiles.TableFilled (TU)
open AtPublicFiles.OldAtNine (oldAt_nine depths_place)
open H2K.Member (piKUFull)

variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include hK₀ in
/-- **`SaysAt` at a stand, at every coin lent.** -/
theorem says_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E)
    (c : RowCoins [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JN Xs K₁ B).p.place
      [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)] 0 = .ok c) :
    SaysAt (AN (X₀ := X₀) Xs K₁ B) m.st.input (frontOf m) (restCoins (JN Xs K₁ B) c.2.1) :=
  saysAt_nine K₀ Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ _ rest Kp Vd w hQ e B u [] _
    (words_tied_nine K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ u [] c.2.1
      (lendRow_second hc))

include hK₀ in
/-- **`K12At` at a stand.** -/
theorem fields_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E) (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts (JN Xs K₁ B).p : Block T12 Unit).rounds ds = true)
    (c : RowCoins [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JN Xs K₁ B).p.place
      [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)] 0 = .ok c) :
    K12At (JN Xs K₁ B) (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave s m E ds c := by
  have hp : (JN Xs K₁ B).p = piKUFull := place_full
  have e3 := trees_key Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w e B
  have hsent : E.sent = 3 := by
    have h := u.2.2.2.2.1.2.2.1
    exact h.trans e3
  obtain ⟨st0, rest0, hst⟩ : ∃ a r, (JN Xs K₁ B).p.nums.stages = a :: r := by
    have h2 : 2 ≤ (JN Xs K₁ B).p.nums.stages.length := by
      rw [hp]
      exact AtPublicFiles.KeyPlaysAt.stages_two
    cases hh : (JN Xs K₁ B).p.nums.stages with
    | nil =>
      rw [hh] at h2
      simp only [List.length_nil] at h2
      omega
    | cons a t => exact ⟨a, t, rfl⟩
  have hL : LinesAt (parKey Xs PF) pU := by
    rw [e, show pU = piKUFull from place_full]
    exact lines_at_key
  have hpl : ∀ b ∈ [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8], b.planOk = true :=
    eight_plan_at_key (e ▸ B.made)
  obtain ⟨t', ht'⟩ := accepts_of_lines (fun c : Common W₀ Rc TableKey => c.key)
    (fun c (fr : Front X₀) =>
      ProofFile.Honest.K12.Light.colsLoc (parKey Xs PF) ((keyProver K₁).storedWords c.w₀ c.rc) fr.seen.rounds)
    (fun c => K₁.weights c.w₀) (fun c => randKey K₁ c.rc) none hL B.made hpl m.st.input (frontOf m)
    (restCoins (JN Xs K₁ B) c.2.1) ds hd
    (says_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ u c hc)
  exact
    { agree := agree_at_U K₀ hK₀ (AN (X₀ := X₀) Xs K₁ B) place_full
        (by
          show memsOf (parKey Xs PF) = _
          rw [e]
          exact members_closed)
        (by
          rw [fresh_closed]
          rfl) _ _ c hc _ _
      count := (length_test (JN Xs K₁ B) _ _ _ _).trans
        (PlanAtKey.planPlays_KU (JN Xs K₁ B) hp rfl st0 rest0 hst).count
      opens := ⟨[24, 13], fun j => [Fmt.TreeSource.own 0, .own 2].getD j (.own 0), by
          show [ProofFile.Honest.K12.Light.depthOf pU 0, ProofFile.Honest.K12.Light.depthOf pU 1] = [24, 13]
          rw [show pU = piKUFull from place_full, depths_place.1, depths_place.2], by
          rw [hsent]
          refine opensFit_of_B (JN Xs K₁ B) _ [24, 13] [.own 0, .own 2] 3 ?_
          rw [hp]
          exact opens_U,
        oldAt_nine K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e u c hc⟩
      enters := enters_nine Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ _ rest Kp Vd w hQ B u
      accepts := ⟨t', ht', _, rfl⟩ }

include hK₀ B in
/-- **It is accepted, at member 9**: `Accepted` (Honest/Thread/Pays.lean), from the thread's invariant alone,
at any falls: no list that fits is excepted. -/
theorem accepted_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (fall : ℕ → St → List Fmt.Drawn → Option String) :
    Accepted (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) fall 9 := by
  have hseat := (seat_nine Xs Nr PF K₁ ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w B).2
  have hblk := (seat_nine Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w B).1
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
  have hf : ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).hs.find? fun g =>
      g.place == (JN Xs K₁ B).p.place) = some (proverSideOfProximityTest (JN Xs K₁ B)) := by
    rw [← hseat.place]
    exact find_U Xs K₁ B hs hsp
  have h : AcceptedS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) (fun _ _ _ => True) fall 9 := by
    refine acceptedS_at_test _ _ hblk (JN Xs K₁ B) _ _ hseat st0 st1 st2 hst hk hf fall ?_
    intro k s m E ds c u hd _ hc
    exact fields_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ u.1 ds hd c hc
  exact fun blk hb k s m E ds y cols hA => h blk hb k s m E ds y cols ⟨hA, trivial⟩

include hK₀ B in
/-- The same from the thread's pair, at any second condition. -/
theorem acceptedS_at_key (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    AcceptedS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said fall 9 :=
  acceptedS_of _ Said (accepted_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ hs hsp fall)

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.says_at_key
#print axioms ProofFile.Honest.K12.AtKey.fields_at_key
#print axioms ProofFile.Honest.K12.AtKey.accepted_at_key
#print axioms ProofFile.Honest.K12.AtKey.acceptedS_at_key
