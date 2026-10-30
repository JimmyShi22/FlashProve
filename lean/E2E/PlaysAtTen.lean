-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/PlaysAtTen.lean

`PlaysS` AT MEMBER 10 OF THE KEY's SHARED THREAD, AT keyBook, AT ANY LETTER THAT HOLDS THE FIELD.

THE FORM. `PlaysS T Said 10`, general in `Said`, under hop: where `Said` holds at 10 the field is some.
L2's letter and L3's both feed it. The plain form is `Said := fun _ _ m => m.opened.isSome`. Bare `Plays`
at 10 is false wherever playable (`play_guarded_none`).

  `mems_at`, `fresh_at`   the job's members and word, at the chain's parameters
  `old_ten`        `RunPlays.old` at a stand of Thr at 10
  `plays_at_ten`   the statement

PREMISES, and who pays: as at member 9 (PlaysAtNine.lean), with h7 and htt: the arms at own 7 to 10, here
premises; hop: the letter's.

Limits.
- That `ThrS` stands, or that any letter at this thread has hop, is NOT said.
- A YES AT «SOME» IS A YES AT ANY COLUMNS. hop asks isSome alone. At m.opened = some [] or at wrong
  columns the job's door is `fallOmega` or another state's way in, and this law still holds: play returns
  and the trees are the tables', for the tables read rows₀, coins and the heard, not rec₀. So `PlaysS`
  at 10 says nothing on whether the prover plays off the verifier's state: that is `enters`'.
- hop has no E and no Thr: the form that L2's ∀ letter pays with Thr's own E is `plays_at_ten_thr`
  (PlaysAtLetters.lean). wts, rnd free: as at member 9; `plays_ten_real` there.
- A stand at 10 wants member 9 stepped: Accepted at U at the key: it is not shown.
- `PlaysS` at the half behind the guard; the plain half never stands in the thread's list here.
- No filling of tt is typed. At keyBook. Member 10 alone.
- Nothing on completeness, on soundness or on what is hidden.

NOT IN FRONT OF A LAW OVER COINS: `plays_at_ten` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from the pair (`ThrS`) as a premise, `PlaysS` as an end. None: the bar is flat.
-/
import E2E.PlaysAtNine
import E2E.PlaysAtTenGuards
import E2E.TreesAtTenKey
import E2E.KeyAgreeAt

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
open AtPublicFiles.KeySharedThread (threadKey parKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyFixedLines (trees_key_O)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega jobKO wtOf rdOf hk_O)
open AtPublicFiles.TreesAtNine (TN)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full JO find_O)
open AtPublicFiles.TreesAtTenKey (block_ten trees_ten_at)
open H2K.Member (piKOFull)
open H2K.JointK (keyOmega)

theorem mems_at {W₀ Rc X₀ : Type} (Q : _root_.Desc.K14.P14) (hq : Q = QK) (bs : List (Block St Unit))
    (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand) :
    (jobKO (X := X₀) ⟨Q, 0⟩ pU pO bs wts rnd).toRun.toTest.members =
      AtPublicFiles.KeyTest.jobOmega.members := by
  subst hq
  exact AtPublicFiles.KeyDepthsClosed.members_O

theorem fresh_at {W₀ Rc X₀ : Type} (Q : _root_.Desc.K14.P14) (hq : Q = QK) (bs : List (Block St Unit))
    (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand) :
    (jobKO (X := X₀) ⟨Q, 0⟩ pU pO bs wts rnd).toRun.toTest.fresh = AtPublicFiles.KeyTest.jobOmega.fresh := by
  subst hq
  exact AtPublicFiles.KeyDepthsClosed.fresh_O

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
/-- **`RunPlays.old` at a stand of Thr at 10.** -/
theorem old_ten (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    {k : Coins (keyBook K₀)} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 10 k s m E) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts (JO Xs K₁ B).p : Block T12 Unit).rounds, ∀ o ∈ d.opens,
      oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨⟨-, hH⟩, -, -, -, ⟨-, -, hsent, -⟩, -, -⟩ := u
  have e7 := trees_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt)
    rest Kp Vd w e B
  rw [e7] at hsent
  have hp : (JO Xs K₁ B).p = piKOFull := pO_full
  intro d hd o ho hO
  rw [hsent] at hO
  rw [hp] at hd
  have a2 := List.all_eq_true.1 (List.all_eq_true.1 wide_O d hd) o ho
  rw [hO] at a2
  cases hσ : o.2 with
  | own n =>
    rw [hσ] at a2
    obtain ⟨hn, hw⟩ : n < 3 ∧ o.1.W = tblW n := by simpa using a2
    have hin : Fmt.TreeSource.own n ∈
        (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hand 10 := by
      show _ ∈ [] ++ (List.range (treesTo _ 10)).map Fmt.TreeSource.own
      rw [e7]
      exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
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
/-- **`PlaysS` at member 10, at keyBook, at any letter that holds the field.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem plays_at_ten (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (h7 : tt 7 = ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true))
    (htt : ∀ τ, τ < 3 → tt (8 + τ) = testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) τ)
    (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hop : ∀ k m, Said 10 k m → m.opened.isSome = true) :
    PlaysS (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) Said 10 := by
  have hseat : SeatOf (keyOmega (PF.O.getD PF.U)) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave := by
    have h := seatOf_inside (Cl := Unit) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  have hblk := block_ten Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w B
  have hp : (JO Xs K₁ B).p = piKOFull := pO_full
  obtain ⟨st0, st1, st2, hst⟩ : ∃ a b r, (JO Xs K₁ B).p.nums.stages = a :: b :: r := by
    have h2 : (JO Xs K₁ B).p.nums.stages.length = 4 := by
      rw [hp]
      exact AtPublicFiles.KeyLay.len_O
    cases hh : (JO Xs K₁ B).p.nums.stages with
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
    refine hk_O st0 ?_
    rw [← hp, hst]
    exact List.mem_cons_self
  have hk : st0.k = (H2K.Pub.sgOf st0).h + (H2K.Pub.sgOf st0).g := by
    show st0.k = st0.h + (st0.k - st0.h)
    omega
  have hplace : ((proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀).place ==
      (JO Xs K₁ B).p.place) = true := beq_self_eq_true _
  have f1 : ([(proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀)].find? fun g =>
      g.place == (JO Xs K₁ B).p.place) = some (proverSideOfProximityTest (JO Xs K₁ B)) := by
    simp [List.find?, hplace]
  have f2 : ([(proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀)].find? fun g =>
      g.place == (keyOmega (PF.O.getD PF.U)).place) = some (proverSideOfProximityTest (JO Xs K₁ B)) := by
    rw [hseat.place]
    exact f1
  have P0 : PlaysOn (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).φ
      (keyBook K₀) (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).chain
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).ft
      [proverSideOfProximityTest (JO Xs K₁ B)] (keyOmega (PF.O.getD PF.U))
      (fun k s m E => Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 10 k s m E ∧
        m.opened.isSome = true) (fun _ _ _ _ => True) := by
    refine playsOn_k12 _ (keyBook K₀) _ _ _ (keyOmega (PF.O.getD PF.U)) (JO Xs K₁ B) _ _ hseat _ _ st0
      st1 st2 hst hk f1 7 (PlanAtKey.planPlays_KO _ hp rfl st0 (st1 :: st2) hst) ?_
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    intro k st m E ds c hA _ hc
    have e7 := trees_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt)
      rest Kp Vd w e B
    have hsent : E.sent = 7 := by
      obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := hA.1
      rw [h3, e7]
    refine ⟨?_, hsent, old_ten K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hA.1⟩
    exact agree_at_O K₀ hK₀ (jobKO (X := X₀) ⟨parKey Xs PF, 0⟩ pU pO
        [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (wtOf K₁) (rdOf K₁))
      pO_full (mems_at _ e _ _ _) (fresh_at _ e _ _ _) _ _ c hc _ _
  have P1 := playsOn_guarded (hs := (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hs)
    (proverSideOfProximityTest (JO Xs K₁ B)) (find_O Xs K₁ B hs hsp) f2 (fun _ _ _ _ h => h.2) P0
  intro blk hblk' k s m E ds l hS hd hst' hl
  obtain rfl : blk = keyOmega (PF.O.getD PF.U) := Option.some.inj (hblk'.symm.trans hblk)
  obtain ⟨y, cols, hy, hc, -⟩ := P1 k s m E ds l ⟨hS.1, hop _ _ hS.2⟩ hd hst' hl
  have hMv : (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Moved
      (keyOmega (PF.O.getD PF.U)) k m E ds y cols := ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨y, cols, hMv, trees_ten_at Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hs hsp own₀ h7 htt
    k s m E ds y cols hS.1 (hop _ _ hS.2) hd hMv⟩

end

end AtPublicFiles.PlaysAtNine

#print axioms AtPublicFiles.PlaysAtNine.mems_at
#print axioms AtPublicFiles.PlaysAtNine.fresh_at
#print axioms AtPublicFiles.PlaysAtNine.old_ten
#print axioms AtPublicFiles.PlaysAtNine.plays_at_ten
