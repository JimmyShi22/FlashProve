-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyPlaysAt.lean: `not_plays` (E2E/KeyFreshTreePlace.lean) at a term: the test on G_u's own half, whose steps
the book lays, so the premises of that statement are met.

Why. «False wherever playable» is empty if nothing is playable. At the halves with no part of
E2E/KeyPartsIdle.lean `chainSteps` errs at the member. Here it returns. That the half's `play` returns is not
shown here: `Moved` at this job is shown by nothing. `Plays` gives it, and the contradiction starts from
that.

Main names.
  `lays_same`: the book's test `laysB` reads of a job its numbers, members and word on the fresh table.
  `find_of_nodup`: in a list with no two alike, the first with a value is that one.
  `not_plays_at`: THE STATEMENT: at `VerifierAndGoals.storedPublicFiles`, no premise but the value `Z₀` and `Kp` with its two: there are
    parts whose `onU` is `proverSideOfProximityTest` of the job at which `Plays` at 9 of the key's thread does not hold, at the
    table's letter set to `oldArm`, the text before it had a letter. At another letter it does not speak. The
    statement names `onU` alone; the proof's other fields are those of E2E/KeyPartsIdle.lean.

What this is. `Plays` at 9 fails at ONE term: these parts, `oldArm`, and the stand at the default coins, with
`Said` laid at True: of that stand the proof spends `Thr` alone. The
table that the thread names for the test's first own tree gives «send o_omega»'s place, and the step
would not. The place is a sufficient reason there; it is not shown to be the only one, and right
tables alone are not shown to give `Plays`. It says
nothing of what the prover sends, and nothing on acceptance. By our reading the mismatch lies in the
thread's tables, not in the test; no statement here shows that. The other letters are as idle as in
`stand_nine_full`: the other halves, the items on the stored table, and the public part `pubKey Z₀`. It
proposes no mend.

NOT IN FRONT OF A LAW OVER COINS: `not_plays_at` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: as at `stand_nine`, at the default coins. None: the
bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyFreshTreePlace
import E2E.KeyNineClosed
import E2E.KeyStandNineFull
import Johnson.Desc.ProofFile.Honest.K12.HalfReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyPlaysAt
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made foldedTestPlace omegaTestPlace of_atFull)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeySharedThread (threadKey parKey sentKey randKey plan_key)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleTk idleRest kFull idleNm_tenant)
open AtPublicFiles.KeyStandMember (keyOf fitOf)
open AtPublicFiles.KeyStandNineAt (stand_nine lists_nine)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts idleWhere idle_quiet)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyDoorNine (jobNine seat_nine)
open AtPublicFiles.KeyFreshTrial (not_plays oldArm)
open AtPublicFiles.KeyNineClosed (place_full lays_full)
open AtPublicFiles.KeyTest (jobFolded)
open Bind.ForProver (shapeOf oodSh Seed)
open H2K.Member (piKUFull)

/-- The book's test reads of a job its numbers, members and word on the fresh table. -/
theorem lays_same {W X W' X' : Type} (B : ProverCoinCounts) (ch : Nat) (J : TestJob W X) (J' : TestJob W' X')
    (a : Addr × Nat) (hp : J.p = J'.p) (hm : J.members = J'.members) (hf : J.fresh = some a)
    (hf' : J'.fresh = some a) : laysB B ch J = laysB B ch J' := by
  cases J
  cases J'
  dsimp only at hp hm hf hf'
  subst hp
  subst hm
  subst hf
  subst hf'
  rfl

/-- The maker's members at a chain's parameters, public. -/
def memsOf (Q : _root_.Desc.K14.P14) : List (Addr × Nat × Due) :=
  [(⟨sendPlace 2, 0⟩, 0, ⟨0, dueOf (jobU ⟨Q, 0⟩).Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape
      ((jobU ⟨Q, 0⟩).sort 0)⟩),
   (⟨sendPlace 5, 0⟩, 1, ⟨0, dueOf (jobOmega ⟨Q, 0⟩).Q.codes
      ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape ((jobOmega ⟨Q, 0⟩).sort 1)⟩)]

theorem members_closed : memsOf QK = jobFolded.members := by
  decide +kernel

theorem fresh_closed : jobFolded.fresh = some (⟨sendPlace 2, 0⟩, 1) := by
  decide +kernel

theorem place_on : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U).place = foldedTestPlace := by
  rw [place_full]
  decide +kernel

theorem stages_two : 2 ≤ piKUFull.nums.stages.length := by
  decide +kernel

theorem fit_gu : drawsFit (H2K.JointK.keyGu PF).rounds ((H2K.JointK.keyGu PF).rounds.map fitOf) = true := by
  decide +kernel

theorem find_of_nodup {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) {g : α} :
    ∀ (l : List α), g ∈ l → (l.map f).Nodup → l.find? (fun h => f h == f g) = some g
  | [], hm, _ => by cases hm
  | a :: t, hm, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases e : f a = f g
    · have hag : a = g := by
        rcases List.mem_cons.1 hm with rfl | h
        · rfl
        · exact absurd (e ▸ List.mem_map_of_mem h) hn.1
      rw [List.find?_cons, beq_iff_eq.2 e]
      rw [hag]
    · have hg : g ∈ t := by
        rcases List.mem_cons.1 hm with rfl | h
        · exact absurd rfl e
        · exact h
      rw [List.find?_cons, show (f a == f g) = false from beq_false_of_ne e]
      exact find_of_nodup f t hg hn.2

/-- **THE STATEMENT.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem not_plays_at (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub),
      KeySourced VerifierAndGoals.storedPublicFiles Xs Nr Pl ∧ fullPub = some K₀ ∧
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ) (Kp : Nat → St → St → Prop),
        (∀ b ∈ [0, 11], ∀ s, Kp b s s) → (∀ s s', Kp 0 s s' → s' = s) →
        ∃ (B : Eight (parKey Xs Pl)) (Kx : KeyParts Weights (ℕ → TableRand) Unit Unit Unit),
          Kx.onU = proverSideOfProximityTest (jobNine (X₀ := Unit) Xs Pl (kFull Z₀ Xs Pl fc) B) ∧
          ¬ Plays (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl Kx id id) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl Kx id id) idleTk
            (oldArm (parKey Xs Pl) (keyOf (pubKey Z₀ Xs.chains) Xs Pl Kx id id).weights
            (randKey (keyOf (pubKey Z₀ Xs.chains) Xs Pl Kx id id))))
          idleRest Kp
          (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)) 9 := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := full_made
  refine ⟨Xs, Nr, Pl, K₀, hs, hK₀, fun fc w₀ rc sd Kp hKp hE => ?_⟩
  obtain ⟨layO, hQ⟩ := plan_key hs VerifierAndGoals.inScope_full
  obtain ⟨B⟩ := hQ.eight
  have e : parKey Xs Pl = QK := par_sourced hs VerifierAndGoals.inScope_full
  have hPl : Pl = PF := later_sourced hs VerifierAndGoals.inScope_full
  subst hPl
  obtain ⟨qr, -, qO, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
    (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
  let J := jobNine (X₀ := Unit) Xs PF (kFull Z₀ Xs PF fc) B
  let Kx : KeyParts Weights (ℕ → TableRand) Unit Unit Unit :=
    { fixedKeyParts fc idleWhere ⟨fun _ _ => 0⟩ () () () with onU := proverSideOfProximityTest J }
  refine ⟨B, Kx, rfl, ?_⟩
  have qU : AtPublicFiles.Stops.QuietHalf Kx.onU := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact first_quiet J
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact rest_quiet J
      · cases hp
  have pU : Kx.onU.place = foldedTestPlace := place_on
  obtain ⟨ds₁, ds₂, ds₄, ds₅, ds₇, ds₈, h₁, h₂, h₄, h₅, h₇, h₈⟩ :=
    lists_nine Xs Nr PF K₀ Kx WitLens.words idleNm (fun _ => idleMg) idleTk
      (oldArm (parKey Xs PF) (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id).weights (randKey (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id))) idleRest Kp (fun _ => True) id id Z₀ w₀ rc _ hs
      VerifierAndGoals.inScope_full sd rfl pU rfl
  obtain ⟨s, m, E, u, -⟩ := stand_nine Xs Nr PF K₀ Kx WitLens.words idleNm (fun _ => idleMg) idleTk
    (oldArm (parKey Xs PF) (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id).weights (randKey (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id))) idleRest Kp (fun _ => True) (fun _ _ _ => True) none
    id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full hK₀ sd rfl idleNm_tenant (fun _ _ _ _ => trivial) hKp hE trivial
    qr qU qO qw pU rfl default ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ h₁ h₂ h₄ h₅ h₇ h₈ trivial
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  have hlays : laysB (keyBook K₀) 1 J = true := by
    rw [lays_same (keyBook K₀) 1 J ({ jobFolded with p := piKUFull } : TestJob Unit Unit)
      (⟨sendPlace 2, 0⟩, 1) place_full ?_ rfl fresh_closed]
    · exact of_atFull lays_full hK₀
    · show memsOf (parKey Xs PF) = _
      rw [e]
      exact members_closed
  obtain ⟨st0, st1, st2, hst⟩ : ∃ a b r, J.p.nums.stages = a :: b :: r := by
    have h2 : 2 ≤ J.p.nums.stages.length := by
      show 2 ≤ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U).nums.stages.length
      rw [place_full]
      exact stages_two
    cases hh : J.p.nums.stages with
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
  have hsp : (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id).lin.S.sharedSplitNeeded = true := hQ.facts.two
  have hnd : ((keyProver (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id)).shared.map (·.place)).Nodup := by
    rw [keyProver_shared _ hsp]
    show [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      Kx.onU.place, (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit)
        (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()).onOmega.place].Nodup
    have pO : (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit)
        (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()).onOmega.place = omegaTestPlace := rfl
    rw [pU, pO]
    decide
  have hfind := find_of_nodup (·.place)
    (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id)).shared
    (List.mem_append_right _ List.mem_cons_self) hnd
  have hno := (AtPublicFiles.KeyFile.noStopAll_keyProver (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id) qr qU qO qw).2.1
  obtain ⟨c, -, hsteps⟩ := lays_of_B (keyBook K₀) 1 (Or.inr rfl) J st0 st1 st2 hst hlays
    (H2K.JointK.keyGu PF) (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave
    (seat_nine Xs Nr PF (kFull Z₀ Xs PF fc) WitLens.words idleNm (fun _ => idleMg)
      (tableKey Xs PF K₀ (kFull Z₀ Xs PF fc) idleTk
        (oldArm (parKey Xs PF) (kFull Z₀ Xs PF fc).weights (randKey (kFull Z₀ Xs PF fc)))) idleRest Kp
      (fun _ => True)
      (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩) B).2
    (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id)).shared hfind default none
  exact not_plays Xs Nr PF K₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF Kx id id) WitLens.words idleNm
    (fun _ => idleMg) idleTk idleRest Kp (fun _ => True) _ hs VerifierAndGoals.inScope_full hQ B
    (ds := (H2K.JointK.keyGu PF).rounds.map fitOf) u.1 fit_gu
    (AtPublicFiles.Stops.chainStopAt_none _ hno [_] _ _) hsteps

end AtPublicFiles.KeyPlaysAt

#print axioms AtPublicFiles.KeyPlaysAt.lays_same
#print axioms AtPublicFiles.KeyPlaysAt.members_closed
#print axioms AtPublicFiles.KeyPlaysAt.fresh_closed
#print axioms AtPublicFiles.KeyPlaysAt.place_on
#print axioms AtPublicFiles.KeyPlaysAt.stages_two
#print axioms AtPublicFiles.KeyPlaysAt.fit_gu
#print axioms AtPublicFiles.KeyPlaysAt.find_of_nodup
#print axioms AtPublicFiles.KeyPlaysAt.not_plays_at
