-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksSeated.lean: THE MAKERS WHOSE SUB-PROTOCOLS THE KINDS' LOTS LAY
INTO
THE FIRST CHAIN's LINKS (the list of Johnson/Goal/Meaning/RecSeated.lean), IN FRONT OF THE BATCHING:
EACH STEPS IN `KeepsLooks` (Johnson/Desc/First/Link/Law/LooksWalk.lean), AT ONE TERM OFF THE PLAN
FOR
ALL LINKS. Definitions and theorems: joinings of the kinds' shares.

  `shOfBuilt built m`: **THE TERM OFF THE PLAN**: the looks of the planned arrays of link m's public
    structure (`Stages.LinkH.Fp`); the empty list where there is no such link.
  `frames_keep`: **every row of the frame, link by link (`Walk.Seat.framesOf built first W`): its
    «laid», «opened» and «cleared» pass `LooksInv (shOfBuilt built)`: NO PREMISE ON shOf IS LEFT**:
    the letters of link l are made of built[l] (`frameAt`, `zeroAt`).
  `k4C_steps` (K4.blockAtC) · `k8W_steps` (K8.whole) · `k1Later_steps` (K1.laterAt) ·
    `readsLay_steps`, `readsHead_steps`, `readsAtt_steps` (the steps without a round behind the
    reads'
    sending) · `quietAt_keeps` (the steps without a round behind a lookup) · `theOwn_steps`,
    `theWhole_steps`, `theStated_steps` (K3's sub-protocol at an address, whole, WHERE ITS TEST ON
    THE PLAN SAYS YES).
  Beside these: `k5_steps_at` (LooksK5.lean) · `k6_steps_seated` (LooksK6.lean) · `k11_steps`,
    `k7_steps` (LooksFrame.lean) · `k2_steps`, `placeH2_makes` (LooksK2.lean).
A TWIN, SAID: the lookups' files name laws `stated_steps_*` and `quietAt_frame`
(Johnson/Desc/First/Look/K3StatedSteps.lean), which this file does not import:
`theStated_steps` is to be held against them.
Limits. THE DECISIONS ALONE. That the IOP's own sub-protocols stand under these makers is the seats'
tie (`steps_under`). At the head's link `placeH2_makes`' premise on the plan stays: P.l and P.X are
that place's letters. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksK2
import Johnson.Desc.First.Link.Law.LooksK3
import Johnson.Desc.First.Link.Law.LooksK4
import Johnson.Desc.First.Link.Law.LooksK5
import Johnson.Desc.First.Link.Law.LooksK6
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.K1.Places
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Top.H0.Walk.FrameLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **The term off the plan**: the looks of link m's planned arrays. -/
def shOfBuilt (built : Array Stages.LinkH) (m : ℕ) : List Look :=
  ((built[m]?).map fun X => X.Fp.trees.toList.map look).getD []

theorem shOfBuilt_at {built : Array Stages.LinkH} {m : ℕ} {X : Stages.LinkH}
    (h : built[m]? = some X) : shOfBuilt built m = X.Fp.trees.toList.map look := by
  unfold shOfBuilt
  rw [h]
  rfl

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- The letters of link l are made of built[l]. -/
theorem frameAt_letters {built : Array Stages.LinkH} {W : Verify.Public} {l : ℕ} {x : Par}
    (h : frameAt built W l = some x) :
    match x with
    | .att P _ => P.l = l ∧ shOfBuilt built l = P.X.Fp.trees.toList.map look
    | .lay P => P.l = l ∧ shOfBuilt built l = P.X.Fp.trees.toList.map look := by
  unfold frameAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, shOfBuilt_at hX⟩
    · split at h
      · obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, shOfBuilt_at hX⟩
      · exact nomatch h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
theorem zeroAt_letters {built : Array Stages.LinkH} {W : Verify.Public} {P : LayPar}
    (h : zeroAt built W = some P) : shOfBuilt built 0 = P.X.Fp.trees.toList.map look := by
  unfold zeroAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · exact nomatch h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact shOfBuilt_at hX

/-- The end of the head's link is the frame's one clearing. -/
theorem tailHead_keeps (shOf : ℕ → List Look) {X : Johnson.Desc.First.Walk.LinkPub} {lay : WsLay}
    {lin : Params.LinShape} {s t : S} (h : First.Close.tailHead X lay lin s = .ok t) :
    KeepsLooks shOf s t :=
  cleared_keeps shOf (X := X) (counts := First.Close.countsHead) (left := First.Close.leftHead)
    (row := fun masks w claims os => First.Pend.pendingRowO lay masks w claims lin os) h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **EVERY ROW OF THE FRAME, LINK BY LINK.** -/
theorem frames_keep {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    (∀ s t, f.lay s = .ok t → KeepsLooks (shOfBuilt built) s t) ∧
      (∀ s t, f.opened s = .ok t → KeepsLooks (shOfBuilt built) s t) ∧
      ∀ s t, f.clear s = .ok t → KeepsLooks (shOfBuilt built) s t := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fun _ _ k => laid_keeps _ k, fun s t k => by cases k; exact keeps_refl _ s,
        fun _ _ k => tailHead_keeps _ k⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        exact ⟨fun _ _ k => laid_keeps _ k,
          fun _ _ k => openLayZero_makes _ k (zeroAt_letters hP),
          fun _ _ k => cleared_keeps _ (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        obtain ⟨e1, e2⟩ := frameAt_letters hP
        exact ⟨fun _ _ k => laid_keeps _ k, fun _ _ k => openAtt_makes _ k (by rw [e1]; exact e2),
          fun _ _ k => cleared_keeps _ (X := P.X) (counts := countsAtt nLin)
            (left := fun _ => none) (row := rowOf W first) k⟩
      · rename_i P hP
        cases e
        obtain ⟨e1, e2⟩ := frameAt_letters hP
        exact ⟨fun _ _ k => laid_keeps _ k, fun _ _ k => openLay_makes _ k (by rw [e1]; exact e2),
          fun _ _ k => cleared_keeps _ (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩

/-! ## The kinds' makers as the lots seat them -/

section
variable (shOf : ℕ → List Look)

theorem k4C_steps (p : OnBytes.Desc.First.K4.Par) :
    (OnBytes.Desc.First.K4.blockAtC p).Steps (KeepsLooks shOf) :=
  fun s rs gs s' h => k4_steps shOf p s rs gs s' h

theorem k8W_steps (p : First.K8.ParW) : (First.K8.whole p).Steps (KeepsLooks shOf) :=
  fun s rs gs s' h => k8_steps (Cl := Claim) shOf p.toPar s rs gs s' h

theorem k1Later_steps {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps (KeepsLooks shOf) :=
  k1_steps shOf _ link moment arrays

theorem readsLay_steps (P : K8.ReadsQuiet.PG) :
    (K8.ReadsQuiet.layers P).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact keeps_same shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsHead_steps (P : K8.ReadsQuiet.PH) :
    (K8.ReadsQuiet.head P).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact keeps_same shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsAtt_steps {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : b.Steps (KeepsLooks shOf) := by
  unfold First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' e
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq (A := A) e
  exact keeps_same shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

/-- The steps without a round behind a lookup. -/
theorem quietAt_keeps {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : KeepsLooks shOf s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → KeepsLooks shOf s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, hF, k⟩ := K9L.ok_bind k
    obtain ⟨G, hG, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    have hF' := named_some hF
    have hG' := named_some hG
    unfold First.Look.slotsTaken at hG'
    split at hG'
    · obtain rfl := Option.some.inj hG'
      refine keeps_of_cases shOf fun G' L' e1 e2 => Or.inr ⟨F, L', hF', ?_, rfl, ?_⟩
      · rw [← link_putFork s]
        exact e2
      · rw [fork_putFork s F hF'] at e1
        rw [← Option.some.inj e1]
    · exact nomatch hG'
  have hd : K3.quietHead X s = .ok t → KeepsLooks shOf s t := by
    intro k
    unfold K3.quietHead at k
    split at k
    · rename_i a ha
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain rfl := Except.ok.inj k
      exact keeps_same shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → KeepsLooks shOf s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact keeps_refl shOf s
  unfold K3.quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact dig _ _ h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact hd h
         | exact lk _ h)
    | cases hf

/-- K3's own sub-protocol at an address, where its test on the plan says yes. -/
theorem theOwn_steps {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) (hp : b.planOk = true) :
    b.Steps (KeepsLooks shOf) := by
  unfold K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have hp' : (K3.Law.blockVia (if digits = true then K3.seatDigits claim else K3.seatCalls
          claim)
          a.piece laid sent p []).planOk = true := by
        cases runs <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.and_eq_true] at hp <;>
          exact hp.1
      intro s rs gs s' e
      have e' : (K3.Law.blockVia (if digits = true then K3.seatDigits claim else K3.seatCalls claim)
          a.piece laid sent p []).decide s rs gs = .ok s' := by
        cases runs <;> exact e
      cases digits with
      | true => exact via_steps_digits shOf claim a.piece laid sent p [] hp' s rs gs s' e'
      | false => exact via_steps_calls shOf claim a.piece laid sent p [] hp' s rs gs s' e'

/-- With the step without a round joined behind it. -/
theorem theWhole_steps {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) (hp : b.planOk = true) :
    b.Steps (KeepsLooks shOf) := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none =>
    simp only [hf] at hp ⊢
    exact theOwn_steps shOf claim runs X codes shape a h0 hp
  | some f =>
    simp only [hf] at hp ⊢
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    have hp0 : b₀.planOk = true := (Bool.and_eq_true_iff.1 hp).1
    exact steps_andThen shOf _ _ _ (theOwn_steps shOf claim runs X codes shape a h0 hp0)
      (steps_quiet _ _ _ _ f fun s t k => quietAt_keeps shOf hq k)

/-- **K3's sub-protocol at an address, whole, with its runs stated.** -/
theorem theStated_steps {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) (hp : b.planOk = true) :
    b.Steps (KeepsLooks shOf) := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact theWhole_steps shOf claim true X codes shape a h0 hp
  · split at h
    · cases h
      exact theWhole_steps shOf claim true X codes shape a h0 hp
    · split at h
      · cases h
        exact theWhole_steps shOf claim true X codes shape a h0 hp
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact fun s rs gs s' e => theWhole_steps shOf claim true X codes shape a h0 hp s rs gs s' e

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frames_keep
#print axioms VerifiableInference.Desc.LinkJoin.k4C_steps
#print axioms VerifiableInference.Desc.LinkJoin.k8W_steps
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_steps
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_steps
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_steps
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_steps
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_keeps
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_steps
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_steps
#print axioms VerifiableInference.Desc.LinkJoin.theStated_steps
