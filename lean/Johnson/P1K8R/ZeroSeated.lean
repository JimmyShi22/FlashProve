-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroSeated.lean: THE MAKERS WHOSE SUB-PROTOCOLS ARE LAID INTO THE FIRST CHAIN's LINKS,
IN FRONT OF THE BATCHING: EACH DECISION STEPS IN `KeepsZero`. THE TERM OFF THE PLAN (shOfBuilt)
GIVES WAY TO ONE PREMISE ON THE PLAN, `okZero`: THE FOUR DECLARATIONS ON IT ARE TURNED BY HAND. MADE
BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksSeated.lean, WITH THE ROWS' FIRST
COLUMNS (`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN
THE PLACE OF KeepsLooks: every declaration of that file that names the looks, or leans on one that
does, under a new name; the others are called where they lie. None of the library's goals. No prover
stands in it; nothing on completeness, soundness or hiding.

  `okZero built`   the planned ledger of every built link has `AllZero`
  `frameAt_lettersZ`, `zeroAt_lettersZ`, `tailHead_kz`, **`frames_kz`**   every row of the frame,
      link by link, under `okZero`
  `k4C_kz`, `k8W_kz`, `k1Later_kz`, `quietAt_kz`   there: the same names with "steps" or "keeps"
  `readsLay_kz`, `readsHead_kz`, `readsAtt_kz`   the like
  `theOwn_kz`, `theWhole_kz`, **`theStated_kz`**   K3's sub-protocol at an address, where its test
      on the plan says yes
Limits. THE DECISIONS ALONE. `okZero` is a premise. K3's three stand under "the sub-protocol's test
on the plan says yes" (Johnson/P1K8R/ZeroVia.lean has them without). Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroK2
import Johnson.P1K8R.ZeroK3
import Johnson.P1K8R.ZeroK4
import Johnson.P1K8R.ZeroK5
import Johnson.P1K8R.ZeroK6
import Johnson.Desc.First.Link.Law.LooksSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- **The premise on the plan**: the planned ledger of every built link has it. -/
def okZero (built : Array Stages.LinkH) : Prop :=
  ∀ (m : ℕ) (X : Stages.LinkH), built[m]? = some X → AllZero X.Fp

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- The letters of link l are made of built[l]. -/
theorem frameAt_lettersZ {built : Array Stages.LinkH} {W : Verify.Public} {l : ℕ} {x : Par}
    (hz : okZero built) (h : frameAt built W l = some x) :
    match x with
    | .att P _ => AllZero P.X.Fp
    | .lay P => AllZero P.X.Fp := by
  unfold frameAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      exact hz _ _ hX
    · split at h
      · obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
        obtain rfl := Option.some.inj h
        exact hz _ _ hX
      · exact nomatch h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
theorem zeroAt_lettersZ {built : Array Stages.LinkH} {W : Verify.Public} {P : LayPar}
    (hz : okZero built) (h : zeroAt built W = some P) : AllZero P.X.Fp := by
  unfold zeroAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · exact nomatch h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact hz _ _ hX

/-- The end of the head's link is the frame's one clearing. -/
theorem tailHead_kz {X : Johnson.Desc.First.Walk.LinkPub} {lay : WsLay}
    {lin : Params.LinShape} {s t : S} (h : First.Close.tailHead X lay lin s = .ok t) :
    KeepsZero s t :=
  cleared_kz (X := X) (counts := First.Close.countsHead) (left := First.Close.leftHead)
    (row := fun masks w claims os => First.Pend.pendingRowO lay masks w claims lin os) h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **EVERY ROW OF THE FRAME, LINK BY LINK.** -/
theorem frames_kz {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (hz : okZero built) (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    (∀ s t, f.lay s = .ok t → KeepsZero s t) ∧
      (∀ s t, f.opened s = .ok t → KeepsZero s t) ∧
      ∀ s t, f.clear s = .ok t → KeepsZero s t := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fun _ _ k => laid_kz k, fun s t k => by cases k; exact kz_refl s,
        fun _ _ k => tailHead_kz k⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        exact ⟨fun _ _ k => laid_kz k,
          fun _ _ k => openLayZero_makesZ k (zeroAt_lettersZ hz hP),
          fun _ _ k => cleared_kz (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        have e2 := frameAt_lettersZ hz hP
        exact ⟨fun _ _ k => laid_kz k, fun _ _ k => openAtt_makesZ k e2,
          fun _ _ k => cleared_kz (X := P.X) (counts := countsAtt nLin)
            (left := fun _ => none) (row := rowOf W first) k⟩
      · rename_i P hP
        cases e
        have e2 := frameAt_lettersZ hz hP
        exact ⟨fun _ _ k => laid_kz k, fun _ _ k => openLay_makesZ k e2,
          fun _ _ k => cleared_kz (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩

/-! ## The kinds' makers as the lots seat them -/

section

theorem k4C_kz (p : OnBytes.Desc.First.K4.Par) :
    (OnBytes.Desc.First.K4.blockAtC p).Steps KeepsZero :=
  fun s rs gs s' h => k4_kz p s rs gs s' h

theorem k8W_kz (p : First.K8.ParW) : (First.K8.whole p).Steps KeepsZero :=
  fun s rs gs s' h => k8_kz (Cl := Claim) p.toPar s rs gs s' h

theorem k1Later_kz {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps KeepsZero :=
  k1_kz _ link moment arrays

theorem readsLay_kz (P : K8.ReadsQuiet.PG) :
    (K8.ReadsQuiet.layers P).Steps KeepsZero := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact kzL_same (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsHead_kz (P : K8.ReadsQuiet.PH) :
    (K8.ReadsQuiet.head P).Steps KeepsZero := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact kzL_same (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsAtt_kz {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : b.Steps KeepsZero := by
  unfold First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' e
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq (A := A) e
  exact kzL_same (by simp [S.fork?, ha]) (by simp [S.link?, ha])

/-- The steps without a round behind a lookup. -/
theorem quietAt_kz {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : KeepsZero s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → KeepsZero s t := by
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
      refine kzL_of_cases fun G' L' e1 e2 => Or.inr ⟨F, L', hF', ?_, rfl, ?_⟩
      · rw [← link_putFork s]
        exact e2
      · rw [fork_putFork s F hF'] at e1
        rw [← Option.some.inj e1]
    · exact nomatch hG'
  have hd : K3.quietHead X s = .ok t → KeepsZero s t := by
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
      exact kzL_same (by simp [S.fork?, ha]) (by simp [S.link?, ha])
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → KeepsZero s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact kz_refl s
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
theorem theOwn_kz {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) (hp : b.planOk = true) :
    b.Steps KeepsZero := by
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
      | true => exact via_kz_digits claim a.piece laid sent p [] hp' s rs gs s' e'
      | false => exact via_kz_calls claim a.piece laid sent p [] hp' s rs gs s' e'

/-- With the step without a round joined behind it. -/
theorem theWhole_kz {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) (hp : b.planOk = true) :
    b.Steps KeepsZero := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none =>
    simp only [hf] at hp ⊢
    exact theOwn_kz claim runs X codes shape a h0 hp
  | some f =>
    simp only [hf] at hp ⊢
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    have hp0 : b₀.planOk = true := (Bool.and_eq_true_iff.1 hp).1
    exact kzs_andThen _ _ _ (theOwn_kz claim runs X codes shape a h0 hp0)
      (steps_quiet _ _ _ _ f fun s t k => quietAt_kz hq k)

/-- **K3's sub-protocol at an address, whole, with its runs stated.** -/
theorem theStated_kz {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) (hp : b.planOk = true) :
    b.Steps KeepsZero := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact theWhole_kz claim true X codes shape a h0 hp
  · split at h
    · cases h
      exact theWhole_kz claim true X codes shape a h0 hp
    · split at h
      · cases h
        exact theWhole_kz claim true X codes shape a h0 hp
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact fun s rs gs s' e => theWhole_kz claim true X codes shape a h0 hp s rs gs s' e

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frameAt_lettersZ
#print axioms VerifiableInference.Desc.LinkJoin.zeroAt_lettersZ
#print axioms VerifiableInference.Desc.LinkJoin.tailHead_kz
#print axioms VerifiableInference.Desc.LinkJoin.frames_kz
#print axioms VerifiableInference.Desc.LinkJoin.k4C_kz
#print axioms VerifiableInference.Desc.LinkJoin.k8W_kz
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_kz
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_kz
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_kz
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_kz
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_kz
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_kz
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_kz
#print axioms VerifiableInference.Desc.LinkJoin.theStated_kz
