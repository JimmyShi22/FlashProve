-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/SaysAtNine.lean

`SaysAt` AT THE TEST ON G_u OF THE KEY's SHARED THREAD, AT A STAND OF Thr AT 9, AS FAR AS IT GOES WITHOUT
`WordsTied`, which stays a premise (hw).

  `AN`             the many-member job behind `jobNine`
  `rec_nine`       at a stand the state on entry reads the thread's statement and group: `enters_nine`
  `members_of_shape`, `members_nine`   the group under test has the members 0 and 3: by the shape, so
                   not through the plain fold that `enters_nine` drops
  `rows_nine`      the group's row count, from Form at 9
  `samples_of_smp`, `open_of_rowsOn`   the items in the forms that `saysAt_of_items` takes
  `saysAt_nine`    the statement

PREMISES. hQ: `plan_key`. e: `par_sourced`. B: `Plan2.eight`. hw: WordsTied: OPEN.

Limits.
- The words are those of the thread's witness at ds. That they are the job's own words is hw.
- Thr at 9 is a premise. Nothing here plays. At `PF`.
- Nothing on completeness, on soundness or on what is hidden.

NOT IN FRONT OF A LAW OVER COINS: `saysAt_nine` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from Thr as a
premise. None: the bar is flat.

-/
import E2E.ItemLaws
import E2E.KeyDoorNine
import E2E.KeyStandNineAt
import E2E.KeyNineLinesKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.Light.ItemLaws
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open Desc.K14 (St)
open Desc.K14.Law (rowsOn RowsU)
open Desc.K14.Honest (Eight SmpOwn)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey parKey sentKey randKey)
open AtPublicFiles.KeyDoorNine (jobNine enters_nine)
open AtPublicFiles.KeyStandNineAt (SaysNine items_at_nine)
open ProofFile.Honest.K14 (Plan2 num form2)
open ProofFile.Honest.K12 (TestCoins)
open ProofFile.Honest.Sh (TestSh testSh)
open KeyDoorUClosed (shapeU sentK members_U)

/-- **Read off a state's shape: the members of the group under test.** -/
theorem members_of_shape (t : T12) (N : TestSh) (h : testSh t = N) (l : List ℕ)
    (hm : (N.core.st.groups[N.g]?).map (·.members) = some l) (G : Group)
    (hG : t.st.groups[t.g]? = some G) : G.members.toList = l := by
  subst h
  have e : ((testSh t).core.st.groups[(testSh t).g]?).map (·.members) = some G.members.toList := by
    show ((t.st.groups.toList.map VerifiableInference.Desc.Ground.Sh.grpSh)[t.g]?).map _ = _
    rw [List.getElem?_map, Array.getElem?_toList, hG]
    rfl
  exact Option.some.inj (e.symm.trans hm)

theorem samples_of_smp {o : ℕ} {s : St} {m : Words GE} (h : SmpOwn o s m) :
    SampleSays rdE s.st o m := by
  intro x hx
  obtain ⟨y, hy, ha⟩ := h
  rw [hx] at hy
  obtain rfl := Option.some.inj hy
  exact ha

theorem open_of_rowsOn {s : St} {g : ℕ} {m : Words GE} (h : AllSay rdE s.st (rowsOn s g) m) (i : ℕ) :
    OpenSays rdE s.st g i m := by
  intro r hr
  obtain ⟨G, hG, hi⟩ := rowAt_iff.1 hr
  have e : rowsOn s g = G.rows.toList := by
    unfold rowsOn
    rw [hG]
    rfl
  rw [e] at h
  exact h r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type} (K₀ : AtPublicFiles.KeyBook.KeyPub)
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : K14.WitLens Wt) (Nm : NumbersS) (Mg₀ : ProofFile.Honest.Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins (AtPublicFiles.KeyBook.keyBook K₀) → ProofFile.Honest.Common W₀ Rc TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (rest : Coins (AtPublicFiles.KeyBook.keyBook K₀) → ProofFile.Honest.Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : ProofFile.Honest.Common W₀ Rc TableKey → Prop)
  (w : ProofFile.Honest.Common W₀ Rc TableKey)

/-- The many-member job behind `jobNine`. -/
abbrev AN (B : Eight (parKey Xs PF)) : ManyJob (ProofFile.Honest.Common W₀ Rc TableKey) X₀ :=
  jobLocU (X := X₀) ⟨parKey Xs PF, 0⟩ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U) (sentKey Xs PF)
    [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (keyProver K).storedWords
    (fun c => K.weights c.w₀) (fun c => randKey K c.rc) none

/-- **The group under test of the job's state has the members 0 and 3.** -/
theorem members_nine {layO : OnBytes.TreeLay} (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO)
    (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) (v : ProofFile.Honest.Common W₀ Rc TableKey)
    (fr : Front X₀) (G : Group)
    (hG : ((AN (X₀ := X₀) Xs K B).rec₀ v fr).st.groups[((AN (X₀ := X₀) Xs K B).rec₀ v fr).g]? = some G) :
    G.members.toList = [0, 3] := by
  have hS : (parKey Xs PF).S.sharedSplitNeeded = true := hQ.facts.two
  have hu : Desc.K14.withU (parKey Xs PF).S = some (sentKey Xs PF) := hQ.facts.goes
  have e1 : (AN (X₀ := X₀) Xs K B).rec₀ v fr =
      doorUF (parKey Xs PF) (sentKey Xs PF) [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
        (fun c : ProofFile.Honest.Common W₀ Rc TableKey => c.key)
        (fun c fr => colsLoc (parKey Xs PF) ((keyProver K).storedWords c.w₀ c.rc) fr.seen.rounds)
        v fr := rfl
  have hsh : testSh ((AN (X₀ := X₀) Xs K B).rec₀ v fr) =
      Desc.K14.Shape.doorU (endOf (parKey Xs PF) (sentKey Xs PF)) := by
    rw [e1]
    exact shape_doorUF (parKey Xs PF) _ B.made hS (sentKey Xs PF) hu _ _ v fr
  have hc : Desc.K14.Shape.doorU (endOf (parKey Xs PF) (sentKey Xs PF)) = shapeU := by
    show Desc.K14.Shape.doorU (endOf (parKey Xs PF) (sentOf (parKey Xs PF).S)) = _
    rw [e]
    unfold shapeU sentK
    rfl
  exact members_of_shape _ _ (hsh.trans hc) _ members_U G hG

/-- **At a stand the job's state on entry reads the thread's statement and group.** -/
theorem rec_nine {layO : OnBytes.TreeLay} (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO)
    (B : Eight (parKey Xs PF)) {k : Coins (AtPublicFiles.KeyBook.keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (ProofFile.Honest.Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w) 9 k s m E) :
    ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).st = s.st ∧
      ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).g = s.loc.gU := by
  have h := enters_nine Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w hQ B u
  have h' := Except.ok.inj h
  exact ⟨(congrArg (·.st) h').symm, (congrArg (·.g) h').symm⟩

/-- **The row count of the group, from Form at 9.** -/
theorem rows_nine {k : Coins (AtPublicFiles.KeyBook.keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (ProofFile.Honest.Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w) 9 k s m E) :
    (rowsOn s s.loc.gU).length = (parKey Xs PF).par.S.fold.index.answers +
      (parKey Xs PF).par.S.fold.columns + 1 := by
  have h9 : (form2 (parKey Xs PF) (fun _ _ => true) 9 s &&
      (!decide ((VerifiableInference.Desc.Shared.sharedPlaces true).length ≤ 9) || true)) = true :=
    u.2.2.1.1
  have h2 := (Bool.and_eq_true_iff.mp h9).1
  unfold form2 at h2
  rw [if_pos ⟨by omega, by omega⟩] at h2
  have hK := (Bool.and_eq_true_iff.mp h2).1
  have hO := (Desc.K14.Law.shapeO_iff _ _ _ _ _ _).1 hK
  exact ((Desc.K14.Law.shapeU_iff _ _ _ _).1 hO.1).2.2.2

/-- **`SaysAt` at the job, at a stand of Thr at 9, beside `WordsTied`.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem saysAt_nine {layO : OnBytes.TreeLay} (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO)
    (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) {k : Coins (AtPublicFiles.KeyBook.keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (ProofFile.Honest.Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w) 9 k s m E) (ds : List Fmt.Drawn)
    (C : TestCoins)
    (hw : ∀ G, ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).st.groups[
        ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).g]? = some G →
      WordsTied ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).st
        ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).g G
        (ℓ.get ((threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).wit k m.st.input (m.st.heard ++ ds)))
        (layoutOf ((AN (X₀ := X₀) Xs K B).rec₀ m.st.input (frontOf m)).st G)
        (plainMany (AN (X₀ := X₀) Xs K B) m.st.input (frontOf m) C)) :
    SaysAt (AN (X₀ := X₀) Xs K B) m.st.input (frontOf m) C := by
  obtain ⟨hst, hg⟩ := rec_nine K₀ Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w hQ B u
  obtain ⟨sU, -, sS, r1, r2, r3, -⟩ := items_at_nine Xs Nr PF K₀ K ℓ Nm Mg₀ tb rest Kp Vd w u ds
  have hI : OnBytes.Means.InOrder s.st := u.2.2.1.2
  have hK : OpenKinds s.st := openKinds_of_thr Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w u
  have hall : AllSay rdE s.st (rowsOn s s.loc.gU)
      (ℓ.get ((threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).wit k m.st.input (m.st.heard ++ ds))) :=
    allSay_three rdE s.st _ _ _ _ 1
      (Nat.le_of_eq (rows_nine K₀ Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w u)) r1 r2 r3
  refine saysAt_of_items _ _ _ C _ (by rw [hst]; exact hI) (by rw [hst]; exact hK)
    (by rw [hst, hg]; exact open_of_rowsOn hall) (fun G hG => ?_) hw
  rw [members_nine Xs K hQ e B _ _ G hG, hst]
  intro o ho
  rcases List.mem_cons.1 ho with rfl | ho
  · exact samples_of_smp sU
  · rcases List.mem_cons.1 ho with rfl | ho
    · exact samples_of_smp sS
    · cases ho

end

end ProofFile.Honest.K12.Light.ItemLaws

#print axioms ProofFile.Honest.K12.Light.ItemLaws.members_of_shape
#print axioms ProofFile.Honest.K12.Light.ItemLaws.samples_of_smp
#print axioms ProofFile.Honest.K12.Light.ItemLaws.open_of_rowsOn
#print axioms ProofFile.Honest.K12.Light.ItemLaws.AN
#print axioms ProofFile.Honest.K12.Light.ItemLaws.members_nine
#print axioms ProofFile.Honest.K12.Light.ItemLaws.rec_nine
#print axioms ProofFile.Honest.K12.Light.ItemLaws.rows_nine
#print axioms ProofFile.Honest.K12.Light.ItemLaws.saysAt_nine
