-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OItems.lean: what the open items say at border 10 of the key's shared
thread, turned into the forms that `saysAt_of_items` takes, on the two facts of shape of the group under test.

  `OmegaItemsSay`                  what the open items say at border 10, of a state and a witness's words
  `group_of_shape`                 read off a state's shape: the rows and the members of the group under test
  `group_at_door`                  at a state of the door's shape that group has one open row, members 2 and 3
  `openSays_of_omega_items`        every open row of G_omega says
  `sampleItem_of_omega_items`      the sample rows of messages 2 and 3 say
  `saysAt_of_omega_items`          `SaysAt` at a job whose state on entry reads s
  `omega_items_at_ten`             at a stand of the key's thread the items say `OmegaItemsSay`

The premises of `saysAt_of_omega_items`, with who pays them. hst, hg: `enters_at_ten_key`. hI: the second half of the
form at 10. hK: `openKinds_of_thr`. hs: `omega_items_at_ten`. hsh: `shape_at_key`. hw: `words_tied_at_ten`.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `omega_items_at_ten` bears this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the
  thread's pair is a premise. It is clause (I) of the thread read off at three items, and pays nothing.
- That a stand at 10 is reached is not said: it wants member 9 stepped, and `keeps` at member 9 must hold what the
  rows of member 10 ask, as `RidesPast` has no step.
- Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.SaysAtNine
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OLines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey Group)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay OpenKinds OpenSays layoutOf sampleItem Words)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open Desc.K14 (St)
open Desc.K14.Law (rowsOn RowsO)
open Desc.K14.Honest (SmpOwn)
open ProofFile.Honest
open ProofFile.Honest.K14 (num WitLens)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items allSay_three samples_of_smp open_of_rowsOn)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeOm)
open ProofFile.Honest.Sh (TestSh testSh)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey)

/-- What the open items say at border 10, of a state and a witness's words. -/
def OmegaItemsSay (s : St) (m : Words GE) : Prop :=
  SmpOwn (num .oOmega) s m ∧ SmpOwn (num .oSp) s m ∧ RowsO rdE 0 1 s m

/-- **Read off a state's shape: the rows and the members of the group under test.** -/
theorem group_of_shape (t : T12) (N : TestSh) (h : testSh t = N) (l : ℕ × List ℕ)
    (hm : (N.core.st.groups[N.g]?).map openRowsAndMembers = some l) (G : Group)
    (hG : t.st.groups[t.g]? = some G) : (G.rows.toList.length, G.members.toList) = l := by
  subst h
  have e : ((testSh t).core.st.groups[(testSh t).g]?).map openRowsAndMembers =
      some (G.rows.toList.length, G.members.toList) := by
    show ((t.st.groups.toList.map VerifiableInference.Desc.Ground.Sh.grpSh)[t.g]?).map _ = _
    rw [List.getElem?_map, Array.getElem?_toList, hG]
    simp only [Option.map_some, openRowsAndMembers, VerifiableInference.Desc.Ground.Sh.grpSh, List.length_map]
  exact Option.some.inj (e.symm.trans hm)

/-- **The group under test has one open row, and the members 2 and 3**, at a state of the door's shape. -/
theorem group_at_door (t : T12) (ht : testSh t = shapeOm) (G : Group)
    (hG : t.st.groups[t.g]? = some G) : G.rows.toList.length = 1 ∧ G.members.toList = [2, 3] := by
  have e := group_of_shape t _ ht _ group_under_test G hG
  exact ⟨congrArg (·.1) e, congrArg (·.2) e⟩

/-- **Every open row of G_omega says**, where the group has at most one open row. -/
theorem openSays_of_omega_items {s : St} {m : Words GE} (h : OmegaItemsSay s m)
    (hrows : (rowsOn s s.loc.gOmega).length ≤ 1) (i : ℕ) :
    OpenSays rdE s.st s.loc.gOmega i m :=
  open_of_rowsOn (allSay_three rdE s.st _ _ 1 0 0 hrows h.2.2
    (fun r hr => by simp at hr) (fun r hr => by simp at hr)) i

/-- **The sample rows of the group's two members say.** -/
theorem sampleItem_of_omega_items {s : St} {m : Words GE} (h : OmegaItemsSay s m) :
    sampleItem rdE s.st [2, 3] m := by
  intro o ho
  rcases List.mem_cons.1 ho with rfl | ho
  · exact samples_of_smp h.1
  · rcases List.mem_cons.1 ho with rfl | ho
    · exact samples_of_smp h.2.1
    · cases ho

/-- **`SaysAt` at a job whose state on entry reads the state s**, from the items and the tie. -/
theorem saysAt_of_omega_items {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (s : St) (m : Words GE) (hst : (A.rec₀ w fr).st = s.st) (hg : (A.rec₀ w fr).g = s.loc.gOmega)
    (hI : OnBytes.Means.InOrder s.st) (hK : OpenKinds s.st) (hs : OmegaItemsSay s m)
    (hsh : testSh (A.rec₀ w fr) = shapeOm)
    (hw : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
      WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
        (plainMany A w fr C)) :
    SaysAt A w fr C := by
  have hrows : (rowsOn s s.loc.gOmega).length ≤ 1 := by
    unfold rowsOn
    cases hG : s.st.groups[s.loc.gOmega]? with
    | none => exact Nat.zero_le _
    | some G =>
      have hG' : (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G := by
        rw [hst, hg]
        exact hG
      exact Nat.le_of_eq (group_at_door _ hsh G hG').1
  refine saysAt_of_items _ _ _ C _ (by rw [hst]; exact hI) (by rw [hst]; exact hK)
    (by rw [hst, hg]; exact openSays_of_omega_items hs hrows) (fun G hG => ?_) hw
  rw [(group_at_door _ hsh G hG).2, hst]
  exact sampleItem_of_omega_items hs

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The items at border 10 of the key's shared thread.** -/
theorem omega_items_at_ten {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 10 k s m E) (ds : List Fmt.Drawn) :
    OmegaItemsSay s (ℓ.get ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).wit k m.st.input
      (m.st.heard ++ ds))) := by
  have hI := u.2.2.2.1 ds
  refine ⟨hI (ItemS.row (.sample .oOmega)) ?_, hI (ItemS.row (.sample .oSp)) ?_,
    hI (ItemS.row .foldOmega) ?_⟩
  all_goals
    show _ ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10
    decide

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.OmegaItemsSay
#print axioms ProofFile.Honest.K12.AtKey.group_of_shape
#print axioms ProofFile.Honest.K12.AtKey.group_at_door
#print axioms ProofFile.Honest.K12.AtKey.openSays_of_omega_items
#print axioms ProofFile.Honest.K12.AtKey.sampleItem_of_omega_items
#print axioms ProofFile.Honest.K12.AtKey.saysAt_of_omega_items
#print axioms ProofFile.Honest.K12.AtKey.omega_items_at_ten
