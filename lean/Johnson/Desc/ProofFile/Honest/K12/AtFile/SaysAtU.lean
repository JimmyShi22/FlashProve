-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SaysAtU.lean: `SaysAt` at the test on G_u at the proof file's
shared thread, at a stand, from what the thread's items say at border 9 and `words_tied_U`: the premise
hsay of `acceptedS_head_U`.

  `SaysU`        what the open items say at border 9, of a state and a witness's words
  `samples_of_smp`, `open_of_rowsOn`   the items in the forms that `saysAt_of_items` takes
  `saysAt_U`     `SaysAt` from these, at a state that the seat's way in reads
  `items_at_U`   at a stand of a shared thread whose meaning is `mgWords`, the items say `SaysU`
  `rows_at_U`    the group's row count, at a thread whose form is `form2`
  `order_at_U`   the statement is in order

By what. `saysAt_of_items`, `allSay_three` (E2E/ItemLaws.lean).

The premises of `saysAt_U`. hst, hg: the job's state on entry reads s's statement and group:
`enters_at_nine` (FieldsAtU.lean). hI, hK: the statement is in order, and no open row is marked as a sample
row, at s. hrows: the group's row count, from the thread's form at 9. hs: `SaysU`: the items. hmem: the
members. hw: `WordsTied`: `words_tied_U` (WordsTiedU.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's stand is a premise.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WordsTiedU
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import E2E.ItemLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey Group GroupLayout)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay OpenKinds OpenSays SampleSays InOrder rowAt_iff layoutOf sampleItem Words)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12)
open Desc.K14 (St blocks frontBlock withU first)
open Desc.K14.Law (rowsOn RowsU RowsO)
open Desc.K14.Honest (SmpOwn Like)
open ProofFile.Honest
open ProofFile.Honest.K14 (num)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items allSay_three)
open OnBytes.Params (LinShape)

/-- What the open items say at border 9, of a state and a witness's words. -/
def SaysU (Q : Desc.K14.P14) (s : St) (w : Words GE) : Prop :=
  SmpOwn (num .oU) s w ∧ SmpOwn (num .oOmega) s w ∧ SmpOwn (num .oSp) s w ∧
    RowsU rdE 0 Q.par.S.fold.index.answers s w ∧
    RowsU rdE Q.par.S.fold.index.answers Q.par.S.fold.columns s w ∧
    RowsU rdE (Q.par.S.fold.index.answers + Q.par.S.fold.columns) 1 s w ∧
    RowsO rdE 0 1 s w

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

/-- **`SaysAt` at the job, at a state that the seat's way in reads**, from the items and the tie. -/
theorem saysAt_U {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (Q : Desc.K14.P14) (s : St) (m : Words GE)
    (hst : (A.rec₀ w fr).st = s.st) (hg : (A.rec₀ w fr).g = s.loc.gU)
    (hI : OnBytes.Means.InOrder s.st) (hK : OpenKinds s.st)
    (hrows : (rowsOn s s.loc.gU).length =
      Q.par.S.fold.index.answers + Q.par.S.fold.columns + 1)
    (hs : SaysU Q s m)
    (hmem : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G → G.members.toList = [0, 3])
    (hw : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
      WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
        (plainMany A w fr C)) :
    SaysAt A w fr C := by
  obtain ⟨sU, -, sS, r1, r2, r3, -⟩ := hs
  have hall : AllSay rdE s.st (rowsOn s s.loc.gU) m :=
    allSay_three rdE s.st _ _ _ _ 1 (Nat.le_of_eq hrows) r1 r2 r3
  refine saysAt_of_items _ _ _ C _ (by rw [hst]; exact hI) (by rw [hst]; exact hK)
    (by rw [hst, hg]; exact open_of_rowsOn hall) (fun G hG => ?_) hw
  rw [hmem G hG, hst]
  intro o ho
  rcases List.mem_cons.1 ho with rfl | ho
  · exact samples_of_smp sU
  · rcases List.mem_cons.1 ho with rfl | ho
    · exact samples_of_smp sS
    · cases ho

section
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS)
open ProofFile.Honest.K14 (mgWords form2 WitLens)
variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}
  (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (Q : Desc.K14.P14)

/-- **The items at border 9**, at a shared thread whose meaning is `mgWords`. -/
theorem items_at_U (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (hMg : L.Mg = fun w => mgWords ℓ Q L.N (Mg₀ w)) (hsp : L.split = true) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr L.thread 9 k s m E)
    (ds : List Fmt.Drawn) :
    SaysU Q s (ℓ.get (L.wit k m.st.input (m.st.heard ++ ds))) := by
  have hI := u.2.2.2.1 ds
  have key : ∀ i, i ∈ L.thread.opened 9 → ItemS.holdsSh L.N (mgWords ℓ Q L.N (Mg₀ m.st.input)) i s
      (L.thread.strs E) (L.wit k m.st.input (m.st.heard ++ ds)) := fun i hi => by
    have e := hI i hi
    change ItemS.holdsSh L.N (L.Mg m.st.input) i s (L.thread.strs E)
      (L.wit k m.st.input (m.st.heard ++ ds)) at e
    rw [hMg] at e
    exact e
  have hop : ∀ i, i ∈ ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start
      (ProofFile.Honest.SharedRows.rows true) 9 → i ∈ L.thread.opened 9 := fun i hi => by
    show i ∈ ProofFile.Honest.fwdOpen ProofFile.Honest.SharedRows.start
      (ProofFile.Honest.SharedRows.rows L.split) 9
    rw [hsp]
    exact hi
  refine ⟨key (ItemS.pin .oU) (hop _ ?_) .oU rfl, key (ItemS.pin .oOmega) (hop _ ?_) .oOmega rfl,
    key (ItemS.pin .oSp) (hop _ ?_) .oSp rfl, key (ItemS.row .recG) (hop _ ?_),
    key (ItemS.row .loc) (hop _ ?_), key (ItemS.row .foldU) (hop _ ?_),
    key (ItemS.row .foldOmega) (hop _ ?_)⟩
  all_goals decide

/-- **The group's row count**, at a shared thread whose form is `form2`. -/
theorem rows_at_U (other : ℕ → St → Bool) (hsh : L.shape = form2 Q other) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr L.thread 9 k s m E) :
    (rowsOn s s.loc.gU).length = Q.par.S.fold.index.answers + Q.par.S.fold.columns + 1 := by
  have h9 : (L.shape 9 s && _) = true := u.2.2.1.1
  rw [hsh] at h9
  have h2 := (Bool.and_eq_true_iff.mp h9).1
  unfold form2 at h2
  rw [if_pos ⟨by omega, by omega⟩] at h2
  have hK := (Bool.and_eq_true_iff.mp h2).1
  have hO := (Desc.K14.Law.shapeO_iff _ _ _ _ _ _).1 hK
  exact ((Desc.K14.Law.shapeU_iff _ _ _ _).1 hO.1).2.2.2

/-- The statement is in order, at a shared thread whose order is that. -/
theorem order_at_U (ho : ∀ s, L.order s → OnBytes.Means.InOrder s.st) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr L.thread 9 k s m E) : OnBytes.Means.InOrder s.st :=
  ho s u.2.2.1.2

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.items_at_U
#print axioms ProofFile.Honest.K12.AtFile.rows_at_U
#print axioms ProofFile.Honest.K12.AtFile.order_at_U
#print axioms ProofFile.Honest.K12.AtFile.samples_of_smp
#print axioms ProofFile.Honest.K12.AtFile.open_of_rowsOn
#print axioms ProofFile.Honest.K12.AtFile.saysAt_U
