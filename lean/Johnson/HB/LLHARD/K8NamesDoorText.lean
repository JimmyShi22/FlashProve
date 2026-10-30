-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K8NamesDoorText.lean: the public test `namesDoorB` on a file's description
(Johnson/Desc/First/K8/PlanDoor.lean): at every sub-protocol of the kind K8, every tree that the
entry four in front of it and the entry right in front of it send is named in its field `before`,
and each of these two sends a tree. It accepts at every description whose first chain's entries are
shaped and whose cut into sub-protocols is the written one. So it accepts in scope wherever the
value is laid.

Row or tool. General laws, closed facts on written values with negative tests, and a law in scope by
calls of named laws. A payer for a premise of another law: the first conjunct of the condition
`K8Cond` on the kind K8 (Johnson/Goal/Skeleton/Kinds/K8Bridge.lean).


What it spends. Rows are those of the proof file's entry tests, `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean), counted from 1: row 10 holds the cut
into sub-protocols to the written one (`cutRow`). `doorText_at_name`: row 10, by the second half of
`pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), and the field `planOk` of `LaidAt` (the
description's own test on the plan, for "shaped"). All else here: no row and no field: general laws,
or facts on written values.

The test's text. This file imports PlanNames.lean, which PlanDoor.lean imports, and not
PlanDoor.lean itself. `drawIxsT`, `sentByT`, `doorAtT` and `doorText` spell out `drawIxs`, `sentBy`,
`namesDoorAt` and `namesDoorB`. The file K8NamesDoorAtHead.lean beside this one imports
PlanDoor.lean and shows that the text is the test.

Why it is a test on the cut. Of a description F the test reads the first chain's flat list alone:
`F.roundsDeclaredByBlocks.1` is that list's rounds in a row, by definition. Where an entry is shaped (`Block.shaped`,
a clause of the description's own test on the plan) its declared rounds send as many trees as it
tells. So the trees in front of entry i are `treesTold` of what the entries tell
(Johnson/Desc/First/BookFit.lean). What is left are three projections of the cut: the places, what
each entry tells, and the fields `before`. No list of rounds is walked.

What is here.
  `roots_zip`, `roots_shaped`: a shaped entry's rounds send as many trees as it tells.
    `take_len_add`, `take_flat`, `roots_flat`: on lists. `trees_is`.
  `sent3`, `doorAt3`, `ixs3`, `door3 P T B d`: the test on three lists; d is the greater distance, 4
    in the test.
  `sent_is`, `doorAt_is`, `ixs_is`, `door_is`: under "shaped", `doorText F` is `door3` at the three
    projections, at 4.
  `beforeCut`: the fields `before` of the written cut.
  `door_written`: `door3` accepts at the written places, the written tellings and `beforeCut`, at 4.
  `door_walks`: the written places have 25 of the kind K8: so the test does not pass for want of
    such an entry.
  `door_rejects`: negative tests, each at every one of the 25: at the distance 3 the test at the
    entry rejects, and it does so because the entry three in front sends no tree; with the last name
    struck from every `before` the test at the entry rejects.
  `doorText_of_cut`: general in the description. `doorText_at_name`: in scope, where the value is
    laid.
By evaluations in Lean's kernel (`decide +kernel`): `door_written`, `door_walks`, `door_rejects`.

Limits. Those of PlanDoor.lean: the distances 4 and 1 are written numbers; the test says that the
sent trees are among the named ones, not that no other is named. Nothing on soundness.


-/
import Johnson.Desc.First.K8.PlanNames
import Johnson.Desc.First.CutWritten
import Johnson.Desc.First.BookFit
import Johnson.Desc.RunLaws
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First (treesTold toldCut placesCut told_at_written toldOf blockPlaces)
open VerifiableInference.Desc.First.K8 (rootsOfRounds roundsOfBlocks treesFrom)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)

/-! ## The test's text -/

/-- The text of `drawIxs`. -/
def drawIxsT {Xi : Type} (F : FileDescription Xi) : List ℕ :=
  (F.first.blocksInOrder.zipIdx.filter fun x => x.1.place.kind == KindName.K8).map (·.2)

/-- The text of `sentBy`. -/
def sentByT {Xi : Type} (F : FileDescription Xi) (i : ℕ) : List ℕ :=
  match F.first.blocksInOrder[i]? with
  | some b => List.range' (treesFrom F i) (rootsOfRounds b.rounds)
  | none => []

/-- The text of `namesDoorAt`. -/
def doorAtT {Xi : Type} (F : FileDescription Xi) (i : ℕ) : Bool :=
  match F.first.blocksInOrder[i]? with
  | some b =>
    decide (4 ≤ i) && !(sentByT F (i - 4)).isEmpty && !(sentByT F (i - 1)).isEmpty &&
      (sentByT F (i - 4) ++ sentByT F (i - 1)).all fun j => b.before.contains (1, j)
  | none => false

/-- The text of `namesDoorB`. -/
def doorText {Xi : Type} (F : FileDescription Xi) : Bool := (drawIxsT F).all (doorAtT F)

/-! ## A shaped entry's rounds send as many trees as it tells -/

theorem roots_zip : ∀ (rs : List Fmt.DeclaredRound) (os : List (List Oracle)),
    os.length = rs.length → (∀ x ∈ rs.zip os, x.2.length = x.1.entry.roots) →
    rootsOfRounds rs = os.flatten.length
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | r :: rs, o :: os, h, H => by
    have ih := roots_zip rs os (Nat.succ.inj h) fun x hx => H x (List.mem_cons_of_mem _ hx)
    have h0 : o.length = r.entry.roots := H (r, o) (List.mem_cons_self ..)
    unfold rootsOfRounds at ih ⊢
    rw [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, ih, h0]

theorem roots_shaped {S Cl : Type} {b : Block S Cl} (h : b.shaped = true) :
    rootsOfRounds b.rounds = b.oracles.flatten.length := by
  simp only [Block.shaped, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact roots_zip _ _ h.1 fun x hx => (h.2 x hx).1

theorem take_len_add {α : Type} : ∀ (l₁ l₂ : List α) (n : ℕ),
    (l₁ ++ l₂).take (l₁.length + n) = l₁ ++ l₂.take n
  | [], l₂, n => by simp
  | a :: l₁, l₂, n => by
    show ((a :: (l₁ ++ l₂)).take ((l₁.length + 1) + n)) = _
    rw [Nat.add_right_comm, List.take_succ_cons, take_len_add l₁ l₂ n]
    rfl

theorem take_flat {β γ : Type} (f : β → List γ) : ∀ (bs : List β) (i : ℕ),
    (bs.flatMap f).take (((bs.take i).map fun b => (f b).length).sum) = (bs.take i).flatMap f
  | [], i => by simp
  | _ :: _, 0 => by simp
  | b :: bs, i + 1 => by
    rw [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.flatMap_cons,
      take_len_add, take_flat f bs i]

theorem roots_flat {S Cl : Type} : ∀ l : List (Block S Cl),
    rootsOfRounds (l.flatMap (·.rounds)) = (l.map fun b => rootsOfRounds b.rounds).sum
  | [] => rfl
  | b :: l => by
    have ih := roots_flat l
    unfold rootsOfRounds at ih ⊢
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- **The trees in front of entry i are those that the entries in front tell.** -/
theorem trees_is {Xi : Type} (F : FileDescription Xi) (hs : ∀ b ∈ F.first.blocksInOrder, b.shaped = true)
    (i : ℕ) : treesFrom F i = treesTold (toldOf F.first.blocksInOrder) i := by
  unfold treesFrom roundsOfBlocks
  show rootsOfRounds ((F.first.blocksInOrder.flatMap (·.rounds)).take
    (((F.first.blocksInOrder.take i).map fun b => b.rounds.length).sum)) = _
  rw [take_flat (β := Block F.S₁ F.Cl) (fun b => b.rounds) F.first.blocksInOrder i, roots_flat]
  unfold treesTold toldOf
  rw [← List.map_take, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun b hb =>
    roots_shaped (hs b (List.mem_of_mem_take hb)))

/-! ## The test on three lists -/

def sent3 (T : List (List Oracle)) (i : ℕ) : List ℕ :=
  match T[i]? with
  | some os => List.range' (treesTold T i) os.length
  | none => []

def doorAt3 (T : List (List Oracle)) (B : List (List (ℕ × ℕ))) (d i : ℕ) : Bool :=
  match B[i]? with
  | some bf =>
    decide (d ≤ i) && !(sent3 T (i - d)).isEmpty && !(sent3 T (i - 1)).isEmpty &&
      (sent3 T (i - d) ++ sent3 T (i - 1)).all fun j => bf.contains (1, j)
  | none => false

def ixs3 (P : List Place) : List ℕ :=
  (P.zipIdx.filter fun x => x.1.kind == KindName.K8).map (·.2)

/-- **The test on the places, what the entries tell, and the fields `before`.** -/
def door3 (P : List Place) (T : List (List Oracle)) (B : List (List (ℕ × ℕ))) (d : ℕ) : Bool :=
  (ixs3 P).all (doorAt3 T B d)

theorem sent_is {Xi : Type} (F : FileDescription Xi) (hs : ∀ b ∈ F.first.blocksInOrder, b.shaped = true)
    (i : ℕ) : sentByT F i = sent3 (toldOf F.first.blocksInOrder) i := by
  unfold sentByT sent3
  rw [show (toldOf F.first.blocksInOrder)[i]? = (F.first.blocksInOrder[i]?).map fun b => b.oracles.flatten from
    List.getElem?_map ..]
  cases hb : F.first.blocksInOrder[i]? with
  | none => rfl
  | some b =>
    show List.range' (treesFrom F i) (rootsOfRounds b.rounds) = _
    rw [trees_is F hs, roots_shaped (hs b (List.mem_of_getElem? hb))]
    rfl

theorem doorAt_is {Xi : Type} (F : FileDescription Xi) (hs : ∀ b ∈ F.first.blocksInOrder, b.shaped = true)
    (i : ℕ) :
    doorAtT F i = doorAt3 (toldOf F.first.blocksInOrder) (F.first.blocksInOrder.map (·.before)) 4 i := by
  unfold doorAtT doorAt3
  rw [List.getElem?_map, sent_is F hs, sent_is F hs]
  cases F.first.blocksInOrder[i]? <;> rfl

theorem ixs_is {Xi : Type} (F : FileDescription Xi) : drawIxsT F = ixs3 (blockPlaces F.first.blocksInOrder) := by
  unfold drawIxsT ixs3 blockPlaces
  rw [List.zipIdx_map, List.filter_map, List.map_map]
  rfl

/-- **Under "shaped" the test is the test on three lists.** -/
theorem door_is {Xi : Type} (F : FileDescription Xi) (hs : ∀ b ∈ F.first.blocksInOrder, b.shaped = true) :
    doorText F =
      door3 (blockPlaces F.first.blocksInOrder) (toldOf F.first.blocksInOrder) (F.first.blocksInOrder.map (·.before)) 4 := by
  unfold doorText door3
  rw [ixs_is]
  exact congrArg _ (funext fun i => doorAt_is F hs i)

/-! ## At the written cut -/

/-- The fields `before` of the written cut. -/
def beforeCut : List (List (ℕ × ℕ)) := cutFirstFull.map (·.2.2.2.2.2)

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written cut.** -/
theorem door_written : door3 placesCut toldCut beforeCut 4 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The written places have 25 of the kind K8.** -/
theorem door_walks : (ixs3 placesCut).length = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Negative tests, each at every one of the 25.** -/
theorem door_rejects :
    ((ixs3 placesCut).all fun i => !doorAt3 toldCut beforeCut 3 i) = true ∧
      ((ixs3 placesCut).all fun i => (sent3 toldCut (i - 3)).isEmpty) = true ∧
      ((ixs3 placesCut).all fun i => !doorAt3 toldCut (beforeCut.map (·.dropLast)) 4 i) = true := by
  decide +kernel

/-- **At every description whose first chain is shaped and cut as written.** -/
theorem doorText_of_cut {Xi : Type} (F : FileDescription Xi)
    (hs : ∀ b ∈ F.first.blocksInOrder, b.shaped = true) (hc : cutOf F.first.blocksInOrder = cutFirstFull) :
    doorText F = true := by
  have hB : F.first.blocksInOrder.map (·.before) = beforeCut := by
    unfold beforeCut
    rw [← hc]
    unfold cutOf
    rw [List.map_map]
    rfl
  rw [door_is F hs, (told_at_written hc).1, (told_at_written hc).2, hB]
  exact door_written

/-- **In scope, where the value is laid.** -/
theorem doorText_at_name {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    doorText (F0T OnBytes.secondHashFunction Zp Np cF) = true :=
  doorText_of_cut _ (fun b hb => (((FileDescription.planOk_ok _).1 L.planOk).blocks₁ b hb).2)
    (pins_of_laid hZ L).2

end P5J


#print axioms P5J.roots_zip
#print axioms P5J.roots_shaped
#print axioms P5J.take_len_add
#print axioms P5J.take_flat
#print axioms P5J.roots_flat
#print axioms P5J.trees_is
#print axioms P5J.sent_is
#print axioms P5J.doorAt_is
#print axioms P5J.ixs_is
#print axioms P5J.door_is
#print axioms P5J.door_written
#print axioms P5J.door_walks
#print axioms P5J.door_rejects
#print axioms P5J.doorText_of_cut
#print axioms P5J.doorText_at_name
