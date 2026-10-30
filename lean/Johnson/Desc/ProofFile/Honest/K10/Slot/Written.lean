-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Slot/Written.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/
WP.lean) THE 25 CLOSINGS, SPELLED, AND EACH HELD AGAINST THE WRITTEN BLOCK AT ITS PLACE; k AND h HELD A SECOND TIME
AGAINST THE WRITTEN REQUEST'S GROUPS; carried to every description whose plan is alike.

  `writtenPar`, `writtenClosings`  the 25 numbers, spelled: link, piece, k, h (0 at all), rows, the trees in front. How they came:
      read by a program off CutLit.lean's rows (place, number of rounds, list of trees), of which WP's blocks are made,
      and, rows and h, off a table of this project. So of k and the trees the first test is a check of the spelling alone;
      of the rows it is a check against the written rounds; k and h meet a second source in `groupsAre`
  `blockIs`, `closingsAre`  a public test: every block of the first chain at such a place has the kind's declared rounds,
      oracle messages and list of trees in front; each place has a block; as many blocks of the kind as members;
      each member has 1 ≤ k and h ≤ k: that is `closePlan`, the kind's own test on the plan (`closePlan_iff`)
  `groupsAre`         a public test: k and h against `reqGroups` of the written request (`proofSizedFull`)
  `closings_written`, `groups_written`  Lean's kernel says yes to both
  `closings_bite`      THE TESTS CAN FAIL: the last member dropped; one k greater by one; one count of rows greater by one;
      one h greater by one at the second test
  `written_rounds`, `written_there`   at F with `PlanAlike WP F`: each block at such a place has those rounds and oracle
      messages; there is such a block
  `written_seated`   so `Side.seated` yields a side and it is `CloseSeated`
  `written_goodAt`   the frame's form at such an F, at any job at such a place: Honest/K10/Slot/Good.lean's `slot_goodAt`

Limits. A fact on written values: WP's own limit stands: that any description has these rounds is no theorem of this
file: it stands under `PlanAlike WP F`. `Good` at A := False (Slot/Good.lean). Of a job only its numbers are asked.
Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K10.Slot.Good
import Johnson.AtFull.ProofPlan.WP
import Johnson.AtFull.ProofPlan.PlanAlike
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Slot
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open P2Law.ProofPlan (WP)
open ProofFile.Honest.Small (noneSpent)

/-- A closing's numbers; no work bits, h = 0, the trees 0 .. n - 1 in front. -/
def writtenPar (link piece k rows n : Nat) : Par :=
  { link := link, piece := piece, k := k, h := 0, rows := rows, workField := 0, workClose := 0,
    sent := List.range n }

/-- **The 25 closings, written.** -/
def writtenClosings : List Par := [
  writtenPar 0 11 8 6 4,
  writtenPar 1 11 7 3295 7,
  writtenPar 2 11 8 1324 10,
  writtenPar 3 11 7 3295 13,
  writtenPar 4 11 8 1324 16,
  writtenPar 5 11 7 3295 19,
  writtenPar 6 11 8 1324 22,
  writtenPar 7 11 7 3295 25,
  writtenPar 8 11 8 1324 28,
  writtenPar 9 11 7 3295 31,
  writtenPar 10 11 8 1324 34,
  writtenPar 11 11 7 3295 37,
  writtenPar 12 11 8 1324 40,
  writtenPar 13 11 7 3295 43,
  writtenPar 14 11 8 1324 46,
  writtenPar 15 11 7 3295 49,
  writtenPar 16 11 8 1324 52,
  writtenPar 17 11 7 3295 55,
  writtenPar 18 11 8 1324 58,
  writtenPar 19 11 7 3295 61,
  writtenPar 20 11 8 1324 64,
  writtenPar 21 11 7 3295 67,
  writtenPar 22 11 8 1324 70,
  writtenPar 23 11 7 3295 73,
  writtenPar 24 13 8 1322 76]

/-- A block has the kind's declared rounds, oracle messages and list of trees in front, at P. -/
def blockIs {S Cl : Type} (P : Par) (b : Block S Cl) : Bool :=
  decide (b.rounds = (closeRounds P).map (·.1)) && decide (b.oracles = (closeRounds P).map (·.2)) &&
    decide (b.before = P.sent.map fun n => (1, n))

/-- **A public test on a list of numbers, at the written first chain.** -/
def closingsAre (t : List Par) : Bool :=
  (WP.first.blocksInOrder.all fun b => t.all fun P => b.place != closePlace P || blockIs P b) &&
    (t.all fun P => WP.first.blocksInOrder.any fun b => b.place == closePlace P) &&
    ((WP.first.blocksInOrder.filter fun b => b.place.kind == .K10).length == t.length) &&
    (t.all fun P => decide (1 ≤ P.k) && decide (P.h ≤ P.k))

/-- **A public test: k and h, group by group, against the written request.** -/
def groupsAre (t : List Par) : Bool :=
  ((OnBytes.reqGroups PlanWritten.proofSizedFull.request).toList.take t.length).length == t.length &&
    (((OnBytes.reqGroups PlanWritten.proofSizedFull.request).toList.zip t).all fun x =>
      x.1.k == x.2.k && x.1.h == x.2.h)

theorem closings_written : closingsAre writtenClosings = true := by decide +kernel

theorem groups_written : groupsAre writtenClosings = true := by decide +kernel

/-- **The tests can fail.** -/
theorem closings_bite :
    closingsAre writtenClosings.dropLast = false ∧
      closingsAre (writtenClosings.modify 3 fun P => { P with k := P.k + 1 }) = false ∧
      closingsAre (writtenClosings.modify 3 fun P => { P with rows := P.rows + 1 }) = false ∧
      closingsAre (writtenClosings.modify 3 fun P => { P with sent := P.sent.dropLast }) = false ∧
      groupsAre (writtenClosings.modify 3 fun P => { P with k := P.k + 1 }) = false ∧
      groupsAre (writtenClosings.modify 3 fun P => { P with h := P.h + 1 }) = false := by
  decide +kernel

section Carry
variable {S Cl S' Cl' : Type}

/-- Behind `Forall₂` each member of the second list has its partner in the first. -/
theorem alike_back : ∀ {l : List (Block S Cl)} {l' : List (Block S' Cl')},
    List.Forall₂ Alike₂ l l' → ∀ b' ∈ l', ∃ b ∈ l, Alike₂ b b'
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons (a := a) h t, b', hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨b, hm, ha⟩ := alike_back t b' hb
      exact ⟨b, List.mem_cons_of_mem _ hm, ha⟩

/-- And the other way. -/
theorem alike_forth : ∀ {l : List (Block S Cl)} {l' : List (Block S' Cl')},
    List.Forall₂ Alike₂ l l' → ∀ b ∈ l, ∃ b' ∈ l', Alike₂ b b'
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons (b := c) h t, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨b', hm, ha⟩ := alike_forth t b hb
      exact ⟨b', List.mem_cons_of_mem _ hm, ha⟩

end Carry

theorem closings_parts :
    (WP.first.blocksInOrder.all fun b => writtenClosings.all fun P => b.place != closePlace P || blockIs P b) = true ∧
      (writtenClosings.all fun P => WP.first.blocksInOrder.any fun b => b.place == closePlace P) = true ∧
      (writtenClosings.all fun P => decide (1 ≤ P.k) && decide (P.h ≤ P.k)) = true := by
  have h := closings_written
  unfold closingsAre at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.2⟩

/-- Each written closing passes the kind's test on the plan. -/
theorem written_plan {P : Par} (hP : P ∈ writtenClosings) : closePlan P := by
  have h := List.all_eq_true.1 closings_parts.2.2 P hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- **At F with `PlanAlike WP F`: each block at a written closing's place has the kind's rounds and oracle messages.** -/
theorem written_rounds {Xi : Type} {F : FileDescription Xi} (hF : PlanAlike WP F) {P : Par} (hP : P ∈ writtenClosings) :
    ∀ b ∈ F.first.blocksInOrder, b.place = closePlace P →
      b.rounds = (closeRounds P).map (·.1) ∧ b.oracles = (closeRounds P).map (·.2) := by
  intro b hb hp
  obtain ⟨b₀, hb₀, hal⟩ := alike_back hF.first b hb
  have h1 : b₀.place = closePlace P := hal.1.trans hp
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 closings_parts.1 b₀ hb₀) P hP
  rw [h1, bne_self_eq_false, Bool.false_or] at h2
  unfold blockIs at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨hal.2.1.symm.trans h2.1.1, hal.2.2.1.symm.trans h2.1.2⟩

/-- **There is such a block.** -/
theorem written_there {Xi : Type} {F : FileDescription Xi} (hF : PlanAlike WP F) {P : Par} (hP : P ∈ writtenClosings) :
    ∃ b ∈ F.first.blocksInOrder, b.place = closePlace P := by
  obtain ⟨b₀, hb₀, hp⟩ := List.any_eq_true.1 (List.all_eq_true.1 closings_parts.2.1 P hP)
  obtain ⟨b, hb, hal⟩ := alike_forth hF.first b₀ hb₀
  exact ⟨b, hb, hal.1.symm.trans (eq_of_beq hp)⟩

section Seat
variable {V W X Pb : Type}

/-- **So `Side.seated` yields a side at such a place, and it is `CloseSeated`.** At any job at that place. -/
theorem written_seated {Xi : Type} {F : FileDescription Xi} (hF : PlanAlike WP F) (J : CloseJob W)
    (hP : J.pub.par ∈ writtenClosings) (fs : List (Fall F.S₁)) :
    ∃ σ : Side F.S₁ F.Cl V W X Pb,
      Side.seated F.first.blocksInOrder (closePlace J.pub.par) (slotRow J) fs = some σ ∧ CloseSeated σ J := by
  obtain ⟨b, hb, hp⟩ := written_there hF hP
  have hs : (F.first.blocksInOrder.find? fun b => b.place == closePlace J.pub.par).isSome = true :=
    List.find?_isSome.2 ⟨b, hb, by simpa using hp⟩
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hs
  have e : Side.seated (V := V) (W := W) (X := X) (Pb := Pb) F.first.blocksInOrder (closePlace J.pub.par)
      (slotRow J) fs = some { block := b', row := slotRow J, fall := fallOf fs (closePlace J.pub.par) } := by
    unfold Side.seated
    rw [hb']
    rfl
  exact ⟨_, e, closeSeated_of_seated e (written_rounds hF hP) (written_plan hP)⟩

/-- **The frame's form at such an F, at any job at a written closing's place.** -/
theorem written_goodAt {Xi : Type} {F : FileDescription Xi} (hF : PlanAlike WP F)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) (Bk : ProverCoinCounts)
    (J : CloseJob W) (hP : J.pub.par ∈ writtenClosings) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall F.S₁)) (B : Coins Bk → F.S₁ → Mid W X → Env → Prop)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hB : noneSpent Bk (closeAddr J.pub.par) = true) :
    (slotLettered (S := F.S₁) (Cl := F.Cl) Bk J B On bud).goodAt pre φ F.first.blocksInOrder ord chain firstTree fs :=
  slot_goodAt pre φ Bk J F.first.blocksInOrder ord chain firstTree fs B On bud (written_rounds hF hP)
    (written_plan hP) hB

end Seat

end ProofFile.Honest.K10.Slot

#print axioms ProofFile.Honest.K10.Slot.closings_written
#print axioms ProofFile.Honest.K10.Slot.groups_written
#print axioms ProofFile.Honest.K10.Slot.closings_bite
#print axioms ProofFile.Honest.K10.Slot.written_plan
#print axioms ProofFile.Honest.K10.Slot.written_rounds
#print axioms ProofFile.Honest.K10.Slot.written_there
#print axioms ProofFile.Honest.K10.Slot.written_seated
#print axioms ProofFile.Honest.K10.Slot.written_goodAt
