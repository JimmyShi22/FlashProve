-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/EqSlots.lean: THE SMALLNESS TEST: ITS RUN "K8.equations" AND THE LEDGER's
SLOTS: which of the run's claims name a slot, and what the run turns of the state: for the three
tests on a list of claims of Johnson/Desc/K9/Honest/SlotsLive.lean (`liveAt`, `plainAt`,
`unnamedAt`). From a yes of the run alone: no chance in it. It stands over the library alone. Lemmas
on the verifier's own text; none of the library's goals.

  `Bare cl`   the claim is added under a number that is handed to it (eqFirst is there), and its
                   form names no slot
  `emits_tie`, `emits_read`, `emits_weights`, `emits_tail`   the ties, the reads and the text behind
                   the first four claims lay `Bare` claims alone: by the library's `Emits` and its
                   rules for the routines' steps (Johnson/Desc/K9/Honest/K8NoSlot.lean), which has
                   the four at its weaker `NoSlot` (no word there on eqFirst)
  **`rest_bare`**   WHERE THE RUN's TEXT SAYS YES, EVERY CLAIM BEHIND THE FOURTH (the ties and the
                   reads) IS `Bare`
  **`live_eq`**, **`plain_all`**, **`unnamed_eq`**   SO, AT EVERY SLOT j: liveAt cls j = liveAt
                   (four8 tl g) j · plainAt cls j = true · unnamedAt cls j = unnamedAt (four8 tl g)
                   j: `four8 tl g`: the library's first four, written out
                   (Johnson/Desc/First/Batch/Law/K8Four.lean)
  `live_sBit`   the slot g.sBit is live, under no premise: the third claim names it with the
                   coefficient 1
  `live_of_word`   a slot is live wherever the second claim's own word on it is below the prime and
                   not 0: LITTLE MORE THAN THE TEST's TEXT
  `Spec.word_leaves`, **`word_leaves`**, **`live_leaves`**   THE LEAVES' WINDOW, ON THE FIELD's
                   SIDE: the second claim's coefficient on slot number i of the window is the i-th
                   word of the walk of the leaves' sumcheck, if the form from which that sumcheck
                   started names no such slot (by the library's `Psc.rowForm_value`,
                   OnBytes/Model/HideLaws.lean, read in two worlds); SO the slot is live wherever
                   that word reads as not 0
  **`run_slots`**   the three equations at the list of the run that the kind's block states
  **`merge_kept`**   AT THE RUN THAT THE KIND's BLOCK STATES: the slot of the merge's end value
                   (`K9.mergeOf`, Johnson/Desc/First/Batch/AtS.lean) is as it was
WHAT THE RUN TURNS, by the library's own laws: the state behind is the state in front with the
test's data and the ledger laid (`sits_equations`, Johnson/Desc/First/TailClaims/K8Sits.lean); the
ledger behind is the one in front with one owed claim marked as added, the leaves' window of slots
laid, one owed claim more marked (`take_four`).
Limits. That the form from which the leaves' sumcheck started names no slot of the window is a
premise: a fact on numbers. Which numbers the slots of the first four are; whether a word of theirs
is 0: not said: these forms come of what the lookup on the digits heard. That the merge's slot is
none of theirs is not said.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.TailClaims.K8Sits
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.K9.Honest.SlotsLive
import Johnson.Desc.K9.Honest.K8NoSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.K9L (four8 take_four)
open VerifiableInference.Desc.K9H (Emits)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt unnamedIn notZero slotWord slotCoef
  liveAt_iff unitAt nought)
open _root_.Fo.Eq (at_ok eqKeys_cut eqCounts_cut)

/-- Added under a number that is handed to it; its form names no slot. -/
def Bare (cl : Claim) : Prop := cl.eqFirst.isSome = true ∧ cl.form.slots = #[]

/-! ## The ties and the reads -/

theorem emits_tie (tl : HTailF2) (mu : Nat) : Emits Bare (eqTie tl mu) := by
  unfold eqTie
  repeat (first
    | exact Emits.pure _
    | exact Emits.get _ _
    | exact Emits.emit _ ⟨rfl, rfl⟩
    | apply Emits.bind
    | (show ∀ _, Emits _ _; intro _)
    | (dsimp only))

theorem emits_read (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) :
    Emits Bare (eqRead tl Fn sg laid sums) := by
  unfold eqRead
  repeat (first
    | exact Emits.pure _
    | exact Emits.get _ _
    | exact Emits.ask _ _
    | exact Emits.mustAs _ _
    | exact Emits.testAs _ _
    | exact Emits.emit _ ⟨rfl, rfl⟩
    | apply Emits.bind
    | (show ∀ _, Emits _ _; intro _)
    | (dsimp only)
    | split)

theorem emits_weights (tl : HTailF2) : Emits Bare (eqWeights tl) := by
  unfold eqWeights
  exact Emits.bind (Emits.ask _ _) fun _ => Emits.get _ _

theorem emits_tail (before : Nat) (tl : HTailF2) (funs : Array HFun) :
    Emits Bare (eqTail before tl funs) := by
  unfold eqTail
  repeat (first
    | exact Emits.pure _
    | exact Emits.claims
    | exact Emits.mustAs _ _
    | exact Emits.testAs _ _
    | exact Emits.get _ _
    | exact Emits.ask _ _
    | exact emits_weights _
    | exact emits_tie _ _
    | exact emits_read _ _ _ _ _
    | apply Emits.forInList
    | apply Emits.forInArray
    | apply Emits.ite
    | apply Emits.bind
    | (show ∀ _ _, Emits _ _; intro _ _)
    | (show ∀ _, Emits _ _; intro _)
    | (dsimp only)
    | split)

/-- **Every claim behind the fourth names no slot and is added under a number handed to it.** -/
theorem rest_bare {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∀ cl ∈ cls.drop 4, Bare cl := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := eq_parts h
  have hJ : EqM.at (eqKeys tl) front F #[] = .ok ((tla, s1.1), s1.2) := (at_ok _ _ _ _).2 h8
  have hB : EqM.at (eqCounts tla) front s1.1 s1.2 = .ok ((tlb, s2.1), s2.2) :=
    (at_ok _ _ _ _).2 h9
  obtain ⟨g, runs, -, -, -, j4, -, -⟩ := eqKeys_cut tl tla F s1.1 #[] s1.2 hJ
  obtain ⟨g', Fa, -, -, -, k3, -, -⟩ := eqCounts_cut tla tlb s1.1 s2.1 s1.2 s2.2 hB
  have hsz : s2.2.size = 4 := by
    rw [k3, j4]
    simp
  obtain ⟨new, eA, hQ⟩ := emits_tail before tlb funs front s2 (F1, arr) tl' k9
  have eA' : arr = s2.2 ++ new.toArray := eA
  have e : cls.drop 4 = new := by
    rw [← hcl, eA', Array.toList_append, List.drop_left' (by simpa using hsz)]
  rw [e]
  exact hQ

/-! ## The three tests -/

theorem live_bare {l : List Claim} (h : ∀ cl ∈ l, Bare cl) (j : Nat) : liveAt l j = false := by
  unfold liveAt
  refine List.any_eq_false.2 fun cl hc => ?_
  have e : cl.eqFirst.isNone = false := by
    cases hq : cl.eqFirst with
    | none => have := (h cl hc).1; rw [hq] at this; cases this
    | some _ => rfl
  simp [e]

theorem unnamed_bare {l : List Claim} (h : ∀ cl ∈ l, Bare cl) (j : Nat) :
    l.all (fun cl => unnamedIn cl j) = true := by
  refine List.all_eq_true.2 fun cl hc => ?_
  unfold unnamedIn
  rw [(h cl hc).2]
  rfl

section
variable {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork} {cls : List Claim}
  {g : Forest.Heard}

/-- The list is the library's four and the rest. -/
theorem split_four (h : equations front tl funs F = .ok (tl', F1, cls)) (hg : tl.heard = some g) :
    cls = four8 tl g ++ cls.drop 4 := by
  obtain ⟨g', Fa, e1, e2, -, -⟩ := take_four h
  obtain rfl : g' = g := Option.some.inj (e1.symm.trans hg)
  rw [← e2, List.take_append_drop]

theorem live_eq (h : equations front tl funs F = .ok (tl', F1, cls)) (hg : tl.heard = some g)
    (j : Nat) : liveAt cls j = liveAt (four8 tl g) j := by
  have hb := live_bare (rest_bare h) j
  unfold liveAt at hb ⊢
  rw [split_four h hg, List.any_append, hb, Bool.or_false]

theorem plain_all (h : equations front tl funs F = .ok (tl', F1, cls)) (hg : tl.heard = some g)
    (j : Nat) : plainAt cls j = true := by
  unfold plainAt
  refine List.all_eq_true.2 fun cl hc => ?_
  rw [split_four h hg] at hc
  rcases List.mem_append.1 hc with h4 | hr
  · have e : cl.eqFirst.isNone = true := by
      simp only [four8, List.mem_cons, List.not_mem_nil, or_false] at h4
      rcases h4 with rfl | rfl | rfl | rfl <;> rfl
    rw [e, Bool.true_or]
  · have hu := List.all_eq_true.1 (unnamed_bare (rest_bare h) j) cl hr
    rw [hu, Bool.or_true]

theorem unnamed_eq (h : equations front tl funs F = .ok (tl', F1, cls)) (hg : tl.heard = some g)
    (j : Nat) : unnamedAt cls j = unnamedAt (four8 tl g) j := by
  have hb := unnamed_bare (rest_bare h) j
  unfold unnamedAt
  rw [split_four h hg, List.all_append, hb, Bool.and_true]

end

/-- The word 1 is below the prime and not 0. -/
theorem one_live : notZero (addE zeroE oneE) = true := rfl

/-- **The slot g.sBit is live, under no premise.** -/
theorem live_sBit (tl : HTailF2) (g : Forest.Heard) : liveAt (four8 tl g) g.sBit = true := by
  have e : ∀ runs : Array Run2,
      slotWord { form := Aff.slot g.sBit, runs := runs } g.sBit = addE zeroE oneE := by
    intro runs
    simp [slotWord, Aff.slot]
  unfold liveAt four8
  simp only [List.any_cons, List.any_nil]
  rw [e, one_live]
  simp

/-- A slot is live wherever the second claim's word on it is below the prime and not 0. -/
theorem live_of_word (tl : HTailF2) (g : Forest.Heard) (j : Nat)
    (hw : ∀ cl, (four8 tl g)[1]? = some cl → notZero (slotWord cl j) = true) :
    liveAt (four8 tl g) j = true := by
  unfold liveAt
  refine List.any_eq_true.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
  rw [hw _ rfl]
  rfl

namespace Spec

/-- States: on the field's side: the coefficient with which the claim that a
sumcheck leaves names slot number i of its own window is the i-th word of its walk, if the form
from which the sumcheck started names no such slot. -/
def word_leaves : Prop :=
  ∀ (p : Psc) (i : Nat) (w : E), p.walk.1[i]? = some w →
    (∀ x ∈ p.start.slots.toList, x.1 ≠ p.first + i) →
    slotCoef Reading.gl { form := p.rowForm oneE {} } (p.first + i) = Reading.gl.val w

end Spec

section ring
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A form's coefficient on slot j is its value in the world where slot j holds 1 and all else 0,
less its value in the world where all is 0. -/
theorem coef_value (a : Aff) (j : Nat) :
    (a.slots.toList.map (slotValue ρ (unitAt K j))).sum =
      a.value ρ (unitAt K j) - a.value ρ (nought K) := by
  have e1 : (a.ents.toList.map (Ent.value ρ (unitAt K j))).sum =
      (a.ents.toList.map (Ent.value ρ (nought K))).sum := rfl
  have e3 : (a.slots.toList.map (slotValue ρ (nought K))).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
    simp [slotValue, nought]
  unfold Aff.value
  rw [e1, e3]
  ring

theorem sum_nought (l : List E) : ∀ s : Nat,
    sumFrom (fun t x => ρ.val x * (nought K).slot t) s l = 0 := by
  induction l with
  | nil => intro s; rfl
  | cons x l ih =>
    intro s
    simp only [sumFrom]
    rw [ih]
    simp [nought]

theorem sum_above (j : Nat) (l : List E) : ∀ s : Nat, j < s →
    sumFrom (fun t x => ρ.val x * (unitAt K j).slot t) s l = 0 := by
  induction l with
  | nil => intro s _; rfl
  | cons x l ih =>
    intro s hs
    have e : (unitAt K j).slot s = 0 := if_neg (by omega)
    simp only [sumFrom]
    rw [ih (s + 1) (by omega), e]
    ring

theorem sum_unit (l : List E) : ∀ (s i : Nat) (w : E), l[i]? = some w →
    sumFrom (fun t x => ρ.val x * (unitAt K (s + i)).slot t) s l = ρ.val w := by
  induction l with
  | nil => intro s i w h; simp at h
  | cons x l ih =>
    intro s i w h
    cases i with
    | zero =>
      obtain rfl : x = w := by simpa using h
      have e : (unitAt K (s + 0)).slot s = 1 := if_pos rfl
      simp only [sumFrom]
      rw [sum_above ρ (s + 0) l (s + 1) (by omega), e]
      ring
    | succ i =>
      have e : (unitAt K (s + (i + 1))).slot s = 0 := if_neg (by omega)
      have h' : l[i]? = some w := by simpa using h
      simp only [sumFrom]
      rw [e, show s + (i + 1) = (s + 1) + i by omega, ih (s + 1) i w h']
      ring

/-- A form that names no slot j has one value in the two worlds. -/
theorem value_unnamed (a : Aff) (j : Nat) (h : ∀ x ∈ a.slots.toList, x.1 ≠ j) :
    a.value ρ (unitAt K j) = a.value ρ (nought K) := by
  have e : (a.slots.toList.map (slotValue ρ (unitAt K j))).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have e0 : (unitAt K j).slot x.1 = 0 := if_neg (h x hx)
    simp [slotValue, e0]
  have c := coef_value ρ a j
  rw [e] at c
  exact (sub_eq_zero.1 c.symm)

end ring

theorem word_leaves : Spec.word_leaves := by
  intro p i w hi hs
  show ((p.rowForm oneE {}).slots.toList.map
    (slotValue Reading.gl (unitAt Cb.Gl.E (p.first + i)))).sum = _
  have k0 : ∀ W : World Cb.Gl.E, ({} : Aff).value Reading.gl W = Reading.gl.val zeroE :=
    fun W => by simp [Aff.value]
  rw [coef_value, Psc.rowForm_value, Psc.rowForm_value, sum_unit Reading.gl p.walk.1 p.first i w hi,
    sum_nought, value_unnamed Reading.gl p.start (p.first + i) hs, k0, k0]
  ring

/-- **The leaves' window**: slot number i of the window is live wherever the i-th word of the walk
of the leaves' sumcheck reads as not 0 and the form from which that sumcheck started names no such
slot. -/
theorem live_leaves (tl : HTailF2) (g : Forest.Heard) (i : Nat) (w : E)
    (hi : g.leaves.walk.1[i]? = some w)
    (hs : ∀ x ∈ g.leaves.start.slots.toList, x.1 ≠ g.leaves.first + i)
    (hw : Reading.gl.val w ≠ 0) : liveAt (four8 tl g) (g.leaves.first + i) = true := by
  refine (liveAt_iff _ _).2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, ?_⟩
  show slotCoef Reading.gl { form := g.leaves.rowForm oneE {} } (g.leaves.first + i) ≠ 0
  rw [word_leaves g.leaves i w hi hs]
  exact hw

/-! ## What the run turns -/

theorem merge_putTl (s : S) (tl : HTailF2) : K9.mergeOf (s.putTl tl) = K9.mergeOf s := by
  unfold K9.mergeOf S.putTl
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [ho, h]
  | _ => simp [h]

theorem merge_putFork (s : S) (F : Fork) : K9.mergeOf (s.putFork F) = K9.mergeOf s := by
  unfold K9.mergeOf S.putFork
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [ho, h]
  | _ => simp [h]

/-- **The slot of the merge's end value is as it was.** -/
theorem merge_kept (p : ParW) (run : Nat → S → Except String (List Claim × S))
    (h : ("K8.equations", run) ∈ (whole p).claims) (front : Nat) (s s' : S) (cls : List Claim)
    (hy : run front s = .ok (cls, s')) : K9.mergeOf s' = K9.mergeOf s := by
  obtain ⟨q, tl', F1, -, -, rfl⟩ := (sits_equations p run h front s s' cls).1 hy
  show K9.mergeOf ((s.putTl tl').putFork F1) = _
  rw [merge_putFork, merge_putTl]

/-- **The three tests at the list of the run that the kind's block states.** -/
theorem run_slots (p : ParW) (run : Nat → S → Except String (List Claim × S))
    (h : ("K8.equations", run) ∈ (whole p).claims) (front : Nat) (s s' : S) (cls : List Claim)
    (hy : run front s = .ok (cls, s')) :
    ∃ q g, partOf s = some q ∧ q.tl.heard = some g ∧ ∀ j,
      liveAt cls j = liveAt (four8 q.tl g) j ∧ plainAt cls j = true ∧
        unnamedAt cls j = unnamedAt (four8 q.tl g) j := by
  obtain ⟨q, tl', F1, hq, he, -⟩ := (sits_equations p run h front s s' cls).1 hy
  obtain ⟨g, Fa, hg, -⟩ := take_four he
  exact ⟨q, g, hq, hg, fun j => ⟨live_eq he hg j, plain_all he hg j, unnamed_eq he hg j⟩⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.word_leaves
#print axioms VerifiableInference.Desc.First.K8.Honest.live_leaves
#print axioms VerifiableInference.Desc.First.K8.Honest.run_slots
#print axioms VerifiableInference.Desc.First.K8.Honest.emits_tail
#print axioms VerifiableInference.Desc.First.K8.Honest.rest_bare
#print axioms VerifiableInference.Desc.First.K8.Honest.split_four
#print axioms VerifiableInference.Desc.First.K8.Honest.live_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_all
#print axioms VerifiableInference.Desc.First.K8.Honest.unnamed_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.one_live
#print axioms VerifiableInference.Desc.First.K8.Honest.live_sBit
#print axioms VerifiableInference.Desc.First.K8.Honest.live_of_word
#print axioms VerifiableInference.Desc.First.K8.Honest.merge_kept
#print axioms VerifiableInference.Desc.First.K8.Honest.Bare
#print axioms VerifiableInference.Desc.First.K8.Honest.emits_tie
#print axioms VerifiableInference.Desc.First.K8.Honest.emits_read
#print axioms VerifiableInference.Desc.First.K8.Honest.emits_weights
#print axioms VerifiableInference.Desc.First.K8.Honest.live_bare
#print axioms VerifiableInference.Desc.First.K8.Honest.unnamed_bare
#print axioms VerifiableInference.Desc.First.K8.Honest.Spec.word_leaves
#print axioms VerifiableInference.Desc.First.K8.Honest.coef_value
#print axioms VerifiableInference.Desc.First.K8.Honest.sum_nought
#print axioms VerifiableInference.Desc.First.K8.Honest.sum_above
#print axioms VerifiableInference.Desc.First.K8.Honest.sum_unit
#print axioms VerifiableInference.Desc.First.K8.Honest.value_unnamed
#print axioms VerifiableInference.Desc.First.K8.Honest.merge_putTl
#print axioms VerifiableInference.Desc.First.K8.Honest.merge_putFork
