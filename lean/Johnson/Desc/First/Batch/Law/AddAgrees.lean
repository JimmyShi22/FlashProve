-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AddAgrees.lean
(kind K9): THEOREMS OF AGREEMENT: K9's OWN TEXT OF THE ADDING OF A CLAIM
(Batch/Add.lean: weightNext, addEntry, addSlot, addForm, addRun, addRuns, addOne, addList) AGAINST
THE FUNCTIONS addClaim, addAll (Johnson/Desc/Claim.lean; over OnBytes/Model/Hide.lean:
Fork.kap, Fork.push and OnBytes/Model/Trees.lean: Fork.pushRuns).
Each is stated as an equation between the own text's answer, its refusals' names forgotten
(Except.toOption), and the other function's value:
  addEntry_older, addSlot_older, addRun_older, addRuns_older   at all arguments.
  addForm_older      where the one equation has not been made yet (Fork.push asks it; the
                     own text asks it once, in weightNext).
  weightNext_older   WHERE THERE IS A MARK (kapMapF is not empty).
  addOne_toOption    **(addOne F cl).toOption = addClaim F cl, where there is a mark.**
  addOne_older       **addOne F cl = .ok G → addClaim F cl = some G: AT ALL ARGUMENTS** (a yes of
                     the own text has found a mark).
  addOne_newer       addClaim F cl = some G → there is a mark → addOne F cl = .ok G.
  addOne_marks       a yes keeps the number of marks.
  addList_older, addList_newer   the like of a list of claims.
  parts              WHERE THE TWO PART, shown at a written record: with no mark at all addClaim
                     adds a claim; the own text refuses. THERE IS NO OTHER PLACE: with a
                     mark the two are equal (addOne_toOption); with none the own text refuses all
                     (marks_of_weightNext).
So a law of the form "where addAll returns, ..." holds at every yes of addList. NOT carried: a
sentence that addAll returns somewhere (Law/Ledger.lean's witness for it is the record of "parts",
at which the own text refuses); the statements T1, T3, k9Law (Law/Statements.lean, Count.lean) stay
sentences on addClaim.

-/
import Johnson.Desc.First.Batch.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans weightNext entryThere addEntry addSlot addForm runFitsRow
  addRun addRuns addOne addList)

/-! ## An answer with its refusal's name forgotten -/

theorem toOption_some {α : Type} {x : Ans α} {a : α} : x.toOption = some a ↔ x = .ok a := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | ok b => exact ⟨fun h => by rw [Option.some.inj h], fun h => by rw [Except.ok.inj h]; rfl⟩

theorem toOption_bind {α β : Type} (x : Ans α) (f : α → Ans β) :
    (x >>= f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

theorem toOption_need {α : Type} (n : String) (b : Bool) (f : Unit → Ans α) :
    (K9.need n b >>= f).toOption = if b then (f ()).toOption else none := by
  cases b <;> rfl

theorem ans_bind {α β : Type} {x : Ans α} {f : α → Ans β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem need_true {n : String} {b : Bool} {u : Unit} (h : K9.need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => exact nomatch h

theorem foldlM_older {α β : Type} (f : β → α → Ans β) (g : β → α → Option β)
    (h : ∀ b a, (f b a).toOption = g b a) :
    ∀ (l : List α) (b : β), (l.foldlM f b).toOption = l.foldlM g b
  | [], _ => rfl
  | a :: l, b => by
    rw [List.foldlM_cons, List.foldlM_cons, toOption_bind, h]
    cases g b a with
    | none => rfl
    | some c => exact foldlM_older f g h l c

theorem arr_older {α β : Type} (f : β → α → Ans β) (g : β → α → Option β)
    (h : ∀ b a, (f b a).toOption = g b a) (l : Array α) (b : β) :
    (l.foldlM f b).toOption = l.foldlM g b := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact foldlM_older f g h l.toList b

/-! ## The parts -/

theorem addEntry_older (w : E) (trees : Array HTree) (x : Ent) :
    (addEntry w trees x).toOption = Fork.pushEnt w trees x := by
  unfold addEntry Fork.pushEnt
  rw [toOption_need]
  rfl

theorem addSlot_older (w : E) (ns : Nat) (LS : Array E) (x : Nat × E) :
    (addSlot w ns LS x).toOption = Fork.pushSlot w ns LS x := by
  unfold addSlot Fork.pushSlot
  rw [toOption_need]
  by_cases h : x.1 < ns <;> simp [h] <;> rfl

theorem addRun_older (w : E) (trees : Array HTree) (r : Run2) :
    (addRun w trees r).toOption = pushRun w trees r := by
  unfold addRun pushRun
  rw [toOption_need]
  rfl

theorem addRuns_older (F : Fork) (w : E) (runs : Array Run2) :
    (addRuns F w runs).toOption = F.pushRuns w runs := by
  unfold addRuns Fork.pushRuns
  simp only []
  rw [toOption_bind, arr_older _ _ (addRun_older w)]
  cases runs.foldlM (pushRun w) F.trees <;> rfl

theorem addForm_older (F : Fork) (w : E) (a : Aff) (hd : F.doorShutF = false) :
    (addForm F w a).toOption = F.push w a := by
  unfold addForm Fork.push
  simp only [hd, Bool.false_eq_true, if_false]
  rw [toOption_bind, arr_older _ _ (addEntry_older w)]
  cases a.ents.foldlM (Fork.pushEnt w) F.trees with
  | none => rfl
  | some t =>
    show ((a.slots.foldlM (addSlot w F.ns) F.LS) >>= fun LS' => (pure _ : Ans Fork)).toOption = _
    rw [toOption_bind, arr_older _ _ (addSlot_older w F.ns)]
    cases a.slots.foldlM (Fork.pushSlot w F.ns) F.LS <;> rfl

/-- What a yes of weightNext is. -/
theorem weightNext_ok (F : Fork) (x : E × Fork) (h : weightNext F = .ok x) :
    F.doorShutF = false ∧ F.thetaDrawnF = true ∧ F.nClaim < F.planClaimsF ∧
      F.kapMapF.size = F.planClaimsF ∧ F.kapMapF.getD F.nClaim true = false ∧
      x = (powE F.theta F.nClaim,
        { F with kapMapF := F.kapMapF.set! F.nClaim true, nClaim := F.nClaim + 1 }) := by
  unfold weightNext at h
  obtain ⟨_, n1, h⟩ := ans_bind h
  obtain ⟨_, n2, h⟩ := ans_bind h
  obtain ⟨_, n3, h⟩ := ans_bind h
  have h1 := need_true n1
  have h2 := need_true n2
  have h3 := need_true n3
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h1 h3
  exact ⟨h1, h2, h3.1.1, h3.1.2, h3.2, (Except.ok.inj h).symm⟩

theorem weightNext_older (F : Fork) (hm : F.kapMapF.isEmpty = false) :
    (weightNext F).toOption = F.kap := by
  unfold weightNext Fork.kap Fork.kapTake Fork.kapAt
  rw [toOption_need, toOption_need, toOption_need]
  cases F.doorShutF <;> cases F.thetaDrawnF <;>
    cases (decide (F.nClaim < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
      !F.kapMapF.getD F.nClaim true) <;> simp [hm] <;> rfl

/-- A yes of the own text has found a mark. -/
theorem marks_of_weightNext (F : Fork) (x : E × Fork) (h : weightNext F = .ok x) :
    F.kapMapF.isEmpty = false := by
  obtain ⟨_, _, h3, h4, _, _⟩ := weightNext_ok F x h
  have : F.kapMapF.size ≠ 0 := by omega
  simpa using this

/-! ## One claim -/

/-- **The own text against addClaim, where there is a mark.** -/
theorem addOne_toOption (F : Fork) (cl : Claim) (hm : F.kapMapF.isEmpty = false) :
    (addOne F cl).toOption = addClaim F cl := by
  unfold addOne addClaim
  simp only []
  rw [toOption_bind, weightNext_older F hm]
  cases hk : weightNext F with
  | error e =>
    have : F.kap = none := by rw [← weightNext_older F hm, hk]; rfl
    rw [this]
    rfl
  | ok x =>
    have hx : F.kap = some x := by rw [← weightNext_older F hm, hk]; rfl
    obtain ⟨d1, _, d3, _, _, ex⟩ := weightNext_ok F x hk
    have dx : x.2.doorShutF = false := by rw [ex]; exact d1
    rw [hx]
    cases he : cl.eqFirst with
    | none =>
      show ((addForm x.2 x.1 cl.form) >>= fun G => addRuns G x.1 cl.runs).toOption =
        (x.2.push x.1 cl.form).bind (·.pushRuns x.1 cl.runs)
      rw [toOption_bind, addForm_older _ _ _ dx]
      cases x.2.push x.1 cl.form with
      | none => rfl
      | some G => exact addRuns_older G _ _
    | some first =>
      show ((addForm x.2 (powE F.theta (F.planClaimsF + first)) cl.form) >>= fun G =>
          addRuns G (powE F.theta (F.planClaimsF + first)) cl.runs).toOption =
        (if F.nClaim < F.planClaimsF then some (powE F.theta (F.planClaimsF + first))
          else none).bind fun k => (x.2.push k cl.form).bind (·.pushRuns k cl.runs)
      rw [if_pos d3]
      show _ = (x.2.push (powE F.theta (F.planClaimsF + first)) cl.form).bind
        (·.pushRuns (powE F.theta (F.planClaimsF + first)) cl.runs)
      rw [toOption_bind, addForm_older _ _ _ dx]
      cases x.2.push (powE F.theta (F.planClaimsF + first)) cl.form with
      | none => rfl
      | some G => exact addRuns_older G _ _

theorem weightNext_of_addOne (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    ∃ x, weightNext F = .ok x := by
  unfold addOne at h
  simp only [] at h
  cases hk : weightNext F with
  | error e =>
    rw [hk] at h
    exact nomatch h
  | ok x => exact ⟨x, rfl⟩

/-- **A yes of the own text is a yes of addClaim, with the same record: at all
arguments.** -/
theorem addOne_older (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    addClaim F cl = some G := by
  obtain ⟨x, hx⟩ := weightNext_of_addOne F G cl h
  rw [← addOne_toOption F cl (marks_of_weightNext F x hx), h]
  rfl

/-- The converse, where there is a mark. -/
theorem addOne_newer (F G : Fork) (cl : Claim) (h : addClaim F cl = some G)
    (hm : F.kapMapF.isEmpty = false) : addOne F cl = .ok G :=
  toOption_some.mp ((addOne_toOption F cl hm).trans h)

/-- A yes keeps the number of marks. -/
theorem addOne_marks (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    G.kapMapF.size = F.kapMapF.size := by
  unfold addOne at h
  simp only [] at h
  obtain ⟨x, hx, h⟩ := ans_bind h
  obtain ⟨G1, h1, h2⟩ := ans_bind h
  obtain ⟨_, _, _, _, _, ex⟩ := weightNext_ok F x hx
  unfold addForm at h1
  simp only [] at h1
  obtain ⟨t, _, h1⟩ := ans_bind h1
  obtain ⟨l, _, h1⟩ := ans_bind h1
  unfold addRuns at h2
  simp only [] at h2
  obtain ⟨t', _, h2⟩ := ans_bind h2
  rw [← Except.ok.inj h2, ← Except.ok.inj h1, ex]
  simp

/-! ## A list of claims -/

/-- **A yes of the own text on a list is a yes of addAll, with the same record: at all
arguments.** -/
theorem addList_older : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    addAll F cls = some G
  | [], F, G, h => by
    have e : F = G := Except.ok.inj h
    rw [e]
    rfl
  | cl :: l, F, G, h => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := ans_bind h
    unfold addAll
    rw [List.foldlM_cons, addOne_older F F1 cl h1]
    exact addList_older l F1 G h2

/-- The converse, where there is a mark. -/
theorem addList_newer : ∀ (cls : List Claim) (F G : Fork), addAll F cls = some G →
    F.kapMapF.isEmpty = false → addList F cls = .ok G
  | [], F, G, h, _ => by
    have e : F = G := Option.some.inj h
    rw [e]
    rfl
  | cl :: l, F, G, h, hm => by
    unfold addAll at h
    rw [List.foldlM_cons] at h
    cases h1 : addClaim F cl with
    | none =>
      rw [h1] at h
      exact nomatch h
    | some F1 =>
      rw [h1] at h
      have n1 := addOne_newer F F1 cl h1 hm
      have hm1 : F1.kapMapF.isEmpty = false := by
        have hs := addOne_marks F F1 cl n1
        have h0 : F.kapMapF.size ≠ 0 := by simpa using hm
        have : F1.kapMapF.size ≠ 0 := by omega
        simpa using this
      unfold addList
      rw [List.foldlM_cons, n1]
      exact addList_newer l F1 G h hm1

/-! ## Where the two part -/

/-- A written record: chi is drawn; no mark at all. -/
def noMarks : Fork := { thetaDrawnF := true }

/-- **With no mark at all addClaim adds a claim; the own text refuses.** -/
theorem parts : (addClaim noMarks {}).isSome = true ∧ (addOne noMarks {}).toOption = none := by
  constructor <;> decide +kernel

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.addOne_toOption
#print axioms VerifiableInference.Desc.K9L.addOne_older
#print axioms VerifiableInference.Desc.K9L.addOne_newer
#print axioms VerifiableInference.Desc.K9L.addOne_marks
#print axioms VerifiableInference.Desc.K9L.addList_older
#print axioms VerifiableInference.Desc.K9L.addList_newer
#print axioms VerifiableInference.Desc.K9L.parts
