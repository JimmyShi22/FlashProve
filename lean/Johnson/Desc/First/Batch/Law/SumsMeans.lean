-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/SumsMeans.lean
(kind K9): THEOREMS: WHAT A YES OF K9's TESTS ON THE SLOTS' COEFFICIENTS GIVES:
each test as a sentence (no block imports this file).
  freeSlot_iff   K9.freeSlot n merge F (Batch/Sums.lean) says yes IF AND ONLY IF at every slot j
                 below n: the coefficient on j is the word 0 just where j is the merge's slot.
  windowsOk_iff  K9.windowsOk ws run cls (K9/Window.lean) says yes IF AND ONLY IF for every window
                 of which the run is no owner, no pair (slot, coefficient) of the FORM of a claim
                 of cls has its slot in the window. OF A CLAIM IT READS form.slots ALONE.
  eachRun_iff    K9.eachRun (K9/Each.lean): windowsOk at the windows read behind the run, and the
                 run's list is as long as is due, where a number is due.
WHAT GIVES THE WINDOWS' TEST ITS WORTH: INSIDE THE ADDING A SLOT's COEFFICIENT IS WRITTEN FROM A
CLAIM's form.slots ALONE:
  addOne_slot    where K9's own addOne (Batch/Add.lean) returns and no pair of the claim's form
                 names slot j, the coefficient on j is the same word behind as in front: entries and
                 runs of a claim cannot reach a slot.
  addList_slot   the like of a list of claims.
  window_kept    so: a run that is no owner of a window, whose claims have passed windowsOk, leaves
                 every coefficient of the window as it was, when its claims are added.
LIMITS. window_kept is of ONE run's claims added by addList; K9.adds adds a whole segment's joined
list at once: "only the owners' claims turn the window" over a joined list wants the list cut by
runs and window_kept at each stranger's stretch: not here. The three laws read "getD j zeroE": at a
j from LS.size on both sides are the word 0: idle there. "The word 0" (isZeroE) is on raw words.
eachRun_iff's right side keeps "windowsOk .. = .ok ()": read it with windowsOk_iff.
NOT CLAIMED (K9/Each.lean's head names them): that nothing but the adding writes the coefficients
between the draw and the one equation; that the windows stand still and are the real ones; that
every claim that is added has gone through the test under its true pair.

-/
import Johnson.Desc.First.Batch.Sums
import Johnson.Desc.First.Batch.Each
import Johnson.Desc.First.Batch.Law.AddAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Window windowsOk freeSlot eachRun weightNext addForm addRuns
  addOne addList)

theorem need_iff (n : String) (b : Bool) : K9.need n b = .ok () ↔ b = true := by
  cases b with
  | true => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | false => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- **What a yes of "K9.free-slot" is.** -/
theorem freeSlot_iff (n : Nat) (merge : Option Nat) (F : Fork) :
    freeSlot n merge F = .ok () ↔
      ∀ j < n, (isZeroE (F.LS.getD j zeroE) = true ↔ merge = some j) := by
  unfold freeSlot
  rw [need_iff, List.all_eq_true]
  constructor
  · intro h j hj
    have h1 := h j (List.mem_range.2 hj)
    rw [beq_iff_eq] at h1
    rw [h1, beq_iff_eq]
  · intro h j hj
    have h1 := h j (List.mem_range.1 hj)
    rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq]
    exact h1

theorem forM_iff {α : Type} (f : α → Ans Unit) :
    ∀ l : List α, l.forM f = .ok () ↔ ∀ a ∈ l, f a = .ok ()
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | a :: l => by
    rw [show (a :: l).forM f = (f a >>= fun _ => l.forM f) from rfl]
    constructor
    · intro h
      obtain ⟨u, h1, h2⟩ := ans_bind h
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h1
      · exact (forM_iff f l).1 h2 b hb
    · intro h
      rw [h a List.mem_cons_self]
      exact (forM_iff f l).2 fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- The claim's form has a pair whose slot lies in the window. -/
theorem namedBy_iff (w : Window) (cl : Claim) :
    w.namedBy cl = true ↔ ∃ x ∈ cl.form.slots, w.first ≤ x.1 ∧ x.1 < w.behind := by
  unfold Window.namedBy Window.holds
  rw [← Array.any_toList, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact ⟨x, Array.mem_toList_iff.1 hx, h⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, Array.mem_toList_iff.2 hx, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact h

/-- **What a yes of "K9.window" is.** -/
theorem windowsOk_iff (ws : List Window) (run : Nat × String) (cls : List Claim) :
    windowsOk ws run cls = .ok () ↔
      ∀ w ∈ ws, run ∉ w.owners → ∀ cl ∈ cls, ∀ x ∈ cl.form.slots,
        ¬ (w.first ≤ x.1 ∧ x.1 < w.behind) := by
  unfold windowsOk
  rw [forM_iff]
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  rw [need_iff, Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true', ← Bool.not_eq_true,
    List.any_eq_true]
  constructor
  · intro h hn cl hcl x hx hw
    rcases h with h | h
    · exact hn h
    · exact h ⟨cl, hcl, (namedBy_iff w cl).2 ⟨x, hx, hw⟩⟩
  · intro h
    by_cases hn : run ∈ w.owners
    · exact Or.inl hn
    · refine Or.inr ?_
      rintro ⟨cl, hcl, hb⟩
      obtain ⟨x, hx, hw⟩ := (namedBy_iff w cl).1 hb
      exact h hn cl hcl x hx hw

/-- **What a yes of the test behind a run is.** -/
theorem eachRun_iff {T : Type} (ws : T → List Window)
    (due : Nat × String → T → Option (String × Nat)) (run : Nat × String) (cls : List Claim)
    (t : T) :
    eachRun ws due run cls t = .ok () ↔
      windowsOk (ws t) run cls = .ok () ∧ ∀ d, due run t = some d → cls.length = d.2 := by
  unfold eachRun
  constructor
  · intro h
    obtain ⟨u, h1, h2⟩ := ans_bind h
    refine ⟨h1, fun d hd => ?_⟩
    rw [hd] at h2
    exact beq_iff_eq.1 ((need_iff _ _).1 h2)
  · rintro ⟨h1, h2⟩
    rw [h1]
    show (match due run t with
      | none => (pure () : Ans Unit)
      | some d => K9.need d.1 (cls.length == d.2)) = .ok ()
    cases hd : due run t with
    | none => rfl
    | some d => exact (need_iff _ _).2 (beq_iff_eq.2 (h2 d hd))

/-! ## Inside the adding a slot's coefficient is written from form.slots alone -/

theorem addSlot_other (w : E) (ns j : Nat) (LS l : Array E) (x : Nat × E)
    (h : K9.addSlot w ns LS x = .ok l) (hx : x.1 ≠ j) : l.getD j zeroE = LS.getD j zeroE := by
  unfold K9.addSlot at h
  obtain ⟨_, _, h⟩ := ans_bind h
  rw [← Except.ok.inj h]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hx]

theorem addSlots_other (w : E) (ns j : Nat) : ∀ (xs : List (Nat × E)) (LS l : Array E),
    xs.foldlM (K9.addSlot w ns) LS = .ok l → (∀ x ∈ xs, x.1 ≠ j) →
    l.getD j zeroE = LS.getD j zeroE
  | [], LS, l, h, _ => by rw [← Except.ok.inj h]
  | x :: xs, LS, l, h, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨l1, h1, h2⟩ := ans_bind h
    rw [addSlots_other w ns j xs l1 l h2 fun y hy => hx y (List.mem_cons_of_mem _ hy),
      addSlot_other w ns j LS l1 x h1 (hx x List.mem_cons_self)]

/-- **A claim whose form names no pair at slot j leaves the coefficient on j.** -/
theorem addOne_slot (F G : Fork) (cl : Claim) (j : Nat) (h : addOne F cl = .ok G)
    (hj : ∀ x ∈ cl.form.slots, x.1 ≠ j) : G.LS.getD j zeroE = F.LS.getD j zeroE := by
  unfold addOne at h
  simp only [] at h
  obtain ⟨x, hx, h⟩ := ans_bind h
  obtain ⟨G1, h1, h2⟩ := ans_bind h
  obtain ⟨_, _, _, _, _, ex⟩ := weightNext_ok F x hx
  unfold addForm at h1
  simp only [] at h1
  obtain ⟨t, _, h1⟩ := ans_bind h1
  obtain ⟨l, hl, h1⟩ := ans_bind h1
  unfold addRuns at h2
  simp only [] at h2
  obtain ⟨t', _, h2⟩ := ans_bind h2
  rw [← Array.foldlM_toList] at hl
  have e := addSlots_other _ _ j _ _ l hl fun y hy => hj y (Array.mem_toList_iff.1 hy)
  have eG : G.LS = l := by rw [← Except.ok.inj h2, ← Except.ok.inj h1]
  have eF : x.2.LS = F.LS := by rw [ex]
  rw [eG, e, eF]

/-- The like of a list of claims. -/
theorem addList_slot (j : Nat) : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    (∀ cl ∈ cls, ∀ x ∈ cl.form.slots, x.1 ≠ j) → G.LS.getD j zeroE = F.LS.getD j zeroE
  | [], F, G, h, _ => by rw [← Except.ok.inj h]
  | cl :: l, F, G, h, hj => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := ans_bind h
    rw [addList_slot j l F1 G h2 fun c hc => hj c (List.mem_cons_of_mem _ hc),
      addOne_slot F F1 cl j h1 (hj cl List.mem_cons_self)]

/-- **A run that is no owner of a window leaves the window's coefficients**, when its claims, which
have passed the windows' test, are added. -/
theorem window_kept (ws : List Window) (run : Nat × String) (cls : List Claim) (F G : Fork)
    (hw : windowsOk ws run cls = .ok ()) (h : addList F cls = .ok G) (w : Window) (hws : w ∈ ws)
    (hn : run ∉ w.owners) (j : Nat) (h1 : w.first ≤ j) (h2 : j < w.behind) :
    G.LS.getD j zeroE = F.LS.getD j zeroE :=
  addList_slot j cls F G h fun cl hcl x hx e =>
    (windowsOk_iff ws run cls).1 hw w hws hn cl hcl x hx (by rw [e]; exact ⟨h1, h2⟩)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.freeSlot_iff
#print axioms VerifiableInference.Desc.K9L.windowsOk_iff
#print axioms VerifiableInference.Desc.K9L.eachRun_iff
#print axioms VerifiableInference.Desc.K9L.addOne_slot
#print axioms VerifiableInference.Desc.K9L.addList_slot
#print axioms VerifiableInference.Desc.K9L.window_kept
