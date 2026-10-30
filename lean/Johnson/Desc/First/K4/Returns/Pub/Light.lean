-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Light.lean: a lighter test for the panels' public readings of the
sub-protocol K4's batched sumcheck: pansL does what pansB (PansB.lean) does, without sorting the
panels and without building the two forms of the end.

  WD              what is read of a step's result: whether it is there, and the bits of the down
                  product's panel.
  sidesThere      the sides of a panel are there at all its rows and columns.
  endStepL        one panel's step on that number of bits alone. It reads neither the challenges nor
                  the panel's first place.
  stackEndOf_light   where the step's first test passes, stackEndOf's result read so is endStepL's.
  stackEndL, stackEnd_light   the whole, at placed panels, against the panels as they were listed.
  returned_63     where the end returns at placed panels, no panel has fewer than lam - 63 bits.
  placesL, places_sum         the number of all places is the sum of the panels' sizes.
  pansL           THE LIGHTER TEST.
  pansB_eq_L      the two tests have one answer.

Limits. NO FILE OF THIS FOLDER PROVES THE TEST TRUE AT ANY PLAN: Johnson/Road/K4/C/PansBPlan.lean
has pansB, which has this test's answer (pansB_eq_L), as a conditional law, and no plan is shown at
which that law's hypotheses hold. #guard is Lean's evaluator and gives no proof. This folder's
tests evaluate it at the small synthetic plan (LightTest.lean) and at the library's own small
configuration (MidTest.lean) alone. It still makes every form of every side to ask whether the form
is there: one reading for each row and column of each panel.
No property is claimed.
-/
import Johnson.Desc.First.K4.Returns.Pub.PansB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2)
open OnBytes.Road (placeStep placeOrder wOf placePanels_eq place_keeps placePanels_size)

/-! ## What is read of a step's result -/

/-- What is read of a step's result: whether it is there, and the bits of the down product's
panel. -/
def WD (x : Option StackEnd) (r : Option Nat) : Prop := x.map (·.wD) = r

theorem WD.neg {c : Prop} [Decidable c] {x z : Option StackEnd} {r : Option Nat} (hc : ¬ c)
    (h : WD x r) : WD (if c then z else x) r := by
  rw [if_neg hc]
  exact h

theorem WD.ite {c : Prop} [Decidable c] {x z : Option StackEnd} {r t : Option Nat} (h1 : WD x r)
    (h2 : WD z t) : WD (if c then x else z) (if c then r else t) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact h1
  · rw [if_neg h, if_neg h]
    exact h2

theorem WD.bind_same {α : Type} {o : Option α} {f : α → Option StackEnd} {g : α → Option Nat}
    (h : ∀ a, WD (f a) (g a)) : WD (o >>= f) (o.bind g) := by
  cases o
  · rfl
  · exact h _

theorem WD.bind_keep {x : Option StackEnd} {k : StackEnd → Option StackEnd} {r : Option Nat}
    (hx : WD x r) (hk : ∀ s, WD (k s) (some s.wD)) : WD (x >>= k) r := by
  cases x
  · exact hx
  · exact (hk _).trans hx

theorem WD.bind_both {x : Option StackEnd} {k : StackEnd → Option StackEnd} {r : Option Nat}
    {g : Nat → Option Nat} (hx : WD x r) (hk : ∀ s, WD (k s) (g s.wD)) :
    WD (x >>= k) (r >>= g) := by
  unfold WD at hx
  subst hx
  cases x
  · rfl
  · exact hk _

theorem WD.step {α : Type} (o : Option α) {k : α → Option StackEnd} {q : Bool} {n : Nat}
    (h : ∀ a, WD (k a) (if q = true then some n else none)) :
    WD (o >>= k) (if (o.isSome && q) = true then some n else none) := by
  cases o
  · rfl
  · exact h _

theorem WD.step_one {α : Type} (o : Option α) {k : α → Option StackEnd} {n : Nat}
    (h : ∀ a, WD (k a) (some n)) :
    WD (o >>= k) (if o.isSome = true then some n else none) := by
  cases o
  · rfl
  · exact h _

/-- A fold whose step is there where a test on the member passes, and keeps the number. -/
theorem WD.foldlM {α : Type} {f : StackEnd → α → Option StackEnd} {p : α → Bool}
    (h : ∀ s x, WD (f s x) (if p x = true then some s.wD else none)) :
    ∀ (l : List α) (s : StackEnd),
      WD (l.foldlM f s) (if l.all p = true then some s.wD else none)
  | [], _ => rfl
  | x :: l, s => by
    rw [List.foldlM_cons, List.all_cons]
    have h0 := h s x
    cases hp : p x with
    | false =>
      rw [hp] at h0
      cases hf : f s x with
      | none => rfl
      | some c =>
        rw [hf] at h0
        cases h0
    | true =>
      rw [hp] at h0
      cases hf : f s x with
      | none =>
        rw [hf] at h0
        cases h0
      | some c =>
        rw [hf] at h0
        have e : c.wD = s.wD := Option.some.inj h0
        have h1 := WD.foldlM h l c
        rw [e] at h1
        exact h1

/-! ## One panel's step -/

/-- The sides of a panel are there at all its rows and columns. A: its A side. -/
def sidesThere (b : SBlk) (A : Nat → Nat → Option Aff) : Bool :=
  (List.range b.ni).all fun i => (List.range b.ny).all fun yv =>
    (A i yv).isSome && (b.v0.isSome || b.B.any fun B => (B i yv).isSome)

/-- One panel's step on the bits of the down product's panel alone. -/
def endStepL (y : Lay) (wD : Nat) (b : SBlk) : Option Nat :=
  if b.tri then
    b.v0.bind fun _ =>
      match b.virt with
      | some _ => if b.wy != y.lfe then none else some wD
      | none => some wD
  else
    match b.virt with
    | some _ => b.v0.bind fun _ => if wD != 0 then none else some b.w
    | none => b.A.bind fun A => if sidesThere b A then some wD else none

/-- **Where the step's first test passes, stackEndOf's result read so is endStepL's.** -/
theorem stackEndOf_light (y : Lay) {rs : Array E} {lam : Nat} (om H1 V : Array E) (s : StackEnd)
    {b : SBlk} (hI : eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) :
    WD (stackEndOf y rs lam om H1 V s b) (endStepL y s.wD b) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  have hc : ¬ (!eqIndexOK (rs.extract w lam) (off / 2 ^ w)) = true := by
    rw [show eqIndexOK (rs.extract w lam) (off / 2 ^ w) = true from hI]
    exact Bool.false_ne_true
  unfold stackEndOf endStepL sidesThere
  cases tri with
  | true =>
    cases virt with
    | some k =>
      simp only [↓reduceIte]
      exact WD.neg hc (WD.bind_same (o := v0) fun _ => WD.ite rfl rfl)
    | none =>
      simp only [↓reduceIte]
      exact WD.neg hc (WD.bind_same (o := v0) fun _ => rfl)
  | false =>
    cases virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact WD.neg hc (WD.bind_same (o := v0) fun _ => WD.ite rfl rfl)
    | none =>
      cases v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine WD.neg hc (WD.bind_same (o := A) fun f => ?_)
        refine WD.foldlM (fun a i => WD.bind_keep ?_ fun _ => by exact rfl) _ _
        exact WD.foldlM (fun c yv => WD.step (f i yv) fun _ => by exact rfl) _ _
      | none =>
        cases B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine WD.neg hc (WD.bind_same (o := A) fun f => ?_)
          refine WD.foldlM (fun a i => WD.bind_keep ?_ fun _ => by exact rfl) _ _
          exact WD.foldlM (fun c yv => WD.step (f i yv) fun _ => by exact rfl) _ _
        | some g =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine WD.neg hc (WD.bind_same (o := A) fun f => ?_)
          refine WD.foldlM (fun a i => WD.bind_keep ?_ fun _ => by exact rfl) _ _
          exact WD.foldlM (fun c yv => WD.step (f i yv) fun _ =>
            WD.step_one (g i yv) fun _ => by exact rfl) _ _

/-! ## The whole, at placed panels -/

/-- A panel with another first place. -/
def Moved (b b0 : SBlk) : Prop := ∃ o, b = { b0 with off := o }

theorem all2_of_getD {α β : Type} {R : α → β → Prop} (d : α) (d' : β) :
    ∀ (l : List α) (l' : List β), l.length = l'.length →
      (∀ i, i < l.length → R (l.getD i d) (l'.getD i d')) → All2 R l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l, b :: l', h, hr => by
    have h0 := hr 0 (Nat.zero_lt_succ _)
    rw [List.getD_cons_zero, List.getD_cons_zero] at h0
    refine .cons h0 (all2_of_getD d d' l l' (Nat.succ.inj h) fun i hi => ?_)
    have h1 := hr (i + 1) (Nat.succ_lt_succ hi)
    rw [List.getD_cons_succ, List.getD_cons_succ] at h1
    exact h1

/-- The placed panels are the listed ones, each with another first place. -/
theorem placed_moved (bl : Array SBlk) : All2 Moved (placePanels bl).1.toList bl.toList := by
  refine all2_of_getD {} {} _ _ ?_ fun i hi => ?_
  · rw [Array.length_toList, Array.length_toList, placePanels_size]
  · have hi' : i < bl.size := by
      rw [Array.length_toList, placePanels_size] at hi
      exact hi
    obtain ⟨o, ho⟩ := place_keeps bl (placeOrder bl) (bl, 0) i hi'
    rw [← placePanels_eq] at ho
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_toList, ← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?]
    exact ⟨o, ho⟩

/-- The end over all panels, on the bits of the down product's panel alone. -/
def stackEndL (y : Lay) (bl : Array SBlk) : Bool :=
  (bl.toList.foldlM (endStepL y) 0).any (· == y.h.ll + y.lPf)

theorem foldlM_light (y : Lay) {rs : Array E} {lam : Nat} (om H1 V : Array E) {l l0 : List SBlk}
    (hl : All2 Moved l l0) :
    (∀ b ∈ l, eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) → ∀ s : StackEnd,
      WD (l.foldlM (stackEndOf y rs lam om H1 V) s) (l0.foldlM (endStepL y) s.wD) := by
  induction hl with
  | nil => exact fun _ _ => rfl
  | @cons b b0 l l0 h0 _ ih =>
    intro hI s
    obtain ⟨o, rfl⟩ := h0
    rw [List.foldlM_cons, List.foldlM_cons]
    exact WD.bind_both (stackEndOf_light y om H1 V s (hI _ List.mem_cons_self))
      (ih fun c hc => hI c (List.mem_cons_of_mem _ hc))

theorem last_test (n t : Nat) (s : StackEnd) :
    (if (n != t) = true then none else some s).isSome = (n == t) := by
  unfold bne
  cases (n == t) <;> rfl

/-- **The end at placed panels**, against the panels as they were listed. -/
theorem stackEnd_light (y : Lay) {bl : Array SBlk} {lam : Nat} {rs : Array E} (om H1 V : Array E)
    (a b : E) (hN : (ceilLog2 (placePanels bl).2 == lam) = true) (hr : rs.size = lam)
    (h63 : ∀ b ∈ bl.toList, lam - b.w ≤ 63) :
    (stackEnd y (placePanels bl).1 rs lam om H1 V a b).isSome = stackEndL y bl := by
  have key := foldlM_light y om H1 V (placed_moved bl) (placed_index hN hr h63)
    { As := a, Bs := b }
  unfold stackEnd stackEndL
  rw [← Array.foldlM_toList]
  unfold WD at key
  rw [← show _ = bl.toList.foldlM (endStepL y) 0 from key]
  cases (placePanels bl).1.toList.foldlM (stackEndOf y rs lam om H1 V) { As := a, Bs := b } with
  | none => rfl
  | some s => exact last_test s.wD _ s

/-- Of two lists related member by member, each member of the right one has a partner on the
left. -/
theorem all2_mem_right {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : All2 R l l') : ∀ c ∈ l', ∃ b ∈ l, R b c := by
  induction h with
  | nil => exact fun _ hc => by cases hc
  | cons h0 _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with e | hc'
    · subst e
      exact ⟨_, List.mem_cons_self, h0⟩
    · obtain ⟨b, hb, hr⟩ := ih c hc'
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- Where the end returns at placed panels and lam challenges, no panel has fewer than lam - 63
bits. -/
theorem returned_63 {y : Lay} {bl : Array SBlk} {lam : Nat} {rs om H1 V : Array E} {a b : E}
    (hr : rs.size = lam)
    (h : (stackEnd y (placePanels bl).1 rs lam om H1 V a b).isSome = true) :
    ∀ c ∈ bl.toList, lam - c.w ≤ 63 := by
  intro c hc
  obtain ⟨fin, hf⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨d, hd, o, rfl⟩ := all2_mem_right (placed_moved bl) c hc
  obtain ⟨s1, s2, e⟩ := Road.stackEnd_each hf _ hd
  have hk := Road.stackEndOf_ok e
  unfold eqIndexOK at hk
  rw [Bool.and_eq_true, decide_eq_true_eq, Array.size_extract, hr, Nat.min_self] at hk
  exact hk.1

/-! ## The number of all places -/

/-- The sum of the panels' sizes. -/
def placesL (bl : Array SBlk) : Nat := ((List.range bl.size).map fun i => 2 ^ wOf bl i).sum

theorem place_snd (bl : Array SBlk) : ∀ (l : List Nat) (s : Array SBlk × Nat),
    (l.foldl (placeStep bl) s).2 = s.2 + (l.map fun i => 2 ^ wOf bl i).sum
  | [], _ => rfl
  | a :: l, s => by
    rw [List.foldl_cons, place_snd bl l, List.map_cons, List.sum_cons]
    show s.2 + 2 ^ wOf bl a + _ = _
    exact Nat.add_assoc _ _ _

/-- **The number of all places is the sum of the panels' sizes.** -/
theorem places_sum (bl : Array SBlk) : (placePanels bl).2 = placesL bl := by
  have perm : (placeOrder bl).Perm (List.range bl.size) := List.mergeSort_perm _ _
  rw [placePanels_eq, place_snd, Nat.zero_add]
  exact (perm.map _).sum_eq

/-! ## The lighter test -/

/-- **THE LIGHTER TEST.** The arguments are pansB's. -/
def pansL (P : Pub) (v₀ : Env) (lamS NCLp : Nat) : Bool :=
  match callsTS P with
  | none => false
  | some TS =>
    match panelsT ⟨v₀, #[], #[], #[], stubO P.y⟩ TS (panelsA ⟨v₀, #[], #[], #[], stubO P.y⟩ {}) with
    | none => false
    | some pans =>
      ceilLog2 (placesL pans.bl) == lamS && pans.nextV == NCLp &&
        pans.bl.toList.all (fun b => decide (lamS - b.w ≤ 63)) && stackEndL P.y pans.bl

/-- **The two tests have one answer.** -/
theorem pansB_eq_L (P : Pub) (v₀ : Env) (lamS NCLp : Nat) :
    pansB P v₀ lamS NCLp = pansL P v₀ lamS NCLp := by
  unfold pansB pansL
  cases callsTS P with
  | none => rfl
  | some TS =>
    dsimp only
    cases panelsT ⟨v₀, #[], #[], #[], stubO P.y⟩ TS (panelsA ⟨v₀, #[], #[], #[], stubO P.y⟩ {}) with
    | none => rfl
    | some pans =>
      dsimp only
      rw [places_sum]
      cases h1 : ceilLog2 (placesL pans.bl) == lamS with
      | false => rfl
      | true =>
        cases pans.nextV == NCLp with
        | false => rfl
        | true =>
          have hN : (ceilLog2 (placePanels pans.bl).2 == lamS) = true := by
            rw [places_sum]
            exact h1
          cases hA : pans.bl.toList.all (fun b => decide (lamS - b.w ≤ 63)) with
          | true =>
            exact stackEnd_light P.y #[] #[] #[] zeroE zeroE hN Array.size_replicate fun b hb =>
              of_decide_eq_true (List.all_eq_true.mp hA b hb)
          | false =>
            cases hX : (stackEnd P.y (placePanels pans.bl).1 (Array.replicate lamS zeroE) lamS #[]
                #[] #[] zeroE zeroE).isSome with
            | false => rfl
            | true =>
              have h63 := returned_63 Array.size_replicate hX
              have : pans.bl.toList.all (fun b => decide (lamS - b.w ≤ 63)) = true :=
                List.all_eq_true.mpr fun b hb => decide_eq_true (h63 b hb)
              rw [hA] at this
              cases this

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.WD.neg
#print axioms OnBytes.Desc.First.K4.RtPub.WD.ite
#print axioms OnBytes.Desc.First.K4.RtPub.WD.bind_same
#print axioms OnBytes.Desc.First.K4.RtPub.WD.bind_keep
#print axioms OnBytes.Desc.First.K4.RtPub.WD.bind_both
#print axioms OnBytes.Desc.First.K4.RtPub.WD.step
#print axioms OnBytes.Desc.First.K4.RtPub.WD.step_one
#print axioms OnBytes.Desc.First.K4.RtPub.WD.foldlM
#print axioms OnBytes.Desc.First.K4.RtPub.stackEndOf_light
#print axioms OnBytes.Desc.First.K4.RtPub.all2_of_getD
#print axioms OnBytes.Desc.First.K4.RtPub.placed_moved
#print axioms OnBytes.Desc.First.K4.RtPub.foldlM_light
#print axioms OnBytes.Desc.First.K4.RtPub.last_test
#print axioms OnBytes.Desc.First.K4.RtPub.stackEnd_light
#print axioms OnBytes.Desc.First.K4.RtPub.all2_mem_right
#print axioms OnBytes.Desc.First.K4.RtPub.returned_63
#print axioms OnBytes.Desc.First.K4.RtPub.place_snd
#print axioms OnBytes.Desc.First.K4.RtPub.places_sum
#print axioms OnBytes.Desc.First.K4.RtPub.pansB_eq_L
