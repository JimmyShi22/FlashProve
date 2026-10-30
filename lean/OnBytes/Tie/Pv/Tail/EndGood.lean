-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndGood.lean: a way to show of a whole routine of a sub-proof's check that it
adds its claims by the steps of OnBytes/Tie/Pv/Led/LedAdds.lean, and that every form that it adds
names entries of one array alone.

Definitions, theorems with their proofs, and one tactic. A claim is added by `SubM.lin f`. The form
f is made before, by routines that return forms and by the forms' operations. So two things are
followed through a routine's text: what it does to the state, and what it returns.

Main names:
  `InU t0 a`: every entry of the form a lies in array t0.
  `AddsIn t0 F G`: G comes from F by a walk (`Adds`, OnBytes/Tie/Pv/Led/LedAdds.lean) that adds a
    list of forms, each with `InU t0`. `AddsIn.refl`, `AddsIn.trans`, `AddsIn.ofKeeps`,
    `AddsIn.ofLin`.
  `HasGood α`: what it is for a value of the type α to hold such forms alone: for a form, `InU`; for
    an array, a list, a pair: for each part; for any other type, unless it is said otherwise:
    nothing.
  `Good t0 a`: the value a is so. A class, so that instance search carries it through the forms'
    operations.
  `PresQ t0 x`: wherever the routine x returns, `AddsIn t0` holds from the state before to the state
    after, and what it returns is good. Laws for a value, for «x, then f», for lifted calls, reads,
    loops and folds, and for the basic steps.
  `walkQ`: the tactic.

Limits: one direction: from a run that returns. The list of forms is found behind the run: that it
is the same list for every batching element is not said. Nothing on the virtual rows that the
entries name. Nothing on claims with runs (`t2Lin`).


-/
import OnBytes.Tie.Pv.Led.LedWalk
import OnBytes.Tie.Pv.Tail.EndLoops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Forms
open OnBytes OnBytes.Model OnBytes.Road.Rows

/-- Every entry of the form lies in array t0. -/
def InU (t0 : Nat) (a : Aff) : Prop := ∀ e ∈ a.ents.toList, e.tree = t0

/-- G comes from F by a walk that adds forms with entries in array t0 alone. -/
def AddsIn (t0 : Nat) (F G : Fork) : Prop := ∃ l, Adds F l G ∧ ∀ a ∈ l, InU t0 a

/-- No step. -/
theorem AddsIn.refl (t0 : Nat) (F : Fork) : AddsIn t0 F F :=
  ⟨[], Adds.nil F, fun _ h => absurd h (List.not_mem_nil)⟩

/-- One walk behind another. -/
theorem AddsIn.trans {t0 : Nat} {F G H : Fork} (a : AddsIn t0 F G) (b : AddsIn t0 G H) :
    AddsIn t0 F H := by
  obtain ⟨l, h1, q1⟩ := a
  obtain ⟨l', h2, q2⟩ := b
  refine ⟨l ++ l', h1.trans h2, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with h | h
  · exact q1 x h
  · exact q2 x h

/-- A step that adds nothing. -/
theorem AddsIn.ofKeeps {t0 : Nat} {F G : Fork} (k : Keeps F G) : AddsIn t0 F G :=
  ⟨[], Adds.keep (Adds.nil F) k, fun _ h => absurd h (List.not_mem_nil)⟩

/-- A claim. -/
theorem AddsIn.ofLin {t0 : Nat} {F G : Fork} {f : Aff} (h : F.lin f = some G) (q : InU t0 f) :
    AddsIn t0 F G :=
  ⟨[] ++ [f], Adds.lin (Adds.nil F) h, fun a ha => by
    obtain rfl : a = f := by simpa using ha
    exact q⟩

/-! ## Values -/

/-- What it is for a value of the type to hold forms with entries in one array alone. -/
class HasGood (α : Type) where
  good : Nat → α → Prop

/-- Unless it is said otherwise: nothing is asked. -/
instance (priority := low) unaskedGood (α : Type) : HasGood α := ⟨fun _ _ => True⟩

/-- What is asked of a value of this type. -/
instance : HasGood Aff := ⟨InU⟩

/-- What is asked of a value of this type. -/
instance {α : Type} [HasGood α] : HasGood (Array α) :=
  ⟨fun t a => ∀ x ∈ a.toList, HasGood.good t x⟩

/-- What is asked of a value of this type. -/
instance {α : Type} [HasGood α] : HasGood (List α) := ⟨fun t a => ∀ x ∈ a, HasGood.good t x⟩

/-- What is asked of a value of this type. -/
instance {α β : Type} [HasGood α] [HasGood β] : HasGood (α × β) :=
  ⟨fun t a => HasGood.good t a.1 ∧ HasGood.good t a.2⟩

/-- What is asked of a value of this type. -/
instance {α β : Type} [HasGood α] [HasGood β] : HasGood (MProd α β) :=
  ⟨fun t a => HasGood.good t a.fst ∧ HasGood.good t a.snd⟩

/-- What is asked of a value of this type. -/
instance {β : Type} [HasGood β] : HasGood (ForInStep β) :=
  ⟨fun t s => match s with
    | .done b => HasGood.good t b
    | .yield b => HasGood.good t b⟩

/-- The value is good. -/
class Good (t0 : Nat) {α : Type} [HasGood α] (a : α) : Prop where
  out : HasGood.good t0 a

/-- Every value of the type is good. -/
class Unasked (α : Type) [HasGood α] : Prop where
  all : ∀ (t : Nat) (a : α), HasGood.good t a

/-- Where nothing is asked, every value is good. -/
instance (priority := low) unasked_self (α : Type) : @Unasked α (unaskedGood α) :=
  ⟨fun _ _ => trivial⟩

/-- Nothing is asked of a value of this type. -/
instance {α : Type} [HasGood α] [Unasked α] : Unasked (Array α) := ⟨fun t _ x _ => Unasked.all t x⟩

/-- Nothing is asked of a value of this type. -/
instance {α : Type} [HasGood α] [Unasked α] : Unasked (List α) := ⟨fun t _ x _ => Unasked.all t x⟩

/-- Nothing is asked of a value of this type. -/
instance {α β : Type} [HasGood α] [HasGood β] [Unasked α] [Unasked β] : Unasked (α × β) :=
  ⟨fun t a => ⟨Unasked.all t a.1, Unasked.all t a.2⟩⟩

/-- Nothing is asked of a value of this type. -/
instance {α β : Type} [HasGood α] [HasGood β] [Unasked α] [Unasked β] : Unasked (MProd α β) :=
  ⟨fun t a => ⟨Unasked.all t a.fst, Unasked.all t a.snd⟩⟩

variable {t0 : Nat}

/-- A value of a type of which nothing is asked. -/
instance good_unasked {α : Type} [HasGood α] [Unasked α] (a : α) : Good t0 a := ⟨Unasked.all t0 a⟩

/-! ## The forms' operations -/

instance good_ofConst (v : E) : Good t0 (Aff.ofConst v) :=
  ⟨fun e he => by simp [Aff.ofConst] at he⟩

/-- A slot has no entry. -/
instance good_slot (j : Nat) : Good t0 (Aff.slot j) := ⟨fun e he => by simp [Aff.slot] at he⟩

/-- The form 0 has no entry. -/
instance good_empty : Good t0 ({} : Aff) := ⟨fun e he => by simp at he⟩

/-- An entry of array t0. -/
instance good_ent (r i : Nat) : Good t0 (Aff.ent t0 r i) :=
  ⟨fun e he => by
    obtain rfl : e = _ := by simpa [Aff.ent] using he
    rfl⟩

/-- The entries of a + k b: those of a, and those of b with other coefficients. -/
theorem addMul_tree (k : E) : ∀ (l : List Ent) (acc : Array Ent) (e : Ent),
    e ∈ (l.foldl (fun s x => s.push { x with coef := mulE x.coef k }) acc).toList →
    e ∈ acc.toList ∨ ∃ x ∈ l, e.tree = x.tree
  | [], _, _, h => Or.inl h
  | y :: l, acc, e, h => by
    rw [List.foldl_cons] at h
    rcases addMul_tree k l _ e h with h1 | ⟨x, hx, ex⟩
    · rcases (by simpa using h1 : e ∈ acc.toList ∨ e = { y with coef := mulE y.coef k }) with
        h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨y, List.mem_cons_self, by rw [h2]⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, ex⟩

/-- The form a + k b. -/
instance good_addMul (a b : Aff) (k : E) [ha : Good t0 a] [hb : Good t0 b] :
    Good t0 (Aff.addMul a b k) :=
  ⟨fun e he => by
    have he' : e ∈ (b.ents.toList.foldl (fun s x => s.push { x with coef := mulE x.coef k })
        a.ents).toList := by
      simpa [Aff.addMul, Array.foldl_toList] using he
    rcases addMul_tree k _ _ e he' with h | ⟨x, hx, ex⟩
    · exact ha.out e h
    · rw [ex]
      exact hb.out x hx⟩

/-- The form k a. -/
instance good_scale (a : Aff) (k : E) [Good t0 a] : Good t0 (Aff.scale a k) :=
  good_addMul {} a k

/-- A sum. -/
instance good_add (a b : Aff) [Good t0 a] [Good t0 b] : Good t0 (a + b) := good_addMul a b oneE

/-- A difference. -/
instance good_sub (a b : Aff) [Good t0 a] [Good t0 b] : Good t0 (a - b) :=
  good_addMul a b (subE zeroE oneE)

/-! ## Pairs, loop states, arrays -/

instance good_pair {α β : Type} [HasGood α] [HasGood β] (a : α) (b : β) [ha : Good t0 a]
    [hb : Good t0 b] : Good t0 (a, b) := ⟨⟨ha.out, hb.out⟩⟩

/-- A pair's first part. -/
instance good_fst {α β : Type} [HasGood α] [HasGood β] (a : α × β) [h : Good t0 a] :
    Good t0 a.1 := ⟨h.out.1⟩

/-- A pair's second part. -/
instance good_snd {α β : Type} [HasGood α] [HasGood β] (a : α × β) [h : Good t0 a] :
    Good t0 a.2 := ⟨h.out.2⟩

/-- A loop's state. -/
instance good_mk {α β : Type} [HasGood α] [HasGood β] (a : α) (b : β) [ha : Good t0 a]
    [hb : Good t0 b] : Good t0 (MProd.mk a b) := ⟨⟨ha.out, hb.out⟩⟩

/-- The first part of a loop's state. -/
instance good_mfst {α β : Type} [HasGood α] [HasGood β] (a : MProd α β) [h : Good t0 a] :
    Good t0 a.fst := ⟨h.out.1⟩

/-- The second part of a loop's state. -/
instance good_msnd {α β : Type} [HasGood α] [HasGood β] (a : MProd α β) [h : Good t0 a] :
    Good t0 a.snd := ⟨h.out.2⟩

/-- A loop goes on. -/
instance good_yield {β : Type} [HasGood β] (b : β) [h : Good t0 b] :
    Good t0 (ForInStep.yield b) := ⟨h.out⟩

/-- A loop ends. -/
instance good_done {β : Type} [HasGood β] (b : β) [h : Good t0 b] :
    Good t0 (ForInStep.done b) := ⟨h.out⟩

/-- The empty array. -/
instance good_emptyArr {α : Type} [HasGood α] : Good t0 (#[] : Array α) :=
  ⟨fun x hx => by simp at hx⟩

/-- An array with one more member. -/
instance good_push {α : Type} [HasGood α] (a : Array α) (x : α) [ha : Good t0 a]
    [hx : Good t0 x] : Good t0 (a.push x) :=
  ⟨fun y hy => by
    rcases (by simpa using hy : y ∈ a.toList ∨ y = x) with h | h
    · exact ha.out y h
    · rw [h]
      exact hx.out⟩

/-- A member of an array, or the value given for a place outside. -/
instance good_getD {α : Type} [HasGood α] (a : Array α) (i : Nat) (d : α) [ha : Good t0 a]
    [hd : Good t0 d] : Good t0 (a.getD i d) :=
  ⟨by
    by_cases h : i < a.size
    · have e : a.getD i d = a[i] := by simp [Array.getD, h]
      rw [e]
      exact ha.out _ (by simp)
    · have e : a.getD i d = d := by simp [Array.getD, h]
      rw [e]
      exact hd.out⟩

/-! ## Routines -/

/-- Wherever the routine returns: a walk that adds forms with entries in t0 alone, and a good value.
-/
class PresQ (t0 : Nat) {α : Type} [HasGood α] (x : SubM α) : Prop where
  out : ∀ F c a G c', x F c = .ok ((a, G), c') → AddsIn t0 F G ∧ HasGood.good t0 a

/-- A routine that only returns a value. -/
instance pq_pure {α : Type} [HasGood α] (a : α) [h : Good t0 a] : PresQ t0 (pure a : SubM α) :=
  ⟨fun F _ _ _ _ hr => by
    obtain ⟨rfl, rfl, _⟩ := (Port.pure_ok _ _ _ _ _ _).1 hr
    exact ⟨AddsIn.refl _ _, h.out⟩⟩

/-- «x, then f». -/
theorem pq_bind {α β : Type} [HasGood α] [HasGood β] {x : SubM α} {f : α → SubM β}
    (hx : PresQ t0 x) (hf : ∀ a, Good t0 a → PresQ t0 (f a)) : PresQ t0 (x >>= f) :=
  ⟨fun F c b G c' h => by
    obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok _ _ _ _ _).1 h
    obtain ⟨k1, g1⟩ := hx.out F c a F1 c1 h1
    obtain ⟨k2, g2⟩ := (hf a ⟨g1⟩).out F1 c1 b G c' h2
    exact ⟨k1.trans k2, g2⟩⟩

/-- «x, then f», where x returns a pair. -/
theorem pq_bind2 {α β γ : Type} [HasGood α] [HasGood β] [HasGood γ] {x : SubM (α × β)}
    {f : α × β → SubM γ} (hx : PresQ t0 x)
    (hf : ∀ a b, Good t0 a → Good t0 b → PresQ t0 (f (a, b))) : PresQ t0 (x >>= f) :=
  pq_bind hx fun p hp => hf p.1 p.2 ⟨hp.out.1⟩ ⟨hp.out.2⟩

/-- A routine that leaves the state, with a good value. -/
theorem pq_still {α : Type} [HasGood α] {x : SubM α}
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → G = F ∧ HasGood.good t0 a) : PresQ t0 x :=
  ⟨fun F c a G c' hr => by
    obtain ⟨rfl, g⟩ := h F c a G c' hr
    exact ⟨AddsIn.refl _ _, g⟩⟩

/-- A lifted block. -/
instance pq_liftS {α : Type} [HasGood α] [Unasked α] (b : Blk α) :
    PresQ t0 (StateT.lift b : SubM α) :=
  pq_still fun F c a G c' h => by
    obtain ⟨x, c1, -, e⟩ := (OnBytes.PscRun.lift_ok b F c ((a, G), c')).1 h
    obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact ⟨rfl, Unasked.all _ _⟩

/-- The same, as the routines' texts write it. -/
instance pq_liftM {α : Type} [HasGood α] [Unasked α] (b : Blk α) : PresQ t0 (liftM b : SubM α) :=
  pq_liftS b

/-- Reading a value off the state. -/
instance pq_ask {α : Type} [HasGood α] [Unasked α] (f : Fork → Option α) : PresQ t0 (SubM.ask f) :=
  pq_still fun F _ _ _ _ h => by
    obtain ⟨_, rfl, _⟩ := (Port.ask_ok _ _ _ _ _ _).1 h
    exact ⟨rfl, Unasked.all _ _⟩

/-- A public condition. -/
instance pq_must (b : Bool) : PresQ t0 (SubM.must b) := pq_liftS _

/-- A condition on values. -/
instance pq_test (b : Bool) : PresQ t0 (SubM.test b) := pq_liftS _

/-- Reading the whole state. -/
instance pq_getF : PresQ t0 (get : SubM Fork) :=
  pq_still fun F c a G c' h => by
    have h' : (Except.ok ((F, F), c) : Except Failure ((Fork × Fork) × Ctx)) = .ok ((a, G), c') := h
    cases h'
    exact ⟨rfl, trivial⟩

/-- Unwrapping a value that is good if it is there. -/
theorem pq_get {α : Type} [HasGood α] (x : Option α) (h : ∀ a, x = some a → Good t0 a) :
    PresQ t0 (SubM.get x) :=
  pq_still fun F _ a _ _ hr => by
    obtain ⟨e, rfl, _⟩ := (Port.get_ok _ _ _ _ _ _).1 hr
    exact ⟨rfl, (h a e).out⟩

/-- Unwrapping a value of a type of which nothing is asked. -/
instance pq_getP {α : Type} [HasGood α] [Unasked α] (x : Option α) : PresQ t0 (SubM.get x) :=
  pq_get x fun a _ => good_unasked a

/-! ## Loops and folds -/

instance good_toList {α : Type} [HasGood α] (a : Array α) [h : Good t0 a] : Good t0 a.toList :=
  ⟨h.out⟩

/-- A list with its members' numbers. -/
instance good_zipIdx {α : Type} [HasGood α] (l : List α) (n : Nat) [h : Good t0 l] :
    Good t0 (l.zipIdx n) :=
  ⟨fun x hx => ⟨h.out x.1 (by
    have := List.fst_mem_of_mem_zipIdx (x := x) hx
    exact this), trivial⟩⟩

/-- A loop over a list. -/
theorem pq_loop {α β : Type} [HasGood α] [HasGood β] (f : α → β → SubM (ForInStep β))
    (hf : ∀ a b, Good t0 a → Good t0 b → PresQ t0 (f a b)) :
    ∀ (l : List α) (b : β), Good t0 l → Good t0 b → PresQ t0 (forIn l b f)
  | [], b, _, hb => by
    rw [List.forIn_nil]
    exact pq_pure b
  | a :: l, b, hl, hb => by
    rw [List.forIn_cons]
    refine pq_bind (hf a b ⟨hl.out a List.mem_cons_self⟩ hb) fun r hr => ?_
    cases r with
    | done b1 =>
      have : Good t0 b1 := ⟨hr.out⟩
      exact pq_pure b1
    | yield b1 =>
      exact pq_loop f hf l b1 ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ ⟨hr.out⟩

/-- A loop over an array. -/
theorem pq_loopArr {α β : Type} [HasGood α] [HasGood β] (f : α → β → SubM (ForInStep β))
    (hf : ∀ a b, Good t0 a → Good t0 b → PresQ t0 (f a b)) (as : Array α) (b : β)
    (ha : Good t0 as) (hb : Good t0 b) : PresQ t0 (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact pq_loop f hf as.toList b ⟨ha.out⟩ hb

/-- A loop over a range of numbers. -/
theorem pq_range {β : Type} [HasGood β] (f : Nat → β → SubM (ForInStep β))
    (hf : ∀ a b, Good t0 a → Good t0 b → PresQ t0 (f a b)) (r : Std.Legacy.Range) (b : β)
    (hb : Good t0 b) : PresQ t0 (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact pq_loop f hf _ b inferInstance hb

/-- A fold over a list. -/
theorem pq_foldlM {α β : Type} [HasGood α] [HasGood β] (f : β → α → SubM β)
    (hf : ∀ b a, Good t0 b → Good t0 a → PresQ t0 (f b a)) :
    ∀ (l : List α) (b : β), Good t0 l → Good t0 b → PresQ t0 (l.foldlM f b)
  | [], b, _, hb => by
    rw [List.foldlM_nil]
    exact pq_pure b
  | a :: l, b, hl, hb => by
    rw [List.foldlM_cons]
    exact pq_bind (hf b a hb ⟨hl.out a List.mem_cons_self⟩) fun b1 h1 =>
      pq_foldlM f hf l b1 ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ h1

/-- A fold over an array. -/
theorem pq_foldlMArr {α β : Type} [HasGood α] [HasGood β] (f : β → α → SubM β)
    (hf : ∀ b a, Good t0 b → Good t0 a → PresQ t0 (f b a)) (as : Array α) (b : β)
    (ha : Good t0 as) (hb : Good t0 b) : PresQ t0 (as.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact pq_foldlM f hf as.toList b ⟨ha.out⟩ hb

/-- A routine for each member of a list. -/
theorem pq_forM {α : Type} [HasGood α] (f : α → SubM PUnit)
    (hf : ∀ a, Good t0 a → PresQ t0 (f a)) : ∀ (l : List α), Good t0 l → PresQ t0 (l.forM f)
  | [], _ => by
    show PresQ t0 (pure PUnit.unit : SubM PUnit)
    exact pq_pure _
  | a :: l, hl => by
    show PresQ t0 (f a >>= fun _ => l.forM f)
    exact pq_bind (hf a ⟨hl.out a List.mem_cons_self⟩) fun _ _ =>
      pq_forM f hf l ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩

/-- A routine for each member of an array. -/
theorem pq_forMArr {α : Type} [HasGood α] (f : α → SubM PUnit)
    (hf : ∀ a, Good t0 a → PresQ t0 (f a)) (as : Array α) (ha : Good t0 as) :
    PresQ t0 (as.forM f) := by
  unfold Array.forM
  exact pq_foldlMArr _ (fun _ a _ h => hf a h) as _ ha inferInstance

/-- A fold of good values, outside any routine. -/
theorem good_foldl {α β : Type} [HasGood α] [HasGood β] (f : β → α → β)
    (hf : ∀ b a, Good t0 b → Good t0 a → Good t0 (f b a)) :
    ∀ (l : List α) (b : β), Good t0 l → Good t0 b → Good t0 (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, b, hl, hb => by
    rw [List.foldl_cons]
    exact good_foldl f hf l _ ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩
      (hf b a hb ⟨hl.out a List.mem_cons_self⟩)

/-- The same over an array. -/
theorem good_foldlArr {α β : Type} [HasGood α] [HasGood β] (f : β → α → β)
    (hf : ∀ b a, Good t0 b → Good t0 a → Good t0 (f b a)) (as : Array α) (b : β)
    (ha : Good t0 as) (hb : Good t0 b) : Good t0 (as.foldl f b) := by
  rw [← Array.foldl_toList]
  exact good_foldl f hf as.toList b ⟨ha.out⟩ hb

/-- An array of copies. -/
instance good_replicate {α : Type} [HasGood α] (n : Nat) (x : α) [h : Good t0 x] :
    Good t0 (Array.replicate n x) :=
  ⟨fun y hy => by
    have : y = x := by
      have h2 : y ∈ List.replicate n x := by simpa using hy
      exact List.eq_of_mem_replicate h2
    rw [this]
    exact h.out⟩

/-- An array with one member replaced. -/
instance good_set {α : Type} [HasGood α] (a : Array α) (i : Nat) (x : α) [ha : Good t0 a]
    [hx : Good t0 x] : Good t0 (a.setIfInBounds i x) :=
  ⟨fun y hy => by
    have h2 : y ∈ a.toList.set i x := by simpa using hy
    rcases List.mem_or_eq_of_mem_set h2 with h | h
    · exact ha.out y h
    · rw [h]
      exact hx.out⟩

/-- One of two values. -/
instance good_ite {α : Type} [HasGood α] (p : Prop) [Decidable p] (a b : α) [ha : Good t0 a]
    [hb : Good t0 b] : Good t0 (if p then a else b) := by
  split
  · exact ha
  · exact hb

/-! ## The basic steps -/

theorem pq_change (f : Fork → Option Fork) (hf : ∀ F G, f F = some G → AddsIn t0 F G) :
    PresQ t0 (SubM.change f) :=
  ⟨fun F c a G c' h => by
    obtain ⟨H, hH, e⟩ := (OnBytes.PscRun.change_ok f F c ((a, G), c')).1 h
    obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact ⟨hf F _ hH, trivial⟩⟩

/-- Adding a claim whose form is good. -/
instance pq_lin (f : Aff) [h : Good t0 f] : PresQ t0 (SubM.lin f) :=
  pq_change _ fun _ _ hr => AddsIn.ofLin hr h.out

/-- `SubM.paid` adds no claim. -/
instance pq_paid (i : Nat) : PresQ t0 (SubM.paid i) :=
  pq_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact AddsIn.ofKeeps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Putting a run of values under slots. -/
instance pq_hideRun (j : Nat) (v : Array E) (f : E) : PresQ t0 (SubM.change (·.hideRun j v f)) :=
  pq_change _ fun _ _ h => AddsIn.ofKeeps (hideRun_keeps h)

/-- `SubM.shown` adds no claim. -/
instance pq_shown (j : Nat) : PresQ t0 (SubM.shown j) := pq_ask _

/-- `SubM.publicPart` adds no claim. -/
instance pq_publicPart (a : Aff) : PresQ t0 (SubM.publicPart a) := pq_ask _

/-- `SubM.slot` adds no claim. -/
instance pq_slot : PresQ t0 SubM.slot := pq_ask _

/-- `SubM.claims` adds no claim. -/
instance pq_claims : PresQ t0 SubM.claims := pq_ask _

/-- The empty list. -/
instance good_nil {α : Type} [HasGood α] : Good t0 ([] : List α) :=
  ⟨fun _ h => absurd h (List.not_mem_nil)⟩

/-- A list with one more member. -/
instance good_cons {α : Type} [HasGood α] (x : α) (l : List α) [hx : Good t0 x] [hl : Good t0 l] :
    Good t0 (x :: l) :=
  ⟨fun y hy => by
    rcases List.mem_cons.1 hy with h | h
    · rw [h]
      exact hx.out
    · exact hl.out y h⟩

/-- A list as an array. -/
instance good_toArray {α : Type} [HasGood α] (l : List α) [h : Good t0 l] : Good t0 l.toArray :=
  ⟨h.out⟩

/-- A refusal never returns. -/
instance pq_refuse {α : Type} [HasGood α] (name : String) :
    PresQ t0 (liftM (refuse name : Blk α) : SubM α) :=
  ⟨fun F c a G c' h => by
    obtain ⟨x, c1, hb, -⟩ := (OnBytes.PscRun.lift_ok (refuse name : Blk α) F c ((a, G), c')).1 h
    simp [refuse, Blk.fail] at hb⟩

/-- One step of a walk through a routine's text. -/
macro "walkQ_step" : tactic => `(tactic| first
  | exact inferInstance
  | refine pq_bind2 ?_ ?_ | refine pq_bind ?_ ?_
  | refine pq_loop _ ?_ _ _ ?_ ?_ | refine pq_loopArr _ ?_ _ _ ?_ ?_
  | refine pq_range _ ?_ _ _ ?_
  | refine pq_foldlM _ ?_ _ _ ?_ ?_ | refine pq_foldlMArr _ ?_ _ _ ?_ ?_
  | refine pq_forM _ ?_ _ ?_ | refine pq_forMArr _ ?_ _ ?_
  | refine good_foldl _ ?_ _ _ ?_ ?_ | refine good_foldlArr _ ?_ _ _ ?_ ?_
  | refine @pq_pure _ _ _ _ ?_
  | refine @good_add _ _ _ ?_ ?_ | refine @good_sub _ _ _ ?_ ?_
  | refine @good_addMul _ _ _ _ ?_ ?_ | refine @good_scale _ _ _ ?_
  | intro _ | dsimp only | split)

/-- A walk through a routine's text. -/
macro "walkQ" : tactic => `(tactic| repeat' walkQ_step)

/-- `uEnt` adds no claim and returns an entry of array t0. -/
instance pq_uEnt (x : Nat) : PresQ t0 (uEnt t0 x) := by
  unfold uEnt
  walkQ

end OnBytes.Tie.Pv.Tail.Forms

#print axioms OnBytes.Tie.Pv.Tail.Forms.pq_bind
#print axioms OnBytes.Tie.Pv.Tail.Forms.good_addMul
#print axioms OnBytes.Tie.Pv.Tail.Forms.pq_uEnt
