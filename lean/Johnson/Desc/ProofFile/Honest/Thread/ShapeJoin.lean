-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeJoin.lean: THE CUT "STRUCTURE | VALUES"
(Honest/Thread/Shape.lean) AT THE LEVEL OF A RUN: a member's decide is several runs in a row, each
some group of authors' text; the chain's one shape is a product with a component for each group.
Here: the two forms (B1) and (B2) for ONE RUN; the lemma that JOINS two runs in a row; the FRAME
lemmas, by which a run that leaves a component of the shape as it was need say nothing more of it;
and THE SEAT: from a member's decide, as one run, to `Carries` and `Returns` at that member.
Definitions: premises' forms; and conditional lemmas on them. General: no kind, no state and no
shape is named.

  1  `CarriesR` (B1r), `ReturnsR` (B2r), `valsThen`   one run f : S → Except String S, its guards g
     on the shape, its named tests on values v
  2  `carries_join`, `returns_join`   two runs in a row
  3  `carries_fst`, `carries_snd`, `returns_fst`, `returns_snd`   THE FRAME: a product of two
  4  `carries_pure`, `returns_pure`   a run that asks nothing and turns nothing of the shape
     `guardsUnder`, `carries_under`, `returns_under`   ONE Bool on the shape in front of a run's
     guards (a mark that every member asks): laid once; (B2r) need then be shown under it alone
  5  `carries_guarded`, `returns_guarded`   a member under the seat's guard (`Block.guarded`)
     `carries_seat`, `returns_seat`   THE SEAT in `Block.step`

The forms. A run is taken as a function of the state alone: whatever else it reads (its rounds, its
columns, the plan) is closed over. (B1r): where the run returns AND its guards return at the
state's shape, they return the shape behind. (B2r): where the guards return and the named tests on
values pass, the run returns. Two runs in a row: the guards in a row; the second run's tests on
values are asked at the state behind the first.

The frame. (B1) at a member speaks of the WHOLE shape. With the shape a pair (c₁ s, c₂ s): a run
whose guards turn the first component alone, reading both, and which leaves c₂ as it was, has (B1r)
at the pair from (B1r) at c₁. More components: by nesting.

The seat. The two seats ask their premise at rounds and columns that FIT the member alone. (Their
first form asked it at whatever rounds and groups: an author of another thread of this project
showed by Lean, at the first real member, that neither could then be filled: at no round its
decision says no whatever the state; and its update lays the number of the round's own entries into
the shape, the guards the plan's number.)

Limits. Nothing shows that any run of a description can be written so. None is one of the library's
goals. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Sh Sh₁ Sh₂ : Type}

/-! ## 1 One run -/

/-- **(B1r)**: where the run returns and its guards return at the state's shape, they return the
shape behind. It is a definition: a premise's form. Nothing is claimed of it, and it is none of the
library's goals. -/
def CarriesR (sh : S → Sh) (f : S → Except String S) (g : Sh → Except String Sh) : Prop :=
  ∀ s s' t, f s = .ok s' → g (sh s) = .ok t → t = sh s'

/-- **(B2r)**: where the guards return and the named tests on values pass, the run returns. It is a
definition: a premise's form. Nothing is claimed of it, and it is none of the library's goals. -/
def ReturnsR (sh : S → Sh) (f : S → Except String S) (g : Sh → Except String Sh) (v : S → Bool) :
    Prop :=
  ∀ s t, g (sh s) = .ok t → v s = true → ∃ s', f s = .ok s'

/-- Two runs' tests on values, in a row: the second's at the state behind the first; true for the
second where the first run fails. -/
def valsThen (f₁ : S → Except String S) (v₁ v₂ : S → Bool) (s : S) : Bool :=
  v₁ s && match f₁ s with
    | .ok s' => v₂ s'
    | .error _ => true

/-! ## 2 Two runs in a row -/

theorem bindR_ok {α β : Type} {x : Except String α} {h : α → Except String β} {b : β}
    (e : x.bind h = .ok b) : ∃ a, x = .ok a ∧ h a = .ok b := by
  cases x with
  | error w => cases e
  | ok a => exact ⟨a, rfl, e⟩

theorem carries_join {sh : S → Sh} {f₁ f₂ : S → Except String S} {g₁ g₂ : Sh → Except String Sh}
    (h₁ : CarriesR sh f₁ g₁) (h₂ : CarriesR sh f₂ g₂) :
    CarriesR sh (fun s => (f₁ s).bind f₂) (fun a => (g₁ a).bind g₂) := by
  intro s s'' t hf hg
  obtain ⟨s', e₁, e₂⟩ := bindR_ok hf
  obtain ⟨t', d₁, d₂⟩ := bindR_ok hg
  have et := h₁ s s' t' e₁ d₁
  subst et
  exact h₂ s' s'' t e₂ d₂

theorem returns_join {sh : S → Sh} {f₁ f₂ : S → Except String S} {g₁ g₂ : Sh → Except String Sh}
    {v₁ v₂ : S → Bool} (c₁ : CarriesR sh f₁ g₁) (h₁ : ReturnsR sh f₁ g₁ v₁)
    (h₂ : ReturnsR sh f₂ g₂ v₂) :
    ReturnsR sh (fun s => (f₁ s).bind f₂) (fun a => (g₁ a).bind g₂) (valsThen f₁ v₁ v₂) := by
  intro s t hg hv
  obtain ⟨t', d₁, d₂⟩ := bindR_ok hg
  unfold valsThen at hv
  rw [Bool.and_eq_true] at hv
  obtain ⟨s', e₁⟩ := h₁ s t' d₁ hv.1
  have et := c₁ s s' t' e₁ d₁
  subst et
  have hv₂ := hv.2
  rw [e₁] at hv₂
  obtain ⟨s'', e₂⟩ := h₂ s' t d₂ hv₂
  refine ⟨s'', ?_⟩
  show (f₁ s).bind f₂ = .ok s''
  rw [e₁]
  exact e₂

/-! ## 3 The frame -/

/-- A run whose guards turn the first component alone, reading both, and which leaves the second.
-/
theorem carries_fst {c₁ : S → Sh₁} {c₂ : S → Sh₂} {f : S → Except String S}
    {g : Sh₁ × Sh₂ → Except String Sh₁}
    (hk : ∀ s s', f s = .ok s' → c₂ s' = c₂ s)
    (h : ∀ s s' t, f s = .ok s' → g (c₁ s, c₂ s) = .ok t → t = c₁ s') :
    CarriesR (fun s => (c₁ s, c₂ s)) f (fun a => (g a).map fun t => (t, a.2)) := by
  intro s s' t hf hg
  cases hq : g (c₁ s, c₂ s) with
  | error w =>
    have hg' : (g (c₁ s, c₂ s)).map (fun t => (t, c₂ s)) = .ok t := hg
    rw [hq] at hg'
    cases hg'
  | ok u =>
    have hg' : (g (c₁ s, c₂ s)).map (fun t => (t, c₂ s)) = .ok t := hg
    rw [hq] at hg'
    have et : (u, c₂ s) = t := Except.ok.inj hg'
    rw [← et]
    show (u, c₂ s) = (c₁ s', c₂ s')
    rw [h s s' u hf hq, hk s s' hf]

theorem carries_snd {c₁ : S → Sh₁} {c₂ : S → Sh₂} {f : S → Except String S}
    {g : Sh₁ × Sh₂ → Except String Sh₂}
    (hk : ∀ s s', f s = .ok s' → c₁ s' = c₁ s)
    (h : ∀ s s' t, f s = .ok s' → g (c₁ s, c₂ s) = .ok t → t = c₂ s') :
    CarriesR (fun s => (c₁ s, c₂ s)) f (fun a => (g a).map fun t => (a.1, t)) := by
  intro s s' t hf hg
  cases hq : g (c₁ s, c₂ s) with
  | error w =>
    have hg' : (g (c₁ s, c₂ s)).map (fun t => (c₁ s, t)) = .ok t := hg
    rw [hq] at hg'
    cases hg'
  | ok u =>
    have hg' : (g (c₁ s, c₂ s)).map (fun t => (c₁ s, t)) = .ok t := hg
    rw [hq] at hg'
    have et : (c₁ s, u) = t := Except.ok.inj hg'
    rw [← et]
    show (c₁ s, u) = (c₁ s', c₂ s')
    rw [h s s' u hf hq, hk s s' hf]

theorem returns_fst {c₁ : S → Sh₁} {c₂ : S → Sh₂} {f : S → Except String S}
    {g : Sh₁ × Sh₂ → Except String Sh₁} {v : S → Bool}
    (h : ∀ s t, g (c₁ s, c₂ s) = .ok t → v s = true → ∃ s', f s = .ok s') :
    ReturnsR (fun s => (c₁ s, c₂ s)) f (fun a => (g a).map fun t => (t, a.2)) v := by
  intro s t hg hv
  cases hq : g (c₁ s, c₂ s) with
  | error w =>
    have hg' : (g (c₁ s, c₂ s)).map (fun t => (t, c₂ s)) = .ok t := hg
    rw [hq] at hg'
    cases hg'
  | ok u => exact h s u hq hv

theorem returns_snd {c₁ : S → Sh₁} {c₂ : S → Sh₂} {f : S → Except String S}
    {g : Sh₁ × Sh₂ → Except String Sh₂} {v : S → Bool}
    (h : ∀ s t, g (c₁ s, c₂ s) = .ok t → v s = true → ∃ s', f s = .ok s') :
    ReturnsR (fun s => (c₁ s, c₂ s)) f (fun a => (g a).map fun t => (a.1, t)) v := by
  intro s t hg hv
  cases hq : g (c₁ s, c₂ s) with
  | error w =>
    have hg' : (g (c₁ s, c₂ s)).map (fun t => (c₁ s, t)) = .ok t := hg
    rw [hq] at hg'
    cases hg'
  | ok u => exact h s u hq hv

/-! ## 4 A run that asks nothing and turns nothing of the shape -/

theorem carries_pure {sh : S → Sh} {f : S → Except String S}
    (hk : ∀ s s', f s = .ok s' → sh s' = sh s) : CarriesR sh f .ok := by
  intro s s' t hf hg
  rw [← Except.ok.inj hg, hk s s' hf]

theorem returns_pure {sh : S → Sh} {f : S → Except String S} {v : S → Bool}
    (h : ∀ s, v s = true → ∃ s', f s = .ok s') : ReturnsR sh f .ok v :=
  fun s _ _ hv => h s hv

/-! ## 4b A Bool on the shape, laid in front of a run's guards -/

/-- A run's guards behind a Bool on the shape. -/
def guardsUnder (p : Sh → Bool) (g : Sh → Except String Sh) (a : Sh) : Except String Sh :=
  if p a then g a else .error "a guard on the shape, laid for all members"

theorem carries_under {sh : S → Sh} {f : S → Except String S} {g : Sh → Except String Sh}
    (p : Sh → Bool) (h : CarriesR sh f g) : CarriesR sh f (guardsUnder p g) := by
  intro s s' t hf hg
  unfold guardsUnder at hg
  cases hp : p (sh s) with
  | false =>
    rw [hp] at hg
    cases hg
  | true =>
    rw [hp] at hg
    exact h s s' t hf hg

/-- (B2r) need be shown under the Bool alone. -/
theorem returns_under {sh : S → Sh} {f : S → Except String S} {g : Sh → Except String Sh}
    {v : S → Bool} (p : Sh → Bool)
    (h : ∀ s t, p (sh s) = true → g (sh s) = .ok t → v s = true → ∃ s', f s = .ok s') :
    ReturnsR sh f (guardsUnder p g) v := by
  intro s t hg hv
  unfold guardsUnder at hg
  cases hp : p (sh s) with
  | false =>
    rw [hp] at hg
    cases hg
  | true =>
    rw [hp] at hg
    exact h s t hp hg hv

/-! ## 5 The seat -/

variable {Cl : Type}

/-- **A MEMBER UNDER THE SEAT's GUARD** (`Block.guarded`, Johnson/Desc/SeatGuard.lean: behind the
bare decision the wrapper compares the state behind with the state in front): (B1r) of the bare
decision gives (B1r) of the guarded one. -/
theorem carries_guarded {sh : S → Sh} {g : Sh → Except String Sh} {same : S → S → Bool}
    {but : Place → Bool} {b : Block S Cl} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : CarriesR sh (fun s => b.decide s rs gs) g) :
    CarriesR sh (fun s => (b.guarded same but).decide s rs gs) g := by
  intro s s' t hf hg
  have hf' : (if but b.place then b.decide s rs gs
      else (b.decide s rs gs).bind (seatSame same s)) = .ok s' := hf
  cases hb : but b.place with
  | true =>
    rw [hb] at hf'
    exact h s s' t hf' hg
  | false =>
    rw [hb] at hf'
    obtain ⟨a, e₁, e₂⟩ := bindR_ok hf'
    unfold seatSame at e₂
    cases hq : same s a with
    | false =>
      rw [hq] at e₂
      cases e₂
    | true =>
      rw [hq] at e₂
      have ea : a = s' := Except.ok.inj e₂
      subst ea
      exact h s a t e₁ hg

/-- (B2r) of the guarded decision wants ONE PREMISE MORE than (B2r) of the bare one: THE WRAPPER's
COMPARISON ACCEPTS WHAT THE BARE DECISION LAYS: owed by whoever seats the chain, of the seat's own
comparison. -/
theorem returns_guarded {sh : S → Sh} {g : Sh → Except String Sh} {v : S → Bool}
    {same : S → S → Bool} {but : Place → Bool} {b : Block S Cl} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ReturnsR sh (fun s => b.decide s rs gs) g v)
    (hs : ∀ s s', b.decide s rs gs = .ok s' → same s s' = true) :
    ReturnsR sh (fun s => (b.guarded same but).decide s rs gs) g v := by
  intro s t hg hv
  obtain ⟨s', e⟩ := h s t hg hv
  have e' : b.decide s rs gs = .ok s' := e
  refine ⟨s', ?_⟩
  show (if but b.place then b.decide s rs gs
    else (b.decide s rs gs).bind (seatSame same s)) = .ok s'
  cases hb : but b.place with
  | true => exact e'
  | false =>
    rw [e']
    show seatSame same s s' = .ok s'
    unfold seatSame
    rw [hs s s' e']
    rfl

/-- **THE SEAT OF (B1)**: from the member's decide, as one run AT ROUNDS AND COLUMNS THAT FIT THE
MEMBER (`Block.Fits`: what its step asks in front of its decide), to `Carries` at the member. -/
theorem carries_seat {bs : List (Block S Cl)} {ft : Nat} {Z : Shape S} {b : Nat} {blk : Block S Cl}
    (hblk : bs[b]? = some blk)
    (h : ∀ rs cols, blk.Fits ft rs cols →
      CarriesR Z.sh (fun s => blk.decide s (rs.map noDigest) (blk.shown ft rs cols)) (Z.g b)) :
    Carries bs ft Z b := by
  intro blk' hblk' s rs cols s' n t hs hg
  rw [hblk] at hblk'
  cases hblk'
  have h3 := (step_iff ft blk s s' rs cols n).1 hs
  exact h rs cols h3.1 s s' t h3.2.1 hg

/-- **THE SEAT OF (B2).** -/
theorem returns_seat {bs : List (Block S Cl)} {ft : Nat} {Z : Shape S} {b : Nat}
    {blk : Block S Cl} (hblk : bs[b]? = some blk)
    (h : ∀ rs cols, blk.Fits ft rs cols →
      ReturnsR Z.sh (fun s => blk.decide s (rs.map noDigest) (blk.shown ft rs cols)) (Z.g b)
        (fun s => Z.vals b s (rs.map noDigest) (blk.shown ft rs cols))) : Returns bs ft Z b := by
  intro blk' hblk' s rs cols t hg hF hv
  rw [hblk] at hblk'
  cases hblk'
  exact h rs cols hF s t hg hv

end ProofFile.Honest

#print axioms ProofFile.Honest.bindR_ok
#print axioms ProofFile.Honest.carries_join
#print axioms ProofFile.Honest.returns_join
#print axioms ProofFile.Honest.carries_fst
#print axioms ProofFile.Honest.carries_snd
#print axioms ProofFile.Honest.returns_fst
#print axioms ProofFile.Honest.returns_snd
#print axioms ProofFile.Honest.carries_pure
#print axioms ProofFile.Honest.returns_pure
#print axioms ProofFile.Honest.carries_under
#print axioms ProofFile.Honest.returns_under
#print axioms ProofFile.Honest.carries_guarded
#print axioms ProofFile.Honest.returns_guarded
#print axioms ProofFile.Honest.carries_seat
#print axioms ProofFile.Honest.returns_seat
