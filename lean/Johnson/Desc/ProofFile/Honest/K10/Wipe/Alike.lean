-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Alike.lean: the closing of a segment (K10): the words in which "a member of a
chain does the same at two states that are one under w" is said, and their general laws. General in the state's type σ
and in a function w : σ → σ; w s is called the wiped state. No kind of member is named. Eleven definitions; the rest are
theorems.

  AlikeE w r r'   two outcomes are alike under w: both refuse with one word, or both return, with values that are
                  one under w. It is the equation r.map w = r'.map w.
  grpShape, SameG   groups of columns, as a member's decide is handed them, of the same positions and widths
  Decides2, Fn2, FnCl2, Test2, Whole2   a member's decide, a change of the state, a run of claims, a test, and a member
                  with all its runs: from two states that are one under w the outcomes are alike under w; the claims
                  of a run are equal
  NoCols          a member's decide does not look at its columns
  wCl, wStep      w on the state beside a list of claims, or beside a number

What is proved. (1) How AlikeE is made and taken apart: of_eq, eq, of_same, ok, error, split, ok_left, rfl', symm,
trans. (2) How it goes through a bind, a map, a test under a name, a value under a name, and a text laid in front of a
refusal's word; a map goes through a bind and through a map. (3) The entrances: Fn2, FnCl2, Test2 and Decides2 each
follow from a law on one state, "the function at the wiped state against the function at the state"; Whole2 has no
entrance of its own. Test2.same: a test with that property has equal outcomes. (4) Laws of SameG and SameShape.

By what. Sections 2 and 3: cases on the two outcomes. Section 4: the law at s, the premise w s = w s', the law at s'. No
text outside this file needs to unfold AlikeE: split, ok and error serve.

Limits. Nothing says what w is, and the properties are shown of no member here. No property of the protocol is claimed:
nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.WipeFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block OpenedColumn)

variable {σ Cl : Type}

/-! ## 1 The definitions -/

/-- Two outcomes are alike under w: both refuse with one word, or both return values that are one under w. -/
def AlikeE {α β : Type} (w : α → β) (r r' : Except String α) : Prop := r.map w = r'.map w

/-- A group of columns as decide is handed it: positions and widths. -/
def grpShape (g : List (Nat × List UInt64)) : List (Nat × Nat) := g.map fun c => (c.1, c.2.length)

/-- Two lists of groups have the same positions and widths, group by group. -/
def SameG (gs gs' : List (List (Nat × List UInt64))) : Prop := gs.map grpShape = gs'.map grpShape

/-- A member's decide has like outcomes at states that are one under w and at groups of one shape. -/
def Decides2 (w : σ → σ) (b : Block σ Cl) : Prop :=
  ∀ (s s' : σ) (rs : List Fmt.RoundView) (gs gs' : List (List (Nat × List UInt64))), w s = w s' → SameG gs gs' →
    AlikeE w (b.decide s rs gs) (b.decide s' rs gs')

/-- A change of the state, which may refuse, has like outcomes at states that are one under w. -/
def Fn2 (w : σ → σ) (f : σ → Except String σ) : Prop := ∀ s s', w s = w s' → AlikeE w (f s) (f s')

/-- w on the state beside a list of claims; the claims stay. -/
def wCl (w : σ → σ) (y : List Cl × σ) : List Cl × σ := (y.1, w y.2)

/-- A run of claims returns equal claims and like states at states that are one under w. -/
def FnCl2 (w : σ → σ) (f : σ → Except String (List Cl × σ)) : Prop :=
  ∀ s s', w s = w s' → AlikeE (wCl w) (f s) (f s')

/-- A test has one outcome at states that are one under w. -/
def Test2 (w : σ → σ) (t : σ → Except String Unit) : Prop :=
  ∀ s s', w s = w s' → AlikeE (id : Unit → Unit) (t s) (t s')

/-- A member's decide, each of its runs of claims and each of its runs behind the batching have these properties. -/
def Whole2 (w : σ → σ) (b : Block σ Cl) : Prop :=
  Decides2 w b ∧ (∀ c ∈ b.claims, ∀ n, FnCl2 w (c.2 n)) ∧ ∀ c ∈ b.after, Fn2 w c.2

/-- A member's decide does not look at its columns. -/
def NoCols (b : Block σ Cl) : Prop :=
  ∀ (s : σ) (rs : List Fmt.RoundView) (gs gs' : List (List (Nat × List UInt64))), b.decide s rs gs = b.decide s rs gs'

/-- w on the state beside a number; the number stays. -/
def wStep (w : σ → σ) (y : σ × Nat) : σ × Nat := (w y.1, y.2)

/-! ## 2 How AlikeE is made and taken apart -/

section laws
variable {α β γ δ : Type} {w : α → β} {v : γ → δ} {r r' r'' : Except String α}

/-- The equation is the property. -/
theorem AlikeE.of_eq (h : r.map w = r'.map w) : AlikeE w r r' := h

/-- The property is the equation. -/
theorem AlikeE.eq (h : AlikeE w r r') : r.map w = r'.map w := h

/-- Equal outcomes are alike. -/
theorem AlikeE.of_same (h : r = r') : AlikeE w r r' := by
  subst h
  exact (rfl : r.map w = r.map w)

/-- An outcome is like itself. -/
theorem AlikeE.rfl' : AlikeE w r r := (rfl : r.map w = r.map w)

/-- Alike the other way round. -/
theorem AlikeE.symm (h : AlikeE w r r') : AlikeE w r' r := by
  unfold AlikeE at h ⊢
  exact Eq.symm h

/-- Alike through a third outcome. -/
theorem AlikeE.trans (h : AlikeE w r r') (h' : AlikeE w r' r'') : AlikeE w r r'' := by
  unfold AlikeE at h h' ⊢
  exact Eq.trans h h'

/-- Two outcomes that return values that are one under w are alike. -/
theorem AlikeE.ok {a a' : α} (h : w a = w a') : AlikeE w (Except.ok a) (Except.ok a') := by
  show (Except.ok (w a) : Except String β) = Except.ok (w a')
  rw [h]

/-- Two refusals with one word are alike. -/
theorem AlikeE.error (e : String) : AlikeE w (Except.error e) (Except.error e) :=
  (rfl : (Except.error e : Except String β) = Except.error e)

/-- **Like outcomes, taken apart**: one word at both, or two values that are one under w. -/
theorem AlikeE.split (h : AlikeE w r r') :
    (∃ e, r = Except.error e ∧ r' = Except.error e) ∨
      ∃ a a', r = Except.ok a ∧ r' = Except.ok a' ∧ w a = w a' := by
  unfold AlikeE at h
  cases r with
  | error e =>
    cases r' with
    | error e' =>
      have he : e = e' := Except.error.inj h
      subst he
      exact Or.inl ⟨e, rfl, rfl⟩
    | ok a' => cases h
  | ok a =>
    cases r' with
    | error e' => cases h
    | ok a' => exact Or.inr ⟨a, a', rfl, rfl, Except.ok.inj h⟩

/-- Where the left outcome returns, so does the right one, a value that is the same under w. -/
theorem AlikeE.ok_left {a : α} (h : AlikeE w r r') (e : r = Except.ok a) :
    ∃ a', r' = Except.ok a' ∧ w a = w a' := by
  rcases h.split with ⟨e', h1, _⟩ | ⟨b, b', h1, h2, hb⟩
  · rw [e] at h1
    cases h1
  · rw [e] at h1
    have hab : a = b := Except.ok.inj h1
    subst hab
    exact ⟨b', h2, hb⟩

/-! ## 3 Through a bind, a map, a test, a named value, a new head on a word -/

/-- Two binds are alike where their heads are alike and their tails are alike at like values. -/
theorem AlikeE.bind {x x' : Except String α} {f f' : α → Except String γ} (h : AlikeE w x x')
    (k : ∀ a a', w a = w a' → AlikeE v (f a) (f' a')) : AlikeE v (x.bind f) (x'.bind f') := by
  rcases h.split with ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    exact AlikeE.error e
  · subst h1 h2
    exact k a a' ha

/-- The same, written with the monad's sign. -/
theorem AlikeE.bind' {x x' : Except String α} {f f' : α → Except String γ} (h : AlikeE w x x')
    (k : ∀ a a', w a = w a' → AlikeE v (f a) (f' a')) : AlikeE v (x >>= f) (x' >>= f') :=
  AlikeE.bind h k

/-- Two binds with one head are alike where their tails are, at each value that the head returns. -/
theorem AlikeE.head_ok {x : Except String α} {f f' : α → Except String γ}
    (k : ∀ a, x = Except.ok a → AlikeE v (f a) (f' a)) : AlikeE v (x.bind f) (x.bind f') := by
  cases x with
  | error e => exact AlikeE.error e
  | ok a => exact k a rfl

/-- The same, written with the monad's sign. -/
theorem AlikeE.head_ok' {x : Except String α} {f f' : α → Except String γ}
    (k : ∀ a, x = Except.ok a → AlikeE v (f a) (f' a)) : AlikeE v (x >>= f) (x >>= f') :=
  AlikeE.head_ok k

/-- Two binds with one head are alike where their tails are. -/
theorem AlikeE.head {x : Except String α} {f f' : α → Except String γ}
    (k : ∀ a, AlikeE v (f a) (f' a)) : AlikeE v (x.bind f) (x.bind f') :=
  AlikeE.head_ok fun a _ => k a

/-- The same, written with the monad's sign. -/
theorem AlikeE.head' {x : Except String α} {f f' : α → Except String γ}
    (k : ∀ a, AlikeE v (f a) (f' a)) : AlikeE v (x >>= f) (x >>= f') :=
  AlikeE.head_ok fun a _ => k a

/-- Two binds with equal heads are alike where their tails are. -/
theorem AlikeE.head_eq {x x' : Except String α} {f f' : α → Except String γ} (hx : x = x')
    (k : ∀ a, AlikeE v (f a) (f' a)) : AlikeE v (x.bind f) (x'.bind f') := by
  subst hx
  exact AlikeE.head k

/-- The same, written with the monad's sign. -/
theorem AlikeE.head_eq' {x x' : Except String α} {f f' : α → Except String γ} (hx : x = x')
    (k : ∀ a, AlikeE v (f a) (f' a)) : AlikeE v (x >>= f) (x' >>= f') :=
  AlikeE.head_eq hx k

/-- Two maps are alike where what is mapped is alike and the two functions keep like values alike. -/
theorem AlikeE.map {x x' : Except String α} {g g' : α → γ} (h : AlikeE w x x')
    (k : ∀ a a', w a = w a' → v (g a) = v (g' a')) : AlikeE v (x.map g) (x'.map g') := by
  rcases h.split with ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    exact AlikeE.error e
  · subst h1 h2
    exact AlikeE.ok (k a a' ha)

/-- Two binds behind a test under a name are alike where the test asks one Bool and the two tails are alike. -/
theorem AlikeE.need {n : String} {b b' : Bool} {k k' : Except String γ} (hb : b = b') (h : AlikeE v k k') :
    AlikeE v (VerifiableInference.Desc.need n b >>= fun _ => k)
      (VerifiableInference.Desc.need n b' >>= fun _ => k') := by
  subst hb
  exact AlikeE.head' fun _ => h

/-- Two binds behind a value under a name are alike where both values lack or are one under w, and the tails are
alike. -/
theorem AlikeE.named {n : String} {o o' : Option α} {f f' : α → Except String γ} (ho : o.map w = o'.map w)
    (k : ∀ a a', w a = w a' → AlikeE v (f a) (f' a')) :
    AlikeE v (VerifiableInference.Desc.named n o >>= f) (VerifiableInference.Desc.named n o' >>= f') := by
  cases o with
  | none =>
    cases o' with
    | none => exact AlikeE.error n
    | some a' => cases ho
  | some a =>
    cases o' with
    | none => cases ho
    | some a' => exact k a a' (Option.some.inj ho)

/-- Two values under one name are alike where both lack or they are one under w. -/
theorem AlikeE.named_alone {n : String} {o o' : Option α} (ho : o.map w = o'.map w) :
    AlikeE w (VerifiableInference.Desc.named n o) (VerifiableInference.Desc.named n o') := by
  cases o with
  | none =>
    cases o' with
    | none => exact AlikeE.error n
    | some a' => cases ho
  | some a =>
    cases o' with
    | none => cases ho
    | some a' => exact AlikeE.ok (Option.some.inj ho)

/-- Like outcomes stay alike where one text is laid in front of a refusal's word. -/
theorem AlikeE.reword (h : AlikeE w r r') (p : String) :
    AlikeE w (match r with | .ok y => .ok y | .error e => .error (p ++ e))
      (match r' with | .ok y => .ok y | .error e => .error (p ++ e)) := by
  rcases h.split with ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · subst h1 h2
    exact AlikeE.error (p ++ e)
  · subst h1 h2
    exact AlikeE.ok ha

/-- A map goes through a bind, to the bind's tail. -/
theorem emap_bind (x : Except String α) (f : α → Except String γ) (v : γ → δ) :
    (x.bind f).map v = x.bind fun a => (f a).map v := by
  cases x with
  | error e => rfl
  | ok a => rfl

/-- The same, written with the monad's sign. -/
theorem emap_bind' (x : Except String α) (f : α → Except String γ) (v : γ → δ) :
    (x >>= f).map v = x >>= fun a => (f a).map v := emap_bind x f v

/-- A map behind a map is one map. -/
theorem emap_map (x : Except String α) (g : α → γ) (v : γ → δ) : (x.map g).map v = x.map fun a => v (g a) := by
  cases x with
  | error e => rfl
  | ok a => rfl

end laws

/-! ## 4 The entrances: a law on one state -/

section entrances
variable {w : σ → σ}

/-- The strict law: f at the wiped state is f at the state with w laid on what it returns. It gives Fn2. -/
theorem Fn2.of_comm {f : σ → Except String σ} (h : ∀ s, f (w s) = (f s).map w) : Fn2 w f := by
  intro s s' hs
  have e : (f s).map w = (f s').map w := by rw [← h s, ← h s', hs]
  exact e

/-- The weak law: f has like outcomes at the wiped state and at the state. It gives Fn2. -/
theorem Fn2.of_wiped {f : σ → Except String σ} (h : ∀ s, AlikeE w (f (w s)) (f s)) : Fn2 w f := by
  intro s s' hs
  have h2 : AlikeE w (f (w s)) (f s') := by
    rw [hs]
    exact h s'
  exact (h s).symm.trans h2

/-- The strict law for a run of claims gives FnCl2. -/
theorem FnCl2.of_comm {f : σ → Except String (List Cl × σ)} (h : ∀ s, f (w s) = (f s).map (wCl w)) :
    FnCl2 w f := by
  intro s s' hs
  have e : (f s).map (wCl w) = (f s').map (wCl w) := by rw [← h s, ← h s', hs]
  exact e

/-- The weak law for a run of claims gives FnCl2. -/
theorem FnCl2.of_wiped {f : σ → Except String (List Cl × σ)} (h : ∀ s, AlikeE (wCl w) (f (w s)) (f s)) :
    FnCl2 w f := by
  intro s s' hs
  have h2 : AlikeE (wCl w) (f (w s)) (f s') := by
    rw [hs]
    exact h s'
  exact (h s).symm.trans h2

/-- A test with one outcome at the wiped state and at the state has Test2. -/
theorem Test2.of_blind {t : σ → Except String Unit} (h : ∀ s, t (w s) = t s) : Test2 w t := by
  intro s s' hs
  have e : t s = t s' := by rw [← h s, ← h s', hs]
  exact AlikeE.of_same e

/-- A test that has Test2 has equal outcomes at states that are one under w. -/
theorem Test2.same {t : σ → Except String Unit} (h : Test2 w t) {s s' : σ} (hs : w s = w s') : t s = t s' := by
  rcases (h s s' hs).split with ⟨e, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · rw [h1, h2]
  · have e : a = a' := ha
    subst e
    rw [h1, h2]

/-- The strict law for a decide that looks at no column gives Decides2. -/
theorem Decides2.of_comm {b : Block σ Cl} (hn : NoCols b)
    (h : ∀ s rs gs, b.decide (w s) rs gs = (b.decide s rs gs).map w) : Decides2 w b := by
  intro s s' rs gs gs' hs _
  have e : (b.decide s rs gs).map w = (b.decide s' rs gs').map w := by
    rw [← h s rs gs, ← h s' rs gs', hs]
    exact hn (w s') rs gs gs'
  exact e

/-- The weak law for a decide that looks at no column gives Decides2. -/
theorem Decides2.of_wiped {b : Block σ Cl} (hn : NoCols b)
    (h : ∀ s rs gs, AlikeE w (b.decide (w s) rs gs) (b.decide s rs gs)) : Decides2 w b := by
  intro s s' rs gs gs' hs _
  have h2 : AlikeE w (b.decide (w s) rs gs) (b.decide s' rs gs') := by
    rw [hs, hn (w s') rs gs gs']
    exact h s' rs gs'
  exact (h s rs gs).symm.trans h2

end entrances

/-! ## 5 Shapes -/

/-- A list of groups is of one shape with itself. -/
theorem SameG.rfl' {gs : List (List (Nat × List UInt64))} : SameG gs gs := (rfl : gs.map grpShape = gs.map grpShape)

/-- Of one shape, the other way round. -/
theorem SameG.symm {gs gs' : List (List (Nat × List UInt64))} (h : SameG gs gs') : SameG gs' gs := by
  unfold SameG at h ⊢
  exact Eq.symm h

/-- The first k groups of two lists of one shape are of one shape. -/
theorem SameG.take {gs gs' : List (List (Nat × List UInt64))} (h : SameG gs gs') (k : Nat) :
    SameG (gs.take k) (gs'.take k) := by
  unfold SameG at h ⊢
  rw [List.map_take, List.map_take, h]

/-- Two lists of one shape without their first k groups are of one shape. -/
theorem SameG.drop {gs gs' : List (List (Nat × List UInt64))} (h : SameG gs gs') (k : Nat) :
    SameG (gs.drop k) (gs'.drop k) := by
  unfold SameG at h ⊢
  rw [List.map_drop, List.map_drop, h]

/-- Two lists of one shape have one length. -/
theorem SameG.length {gs gs' : List (List (Nat × List UInt64))} (h : SameG gs gs') : gs.length = gs'.length := by
  unfold SameG at h
  have e := congrArg List.length h
  rw [List.length_map, List.length_map] at e
  exact e

/-- The first k columns of two lists of one shape are of one shape. -/
theorem SameShape.take {c c' : List OpenedColumn} (h : SameShape c c') (k : Nat) : SameShape (c.take k) (c'.take k) := by
  unfold SameShape at h ⊢
  rw [List.map_take, List.map_take, h]

/-- The weak law for a decide that reads its columns, asked at any two lists of groups of one shape, gives Decides2. -/
theorem Decides2.of_wiped_cols {w : σ → σ} {b : Block σ Cl}
    (h : ∀ s rs gs gs', SameG gs gs' → AlikeE w (b.decide (w s) rs gs') (b.decide s rs gs)) : Decides2 w b := by
  intro s s' rs gs gs' hs hg
  have h1 : AlikeE w (b.decide (w s) rs gs) (b.decide s rs gs) := h s rs gs gs SameG.rfl'
  have h2 : AlikeE w (b.decide (w s) rs gs) (b.decide s' rs gs') := by
    rw [hs]
    exact h s' rs gs' gs hg.symm
  exact h1.symm.trans h2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.AlikeE
#print axioms ProofFile.Honest.K10.grpShape
#print axioms ProofFile.Honest.K10.SameG
#print axioms ProofFile.Honest.K10.Decides2
#print axioms ProofFile.Honest.K10.Fn2
#print axioms ProofFile.Honest.K10.wCl
#print axioms ProofFile.Honest.K10.FnCl2
#print axioms ProofFile.Honest.K10.Test2
#print axioms ProofFile.Honest.K10.Whole2
#print axioms ProofFile.Honest.K10.NoCols
#print axioms ProofFile.Honest.K10.wStep
#print axioms ProofFile.Honest.K10.AlikeE.of_eq
#print axioms ProofFile.Honest.K10.AlikeE.eq
#print axioms ProofFile.Honest.K10.AlikeE.of_same
#print axioms ProofFile.Honest.K10.AlikeE.rfl'
#print axioms ProofFile.Honest.K10.AlikeE.symm
#print axioms ProofFile.Honest.K10.AlikeE.trans
#print axioms ProofFile.Honest.K10.AlikeE.ok
#print axioms ProofFile.Honest.K10.AlikeE.error
#print axioms ProofFile.Honest.K10.AlikeE.split
#print axioms ProofFile.Honest.K10.AlikeE.ok_left
#print axioms ProofFile.Honest.K10.AlikeE.bind
#print axioms ProofFile.Honest.K10.AlikeE.bind'
#print axioms ProofFile.Honest.K10.AlikeE.head_ok
#print axioms ProofFile.Honest.K10.AlikeE.head_ok'
#print axioms ProofFile.Honest.K10.AlikeE.head
#print axioms ProofFile.Honest.K10.AlikeE.head'
#print axioms ProofFile.Honest.K10.AlikeE.head_eq
#print axioms ProofFile.Honest.K10.AlikeE.head_eq'
#print axioms ProofFile.Honest.K10.AlikeE.map
#print axioms ProofFile.Honest.K10.AlikeE.need
#print axioms ProofFile.Honest.K10.AlikeE.named
#print axioms ProofFile.Honest.K10.AlikeE.named_alone
#print axioms ProofFile.Honest.K10.AlikeE.reword
#print axioms ProofFile.Honest.K10.emap_bind
#print axioms ProofFile.Honest.K10.emap_bind'
#print axioms ProofFile.Honest.K10.emap_map
#print axioms ProofFile.Honest.K10.Fn2.of_comm
#print axioms ProofFile.Honest.K10.Fn2.of_wiped
#print axioms ProofFile.Honest.K10.FnCl2.of_comm
#print axioms ProofFile.Honest.K10.FnCl2.of_wiped
#print axioms ProofFile.Honest.K10.Test2.of_blind
#print axioms ProofFile.Honest.K10.Test2.same
#print axioms ProofFile.Honest.K10.Decides2.of_comm
#print axioms ProofFile.Honest.K10.Decides2.of_wiped
#print axioms ProofFile.Honest.K10.SameG.rfl'
#print axioms ProofFile.Honest.K10.SameG.symm
#print axioms ProofFile.Honest.K10.SameG.take
#print axioms ProofFile.Honest.K10.SameG.drop
#print axioms ProofFile.Honest.K10.SameG.length
#print axioms ProofFile.Honest.K10.SameShape.take
#print axioms ProofFile.Honest.K10.Decides2.of_wiped_cols
