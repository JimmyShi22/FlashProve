-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/Kit.lean: the ground under the carried files of this folder: what it means that
a flat function (`Fl`, OnBytes/K/Kc/Flat.lean: from a sub-proof's ledger and a tape of rounds to
nothing, or to a value, the ledger behind and the tape left) returns, in the same words in which the
library says it of the verifier program's routines in a context (OnBytes/Tie/Pv/Psc/PscRun.lean,
OnBytes/Tie/Pv/Psc/PscView.lean, OnBytes/Tie/Pv/Lookup/Forest/FoEv.lean). Typed by hand.
Definitions, and theorems with their proofs.

Why. The library proves of the program's lookup routine, run in a context, that what it returns
holds the flat function's end values (Fo.hcOut2). A law on the verifier that runs is meant to reach
no routine in a context. The library's flat functions are that routine's text line for line, over a
ledger and a tape. The proofs touch a context only through a few laws on "returns" and through
`Evs l c c'` (the calls l of the channel's routines lead from c to c'), where l is a list of the
plain datatype `Ev`. This file gives the same laws, with the same names and the same shapes of
conjunctions, for `Fl` and a tape. The other files of the folder are then the library's own
declarations, carried over by a program under one swap of names.

Main names (each the twin of the library's declaration of that name):
  `Option.ok`: a result written as the library writes it: `.ok ((a, G), c)` is `some (a, G, c)`.
  `At`, `Evs`: one call on a tape; calls one after the other.
  `bind_ok`, `pure_ok`, `lift_ok`, `must_ok`, `get_ok`, `take_ok`, `ask_ok`, `change_ok`,
  `takeSlots_ok`, `slot_ok`, `owe_ok`, `shown_ok`, `publicPart_ok`, `foldlM_nil_ok`,
  `foldlM_cons_ok`, `readSum_ok`, `answer_ok`, `read_ok`, `empty_ok`, `point_ok`: for each way in
    which flat functions are put together, and each step on the ledger or the tape: when it
    returns, and what.
  `Clean`, `Round`, `Took`, `sentOf`, `drawnOf`, `rdRV`; `round_read`, `round_readNZ`,
  `round_values`, `round_sum`, `round_ans`, `round_point`: calls that make up a round take that
    round off the tape.
  `LawfulMonad Fl`: an instance, for List.foldlM_append.

Limits. `Clean` IS ALWAYS TRUE: on a tape no message is "open" apart from the first round's elements
that are left; it is kept so that the carried texts stay as they are, and it carries nothing. `Took
c rvs c'` says c = rvs ++ c' and no more. Of a round's entry in the plan (its name, how many draws
are never 0, its rows) the laws here hand on nothing: the flat functions test these, and the carried
statements do not speak of them. `Option.ok` stands in the namespace Option. Uses of the library's
plain data: `Ev`, `took` (OnBytes/Tie/Pv/Psc/PscRun.lean); `Fl` and its functions. That no routine
in a context is reached is meant, and is not shown in this library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.FlatHear
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A flat function's result, written as the library writes a routine's: value and ledger as a pair,
then the tape. -/
@[reducible] protected def Option.ok {α β γ : Type} (r : (α × β) × γ) : Option (α × β × γ) :=
  some (r.1.1, r.1.2, r.2)

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

theorem ok_inj {α β γ : Type} {r s : (α × β) × γ} (h : Option.ok r = Option.ok s) : r = s := by
  obtain ⟨⟨a, b⟩, c⟩ := r
  obtain ⟨⟨a', b'⟩, c'⟩ := s
  have e : (a, b, c) = (a', b', c') := Option.some.inj h
  cases e
  rfl

/-- The call, on the tape c, returns its result and leaves c'. -/
def At : Ev → Tape → Tape → Prop
  | .sum x, c, c' => recv c = some (x, c')
  | .ans r x, c, c' => closeOne r.name 0 c = some (x, c')
  | .ansNZ r x, c, c' => closeOne r.name 1 c = some (x, c')
  | .read n v, c, c' => recvN n c = some (v, c')
  | .empty r, c, c' => Fl.emptyOn r.name c = some ((), c')
  | .point r n v, c, c' => Fl.pointOn r.name n c = some (v, c')

/-- The calls of a list, one after the other. -/
def Evs : List Ev → Tape → Tape → Prop
  | [], c, c' => c' = c
  | e :: l, c, c' => ∃ c1, At e c c1 ∧ Evs l c1 c'

/-- Calls after calls. -/
theorem Evs.append : ∀ {l m : List Ev} {c c1 c2 : Tape}, Evs l c c1 → Evs m c1 c2 →
    Evs (l ++ m) c c2
  | [], _, _, _, _, h, h' => by
    obtain rfl : _ = _ := h
    exact h'
  | _ :: _, _, _, _, _, ⟨d, h0, h1⟩, h' => ⟨d, h0, Evs.append h1 h'⟩

/-- One call as a list of calls. -/
theorem Evs.one {e : Ev} {c c' : Tape} (h : At e c c') : Evs [e] c c' := ⟨c', h, rfl⟩

theorem evs_append : ∀ (l₁ l₂ : List Ev) (c c' : Tape),
    Evs (l₁ ++ l₂) c c' ↔ ∃ c₁, Evs l₁ c c₁ ∧ Evs l₂ c₁ c'
  | [], l₂, c, c' => ⟨fun h => ⟨c, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
  | e :: l₁, l₂, c, c' => by
    constructor
    · rintro ⟨c₁, h1, h2⟩
      obtain ⟨c₂, h3, h4⟩ := (evs_append l₁ l₂ c₁ c').1 h2
      exact ⟨c₂, ⟨c₁, h1, h3⟩, h4⟩
    · rintro ⟨c₂, ⟨c₁, h1, h3⟩, h4⟩
      exact ⟨c₁, h1, (evs_append l₁ l₂ c₁ c').2 ⟨c₂, h3, h4⟩⟩

theorem evs_one (e : Ev) (c c' : Tape) : Evs [e] c c' ↔ At e c c' :=
  ⟨fun ⟨_, h1, h2⟩ => h2 ▸ h1, fun h => ⟨c', h, rfl⟩⟩

/-- The flat functions' "do" is lawful: the library's proofs split a loop over a list that is laid
together of two (List.foldlM_append). -/
instance : LawfulMonad Fl := LawfulMonad.mk' Fl
  (id_map := fun x => by
    funext F t
    show Fl.andThen x (fun a => Fl.ret (id a)) F t = x F t
    unfold Fl.andThen
    cases x F t with
    | none => rfl
    | some y =>
      obtain ⟨a, G, u⟩ := y
      rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by
    funext F t
    show Fl.andThen (Fl.andThen x f) g F t = Fl.andThen x (fun a => Fl.andThen (f a) g) F t
    unfold Fl.andThen
    cases x F t with
    | none => rfl
    | some y =>
      obtain ⟨a, G, u⟩ := y
      rfl)

section Ways
variable {α β : Type}

/-- «x, then f» returns exactly if x returns and f does from there. -/
theorem bind_ok (x : Fl α) (f : α → Fl β) (F : Fork) (c : Tape) (r : (β × Fork) × Tape) :
    (x >>= f) F c = .ok r ↔ ∃ a G c1, x F c = .ok ((a, G), c1) ∧ f a G c1 = .ok r := by
  show Fl.andThen x f F c = .ok r ↔ _
  unfold Fl.andThen
  cases h : x F c with
  | none =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, _, _, e, _⟩
      cases e
  | some y =>
    obtain ⟨a, G, c1⟩ := y
    constructor
    · intro h'
      exact ⟨a, G, c1, rfl, h'⟩
    · rintro ⟨a', G', c1', e, h'⟩
      have e' : (a, G, c1) = (a', G', c1') := Option.some.inj e
      cases e'
      exact h'

/-- A function that only returns a value leaves ledger and tape. -/
theorem pure_ok (a : α) (F : Fork) (c : Tape) (r : (α × Fork) × Tape) :
    (pure a : Fl α) F c = .ok r ↔ r = ((a, F), c) := by
  constructor
  · intro h
    have h' : Option.ok ((a, F), c) = Option.ok r := h
    exact (ok_inj h').symm
  · rintro rfl
    rfl

/-- A step on the tape alone leaves the ledger. -/
theorem lift_ok (b : Tape → Option (α × Tape)) (F : Fork) (c : Tape) (r : (α × Fork) × Tape) :
    Fl.onTape b F c = .ok r ↔ ∃ a c1, b c = some (a, c1) ∧ r = ((a, F), c1) := by
  show (b c).map (fun x => (x.1, F, x.2)) = .ok r ↔ _
  cases h : b c with
  | none =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, _, e, _⟩
      cases e
  | some y =>
    obtain ⟨a, c1⟩ := y
    constructor
    · intro h'
      have h'' : Option.ok ((a, F), c1) = Option.ok r := h'
      exact ⟨a, c1, rfl, (ok_inj h'').symm⟩
    · rintro ⟨a', c1', e, rfl⟩
      have e' : (a, c1) = (a', c1') := Option.some.inj e
      cases e'
      rfl

/-- A public condition returns exactly if it is true, and leaves ledger and tape. -/
theorem must_ok (b : Bool) (F : Fork) (c : Tape) (r : (Unit × Fork) × Tape) :
    Fl.must b F c = .ok r ↔ b = true ∧ r = (((), F), c) := by
  cases b with
  | false =>
    constructor
    · intro h
      have h' : (none : Option (Unit × Fork × Tape)) = Option.ok r := h
      cases h'
    · rintro ⟨h, _⟩
      cases h
  | true =>
    constructor
    · intro h
      have h' : Option.ok (((), F), c) = Option.ok r := h
      exact ⟨rfl, (ok_inj h').symm⟩
    · rintro ⟨_, rfl⟩
      rfl

/-- Unwrapping a value returns exactly if it is there, and leaves ledger and tape. -/
theorem get_ok (x : Option α) (F : Fork) (c : Tape) (r : (α × Fork) × Tape) :
    Fl.need x F c = .ok r ↔ ∃ a, x = some a ∧ r = ((a, F), c) := by
  cases x with
  | none =>
    constructor
    · intro h
      have h' : (none : Option (α × Fork × Tape)) = Option.ok r := h
      cases h'
    · rintro ⟨_, e, _⟩
      cases e
  | some a =>
    constructor
    · intro h
      have h' : Option.ok ((a, F), c) = Option.ok r := h
      exact ⟨a, rfl, (ok_inj h').symm⟩
    · rintro ⟨a', e, rfl⟩
      cases e
      rfl

/-- A step on the ledger that returns a value leaves the tape. -/
theorem take_ok (f : Fork → Option (α × Fork)) (F : Fork) (c : Tape) (r : (α × Fork) × Tape) :
    Fl.take f F c = .ok r ↔ ∃ y, f F = some y ∧ r = (y, c) := by
  show (f F).map (fun x => (x.1, x.2, c)) = .ok r ↔ _
  cases h : f F with
  | none =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, e, _⟩
      cases e
  | some y =>
    obtain ⟨a, G⟩ := y
    constructor
    · intro h'
      have h'' : Option.ok ((a, G), c) = Option.ok r := h'
      exact ⟨(a, G), rfl, (ok_inj h'').symm⟩
    · rintro ⟨y', e, rfl⟩
      cases e
      rfl

/-- Reading a value off the ledger leaves ledger and tape. -/
theorem ask_ok (f : Fork → Option α) (F : Fork) (c : Tape) (r : (α × Fork) × Tape) :
    Fl.ask f F c = .ok r ↔ ∃ a, f F = some a ∧ r = ((a, F), c) := by
  show (f F).map (fun a => (a, F, c)) = .ok r ↔ _
  cases h : f F with
  | none =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, e, _⟩
      cases e
  | some a =>
    constructor
    · intro h'
      have h'' : Option.ok ((a, F), c) = Option.ok r := h'
      exact ⟨a, rfl, (ok_inj h'').symm⟩
    · rintro ⟨a', e, rfl⟩
      cases e
      rfl

/-- A step on the ledger leaves the tape. -/
theorem change_ok (f : Fork → Option Fork) (F : Fork) (c : Tape) (r : (Unit × Fork) × Tape) :
    Fl.change f F c = .ok r ↔ ∃ G, f F = some G ∧ r = (((), G), c) := by
  show (f F).map (fun G => ((), G, c)) = .ok r ↔ _
  cases h : f F with
  | none =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, e, _⟩
      cases e
  | some G =>
    constructor
    · intro h'
      have h'' : Option.ok (((), G), c) = Option.ok r := h'
      exact ⟨G, rfl, (ok_inj h'').symm⟩
    · rintro ⟨G', e, rfl⟩
      cases e
      rfl

end Ways

/-- Taking n slots returns the next slot and always succeeds. -/
theorem takeSlots_ok (n : Nat) (F : Fork) (c : Tape) (r : (Nat × Fork) × Tape) :
    Fl.takeSlots n F c = .ok r ↔ r = ((F.next, took F n), c) := by
  unfold Fl.takeSlots
  rw [take_ok]
  constructor
  · rintro ⟨y, e, rfl⟩
    cases e
    rfl
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

section More
variable {α : Type}

theorem slot_ok (F : Fork) (c : Tape) (r : (ℕ × Fork) × Tape) :
    Fl.slot F c = .ok r ↔ r = ((F.next, F), c) := by
  unfold Fl.slot
  rw [ask_ok]
  constructor
  · rintro ⟨a, h, rfl⟩
    rw [← Option.some.inj h]
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

theorem owe_ok (what : String) (F : Fork) (c : Tape) (r : (ℕ × Fork) × Tape) :
    Fl.owe what F c = .ok r ↔ r = (F.owe what, c) := by
  unfold Fl.owe
  rw [take_ok]
  constructor
  · rintro ⟨y, h, rfl⟩
    rw [← Option.some.inj h]
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

theorem shown_ok (j : ℕ) (F : Fork) (c : Tape) (r : (OnBytes.E × Fork) × Tape) :
    Fl.shown j F c = .ok r ↔ ∃ a, F.shown j = some a ∧ r = ((a, F), c) := ask_ok _ F c r

theorem publicPart_ok (a : Aff) (F : Fork) (c : Tape) (r : (OnBytes.E × Fork) × Tape) :
    Fl.publicPart a F c = .ok r ↔ ∃ x, F.publicPart a = some x ∧ r = ((x, F), c) := ask_ok _ F c r

theorem foldlM_nil_ok {σ : Type} (f : σ → α → Fl σ) (s : σ) (F : Fork) (c : Tape)
    (r : (σ × Fork) × Tape) : (([] : List α).foldlM f s) F c = .ok r ↔ r = ((s, F), c) :=
  pure_ok s F c r

theorem foldlM_cons_ok {σ : Type} (f : σ → α → Fl σ) (s : σ) (a : α) (l : List α) (F : Fork)
    (c : Tape) (r : (σ × Fork) × Tape) :
    ((a :: l).foldlM f s) F c = .ok r ↔
      ∃ s₁ F₁ c₁, f s a F c = .ok ((s₁, F₁), c₁) ∧ (l.foldlM f s₁) F₁ c₁ = .ok r := by
  rw [List.foldlM_cons]
  exact bind_ok _ _ F c r

theorem liftEv_ok (b : Tape → Option (α × Tape)) (e : α → Ev)
    (he : ∀ a c c', At (e a) c c' ↔ b c = some (a, c'))
    (F G : Fork) (c c' : Tape) (x : α) :
    Fl.onTape b F c = .ok ((x, G), c') ↔ Evs [e x] c c' ∧ G = F := by
  rw [lift_ok, evs_one, he]
  constructor
  · rintro ⟨a, c1, h, e1⟩
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (x = a ∧ G = F) ∧ c' = c1 := by simpa [Prod.ext_iff] using e1
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨x, c', h, rfl⟩

theorem readSum_ok (F G : Fork) (c c' : Tape) (x : OnBytes.E) :
    Fl.readSum F c = .ok ((x, G), c') ↔ Evs [.sum x] c c' ∧ G = F :=
  liftEv_ok recv Ev.sum (fun _ _ _ => Iff.rfl) F G c c' x

theorem answer_ok (r : RoundName) (F G : Fork) (c c' : Tape) (x : OnBytes.E) :
    Fl.answer r F c = .ok ((x, G), c') ↔ Evs [.ans r x] c c' ∧ G = F :=
  liftEv_ok (closeOne r.name 0) (Ev.ans r) (fun _ _ _ => Iff.rfl) F G c c' x

theorem read_ok (n : ℕ) (F G : Fork) (c c' : Tape) (v : Array OnBytes.E) :
    Fl.read n F c = .ok ((v, G), c') ↔ Evs [.read n v] c c' ∧ G = F :=
  liftEv_ok (recvN n) (Ev.read n) (fun _ _ _ => Iff.rfl) F G c c' v

theorem empty_ok (r : RoundName) (F G : Fork) (c c' : Tape) :
    Fl.empty r F c = .ok (((), G), c') ↔ Evs [.empty r] c c' ∧ G = F :=
  liftEv_ok (Fl.emptyOn r.name) (fun _ => Ev.empty r) (fun _ _ _ => Iff.rfl) F G c c' ()

theorem point_ok (r : RoundName) (n : ℕ) (F G : Fork) (c c' : Tape) (v : Array OnBytes.E) :
    Fl.point r n F c = .ok ((v, G), c') ↔ Evs [.point r n v] c c' ∧ G = F :=
  liftEv_ok (Fl.pointOn r.name n) (Ev.point r n) (fun _ _ _ => Iff.rfl) F G c c' v

end More

/-! ## Calls that make up a round take that round off the tape -/

/-- On a tape no message is open. Kept so that the carried texts stay as they are. -/
def Clean (_ : Tape) : Prop := True

/-- The elements sent in a round. -/
def sentOf (r : FlatRound) : List E := r.sent

/-- The elements drawn after a round. -/
def drawnOf (r : FlatRound) : List E := r.drawn

/-- A tape's round as plain data. -/
def rdRV {K : Type} [CommRing K] (ρ : Reading K) (r : FlatRound) : List K × List K :=
  ((sentOf r).map ρ.val, (drawnOf r).map ρ.val)

/-- The round rv is taken off the tape. -/
def Round (c : Tape) (rv : FlatRound) (c' : Tape) : Prop := Clean c ∧ Clean c' ∧ c = rv :: c'

/-- The rounds rvs are taken off the tape. -/
def Took (c : Tape) (rvs : List FlatRound) (c' : Tape) : Prop := Clean c ∧ Clean c' ∧ c = rvs ++ c'

theorem Took.nil {c : Tape} (h : Clean c) : Took c [] c := ⟨h, h, rfl⟩

theorem Round.took {c c' : Tape} {rv : FlatRound} (h : Round c rv c') : Took c [rv] c' := h

theorem Took.append {c c1 c2 : Tape} {l m : List FlatRound} (h : Took c l c1) (h' : Took c1 m c2) :
    Took c (l ++ m) c2 :=
  ⟨h.1, h'.2.1, by rw [h.2.2, h'.2.2, List.append_assoc]⟩

theorem recv_some {c c' : Tape} {x : E} (h : recv c = some (x, c')) :
    ∃ nm z w s d t, c = ⟨nm, z, w, x :: s, d⟩ :: t ∧ c' = ⟨nm, z, w, s, d⟩ :: t := by
  unfold recv at h
  split at h
  · cases h
    exact ⟨_, _, _, _, _, _, rfl, rfl⟩
  · cases h

theorem closeOne_some {name : String} {nz : Nat} {c c' : Tape} {x : E}
    (h : closeOne name nz c = some (x, c')) : ∃ nm z w, c = ⟨some nm, z, w, [], [x]⟩ :: c' := by
  unfold closeOne at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, _, rfl⟩
    · cases h
  · cases h

theorem closeN_some {name : String} {nz n : Nat} {c c' : Tape} {d : List E}
    (h : closeN name nz n c = some (d, c')) :
    d.length = n ∧ ∃ nm z w, c = ⟨some nm, z, w, [], d⟩ :: c' := by
  unfold closeN at h
  split at h
  · split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact ⟨hb.2, _, _, _, rfl⟩
    · cases h
  · cases h

theorem recvLoop_some : ∀ (n : Nat) (a v : Array E) (c c' : Tape), recvLoop n a c = some (v, c') →
    ∀ (nm : Option String) (z w : Nat) (d : List E) (t : Tape), c' = ⟨nm, z, w, [], d⟩ :: t →
    ∃ xs : List E, xs.length = n ∧ v.toList = a.toList ++ xs ∧ c = ⟨nm, z, w, xs, d⟩ :: t
  | 0, a, v, c, c', h, nm, z, w, d, t, e => by
    unfold recvLoop at h
    cases h
    exact ⟨[], rfl, by simp, e⟩
  | n + 1, a, v, c, c', h, nm, z, w, d, t, e => by
    unfold recvLoop at h
    cases hr : recv c with
    | none =>
      rw [hr] at h
      cases h
    | some y =>
      obtain ⟨x, u⟩ := y
      rw [hr] at h
      obtain ⟨xs, h1, h2, h3⟩ := recvLoop_some n (a.push x) v u c' h nm z w d t e
      obtain ⟨nm', z', w', s, d', t', e1, e2⟩ := recv_some hr
      rw [e2] at h3
      cases h3
      exact ⟨x :: xs, by simp [h1], by simp [h2], e1⟩

/-- n elements are received and the round is then closed: the round held just these. -/
theorem recvN_some {n : Nat} {v : Array E} {c c' : Tape} (h : recvN n c = some (v, c'))
    {nm : Option String} {z w : Nat} {d : List E} {t : Tape} (e : c' = ⟨nm, z, w, [], d⟩ :: t) :
    v.size = n ∧ c = ⟨nm, z, w, v.toList, d⟩ :: t := by
  obtain ⟨xs, h1, h2, h3⟩ := recvLoop_some n _ v c c' h nm z w d t e
  have h0 : (Array.emptyWithCapacity n : Array E).toList = [] := rfl
  rw [h0, List.nil_append] at h2
  rw [h2]
  refine ⟨?_, h3⟩
  rw [← Array.length_toList, h2, h1]

theorem round_read (n : Nat) (v : Array E) (r : RoundName) (x : E) (c c' : Tape) (_ : Clean c)
    (h : Evs [.read n v, .ans r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  have h1' : recvN n c = some (v, c1) := h1
  have h2' : closeOne r.name 0 c1 = some (x, c') := h2
  obtain ⟨nm, z, w, e⟩ := closeOne_some h2'
  exact ⟨⟨some nm, z, w, v.toList, [x]⟩, ⟨trivial, trivial, (recvN_some h1' e).2⟩, rfl, rfl⟩

theorem round_readNZ (n : Nat) (v : Array E) (r : RoundName) (x : E) (c c' : Tape) (_ : Clean c)
    (h : Evs [.read n v, .ansNZ r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  have h1' : recvN n c = some (v, c1) := h1
  have h2' : closeOne r.name 1 c1 = some (x, c') := h2
  obtain ⟨nm, z, w, e⟩ := closeOne_some h2'
  exact ⟨⟨some nm, z, w, v.toList, [x]⟩, ⟨trivial, trivial, (recvN_some h1' e).2⟩, rfl, rfl⟩

theorem emptyOn_some {name : String} {c c' : Tape} (h : Fl.emptyOn name c = some ((), c')) :
    ∃ nm z w, c = ⟨some nm, z, w, [], []⟩ :: c' := by
  unfold Fl.emptyOn at h
  cases hc : closeN name 0 0 c with
  | none =>
    rw [hc] at h
    cases h
  | some y =>
    obtain ⟨d, t⟩ := y
    rw [hc] at h
    have e : (((), t) : Unit × Tape) = ((), c') := Option.some.inj h
    cases e
    obtain ⟨hl, nm, z, w, e1⟩ := closeN_some hc
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact ⟨nm, z, w, e1⟩

theorem pointOn_some {name : String} {n : Nat} {c c' : Tape} {v : Array E}
    (h : Fl.pointOn name n c = some (v, c')) :
    v.size = n ∧ ∃ nm z w, c = ⟨some nm, z, w, [], v.toList⟩ :: c' := by
  unfold Fl.pointOn at h
  cases hc : closeN name 0 n c with
  | none =>
    rw [hc] at h
    cases h
  | some y =>
    obtain ⟨d, t⟩ := y
    rw [hc] at h
    have e : (d.toArray, t) = (v, c') := Option.some.inj h
    cases e
    obtain ⟨hl, nm, z, w, e1⟩ := closeN_some hc
    exact ⟨by simpa using hl, nm, z, w, e1⟩

theorem round_values (n : Nat) (v : Array E) (r : RoundName) (c c' : Tape) (_ : Clean c)
    (h : Evs [.read n v, .empty r] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = v.toList ∧ drawnOf rv = [] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  have h1' : recvN n c = some (v, c1) := h1
  have h2' : Fl.emptyOn r.name c1 = some ((), c') := h2
  obtain ⟨nm, z, w, e⟩ := emptyOn_some h2'
  exact ⟨⟨some nm, z, w, v.toList, []⟩, ⟨trivial, trivial, (recvN_some h1' e).2⟩, rfl, rfl⟩

theorem round_sum (mu : E) (r : RoundName) (x : E) (c c' : Tape) (_ : Clean c)
    (h : Evs [.sum mu, .ans r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = [mu] ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  have h1' : recv c = some (mu, c1) := h1
  have h2' : closeOne r.name 0 c1 = some (x, c') := h2
  obtain ⟨nm, z, w, e⟩ := closeOne_some h2'
  obtain ⟨nm', z', w', s, d, t, e1, e2⟩ := recv_some h1'
  rw [e2] at e
  cases e
  exact ⟨⟨_, _, _, [mu], [x]⟩, ⟨trivial, trivial, e1⟩, rfl, rfl⟩

theorem round_ans (r : RoundName) (x : E) (c c' : Tape) (_ : Clean c) (h : Evs [.ans r x] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = [] ∧ drawnOf rv = [x] := by
  obtain ⟨c1, h1, rfl⟩ := h
  have h1' : closeOne r.name 0 c = some (x, c') := h1
  obtain ⟨nm, z, w, e⟩ := closeOne_some h1'
  exact ⟨⟨some nm, z, w, [], [x]⟩, ⟨trivial, trivial, e⟩, rfl, rfl⟩

theorem round_point (r : RoundName) (n : Nat) (v : Array E) (c c' : Tape) (_ : Clean c)
    (h : Evs [.point r n v] c c') :
    ∃ rv, Round c rv c' ∧ sentOf rv = [] ∧ drawnOf rv = v.toList ∧ v.size = n := by
  obtain ⟨c1, h1, rfl⟩ := h
  have h1' : Fl.pointOn r.name n c = some (v, c') := h1
  obtain ⟨hs, nm, z, w, e⟩ := pointOn_some h1'
  exact ⟨⟨some nm, z, w, [], v.toList⟩, ⟨trivial, trivial, e⟩, rfl, rfl, hs⟩

end Fo.Tp
