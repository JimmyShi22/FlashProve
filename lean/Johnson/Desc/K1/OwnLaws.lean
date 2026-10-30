-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/OwnLaws.lean: what a yes of the decision of a sending (kind K1) says, as equations
on the carried record: what the decision has asked and what it has written.

Main names:
  need_ok, named_ok, bind_ok: on the two helpers of the decisions' texts and on Except's bind.
  rowsOf, seedsOf, answersIn: the sample rows of one message; the seeds that a round's draw gives;
    the answers that a round holds.
  Laid, layRows_ok: a yes of layRows, message by message: a sampled one has its seeds and answers,
    its sample rows are those of sampleRow at these, the statement's page has admitted them; no
    answer is left.
  decideSend_ok: a yes of decideSend: nothing was owed; the record's codes are the plan's; no factor
    is spelt by three words 0; the statement's page has received the plan's messages and returned
    their numbers; and Laid holds from the record behind the receiving to the record returned.
Plain records and pure functions of the verifier program are named, as the head of Own.lean lists
them; none that takes a context or runs.

What is not claimed. One direction alone: what a yes says. Nothing on what a row means, on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

theorem need_ok (n : String) (b : Bool) (u : Unit) : need n b = .ok u ↔ b = true := by
  unfold need; cases b <;> simp

theorem named_ok {α : Type} (n : String) (o : Option α) (a : α) :
    named n o = .ok a ↔ o = some a := by
  cases o <;> simp [named]

theorem bind_ok {α β : Type} (x : Except String α) (f : α → Except String β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- The sample rows of one message: at the first seeds and the next answers. -/
def rowsOf (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape) (ys : List E) :
    Array OnBytes.Row :=
  (((seeds.take s.answers).zip (ys.take s.answers)).zipIdx.map fun x =>
    sampleRow (Msg.of codes s) o x.1.1.1 x.1.1.2 x.2 x.1.2).toArray

/-- What a yes of layRows says, as a relation. -/
inductive Laid {L : Type} (codes : Codes) (seeds : List (List E × E)) :
    List (Nat × OracleShape) → List E → DState L → DState L → Prop
  | done (d : DState L) : Laid codes seeds [] [] d d
  | pass (o : Nat) (s : OracleShape) (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L)
      (h0 : s.answers = 0) (h : Laid codes seeds l ys d d') : Laid codes seeds ((o, s) :: l) ys d d'
  | lay (o : Nat) (s : OracleShape) (l : List (Nat × OracleShape)) (ys : List E)
      (d d₁ d' : DState L)
      (h0 : s.answers ≠ 0) (hs : s.answers ≤ seeds.length) (hy : s.answers ≤ ys.length)
      (ha : Ground.admitP d o (rowsOf codes seeds o s ys) = some d₁)
      (h : Laid codes seeds l (ys.drop s.answers) d₁ d') : Laid codes seeds ((o, s) :: l) ys d d'

theorem layRows_ok {L : Type} (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L),
      layRows codes seeds l ys d = .ok d' → Laid codes seeds l ys d d'
  | [], ys, d, d', h => by
    unfold layRows at h
    cases ys with
    | nil => simp at h; subst h; exact .done d
    | cons y t => simp at h
  | (o, s) :: l, ys, d, d', h => by
    unfold layRows at h
    by_cases h0 : s.answers = 0
    · simp [h0] at h
      exact .pass o s l ys d d' h0 (layRows_ok codes seeds l ys d d' h)
    · by_cases hs : seeds.length < s.answers
      · simp [h0, hs] at h
      · by_cases hy : ys.length < s.answers
        · simp [h0, hs, hy] at h
        · simp only [beq_iff_eq, h0, hs, hy, decide_false, if_false, Bool.false_eq_true] at h
          obtain ⟨d₁, h1, h2⟩ := (bind_ok _ _ _).1 h
          exact .lay o s l ys d d₁ d' h0 (Nat.le_of_not_lt hs) (Nat.le_of_not_lt hy)
            ((named_ok _ _ _).1 h1) (layRows_ok codes seeds l _ d₁ d' h2)

/-- The seeds that a round's draw gives. -/
def seedsOf (P : Par) (r₁ : Fmt.RoundView) : List (List E × E) :=
  cutSeeds P.coordinates P.seeds (r₁.drawn.elems.map E.ofTriple)

/-- The answers that a round holds. -/
def answersIn (r₂ : Fmt.RoundView) : List E :=
  r₂.vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none

/-- **What a yes of the sending's decision says.** -/
theorem decideSend_ok {L : Type} (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    owed = none ∧ d.st.codes = P.codes ∧ (∀ s ∈ seedsOf P r₁, isZeroE s.2 = false) ∧
      ∃ d₁, Ground.recvP P.gp.firstTree d P.sent = some (ids, d₁) ∧
        Laid P.codes (seedsOf P r₁) (ids.toList.zip (P.sent.toList.map (·.shape))) (answersIn r₂)
          d₁ d' := by
  unfold decideSend at h
  obtain ⟨_, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, h4, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨x, h5, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨e, h8, h⟩ := (bind_ok _ _ _).1 h
  have h1 := (need_ok _ _ _).1 h1
  have h2 := (need_ok _ _ _).1 h2
  have h4 := (need_ok _ _ _).1 h4
  have h5 := (named_ok _ _ _).1 h5
  have hp : (x.1, e) = (ids, d') := by simpa [pure, Except.pure] using h
  obtain ⟨hx, he⟩ := Prod.mk.inj hp
  subst he
  refine ⟨by simpa using h1, by simpa using h2, ?_, x.2, ?_, ?_⟩
  · intro s hs
    have := (List.all_eq_true.1 h4) s hs
    simpa using this
  · rw [h5, ← hx]
  · rw [← hx]; exact layRows_ok _ _ _ _ _ _ h8

end VerifiableInference.Desc.K1
