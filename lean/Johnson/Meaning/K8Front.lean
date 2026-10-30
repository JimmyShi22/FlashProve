--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Meaning/K8Front.lean: of the list "K8.equations"
(Johnson/Desc/First/TailClaims/Equations.lean): the first four claims stand under their own numbers;
every claim behind them has a first exponent. Proved of the list's own text.

Why. A law of a segment's batching asks that the exponents of the segment's equations differ. For
that the runs of claims are sorted: a plain claim stands under the power of its own number in the
segment's list (Claim.eqFirst = none); a tail claim under powers from the plan's number of claims on
(eqFirst = some ..). This run is plain in front and tail behind. EquationsForms.lean (K08Claims) has
of the first four claims their number and place alone.

  Lays Q x          where the routine x returns, the list of claims has only grown at its end, by
                    claims that all meet Q. With its laws for pure, bind, if, loops and the plain
                    steps (after Tame, EquationsTame.lean).
  LaysN Q k x       the like, and the claims laid are k in number. LaysN.of_none: a routine that
                    lays only claims that meet False lays none.
  plain_keys · plain_counts   eqKeys lays ONE claim and eqCounts THREE, each with eqFirst = none:
                    COUNTED AT THE PLACES WHERE THE TEXT LAYS A CLAIM (EqM.emit), not taken from
                    the text's own test "internal-f-exist" that four claims were laid.
  own_tail          eqTail lays claims with eqFirst = some .. alone.
  K08Front (a closed Prop) · k08_front   where equations front tl funs F returns the list cls:
                    cls = four ++ rest, four has 4 claims, each with eqFirst = none; each claim of
                    rest has eqFirst = some ...

What is not claimed.
 - NO MEMBER: that equations returns at any record is shown by no theorem here or on the trunk. (By
   a run, no Lean: another house's ride of a description said yes at a stored honest proof, and its
   print lists a run of this name among the runs called at every segment.)
 - rest may be empty (no matrix).
 - Which first exponents the claims of rest have: "some" alone: two may be equal as far as this file
   goes. How many they are, and that the single equations behind them have exponents that differ:
   K08Claims, under its premises.
 - THE NAME: that a run which a description names "K8.equations" is this function is said by no
   landed file: outside this folder the name meets the function in comments alone.
 - THE FORM OF A LAW: a law of the batching speaks of the exponents and the count that a meaning
   laid beside the text gives a run. The bridge from Claim.eqFirst on this list to these is owed by
   whoever lays that meaning.
 - Nothing where the routine refuses. Nothing on the numbers of a plan. Nothing on soundness.
-/
import Johnson.Desc.First.TailClaims.EquationsTame

set_option autoImplicit false

namespace Meaning.K8

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims VerifiableInference.Desc.First.TailClaims.Law

/-- Where x returns, the list has only grown at its end, by claims that all meet Q. -/
def Lays (Q : Claim → Prop) {α : Type} (x : EqM α) : Prop :=
  ∀ (front : ℕ) (s s' : St) (a : α), x front s = .ok (a, s') →
    ∃ new : List Claim, s'.2 = s.2 ++ new.toArray ∧ ∀ c ∈ new, Q c

variable {Q : Claim → Prop}

theorem lays_same (s : St) : ∃ new : List Claim, s.2 = s.2 ++ new.toArray ∧ ∀ c ∈ new, Q c :=
  ⟨[], by simp, fun _ h => nomatch h⟩

theorem Lays.pure {α : Type} (a : α) : Lays Q (Pure.pure a : EqM α) := by
  intro front s s' x h
  rw [((eq_pure_ok _ _ _ _ _).1 h).2]
  exact lays_same s

theorem Lays.bind {α β : Type} {x : EqM α} {f : α → EqM β} (hx : Lays Q x)
    (hf : ∀ a, Lays Q (f a)) : Lays Q (x >>= f) := by
  intro front s s' b h
  obtain ⟨a, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨n1, e1, q1⟩ := hx _ _ _ _ h1
  obtain ⟨n2, e2, q2⟩ := hf a _ _ _ _ h2
  refine ⟨n1 ++ n2, by rw [e2, e1]; simp, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact q1 c hc
  · exact q2 c hc

theorem Lays.ite {α : Type} (c : Prop) [Decidable c] {x x' : EqM α} (h : Lays Q x)
    (h' : Lays Q x') : Lays Q (if c then x else x') := by
  by_cases q : c
  · rw [if_pos q]; exact h
  · rw [if_neg q]; exact h'

theorem Lays.forInList {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Lays Q (f a b)) :
    ∀ (l : List α) (b : β), Lays Q (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Lays.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Lays.bind (h a b) fun r => ?_
    cases r with
    | done b' => exact Lays.pure b'
    | yield b' => exact Lays.forInList h l b'

theorem Lays.forInArray {α β : Type} {f : α → β → EqM (ForInStep β)} (h : ∀ a b, Lays Q (f a b))
    (as : Array α) (b : β) : Lays Q (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact Lays.forInList h _ b

theorem Lays.mustAs (n : String) (b : Bool) : Lays Q (EqM.mustAs n b) := by
  intro front s s' a h
  rw [(eq_must_ok h).2]
  exact lays_same s

theorem Lays.testAs (n : String) (b : Bool) : Lays Q (EqM.testAs n b) := Lays.mustAs n b

theorem Lays.get {α : Type} (n : String) (o : Option α) : Lays Q (EqM.get n o) := by
  intro front s s' a h
  rw [(eq_get_ok h).2]
  exact lays_same s

theorem Lays.ask {α : Type} (n : String) (f : Fork → Option α) : Lays Q (EqM.ask n f) := by
  intro front s s' a h
  rw [(eq_ask_ok h).2]
  exact lays_same s

theorem Lays.claims : Lays Q EqM.claims := by
  intro front s s' a h
  rw [(eq_claims_ok h).2]
  exact lays_same s

theorem Lays.emit {c : Claim} (hc : Q c) : Lays Q (EqM.emit c) := by
  intro front s s' a h
  rw [emit_ok h]
  exact ⟨[c], push_one _ _, fun x hx => by rw [List.mem_singleton.1 hx]; exact hc⟩

/-- A routine on the state alone lays nothing. -/
theorem Lays.liftF {α : Type} (x : ForkM α) : Lays Q (EqM.liftF x) := by
  intro front s s' a h
  obtain ⟨F', _, rfl⟩ := (eq_liftF_ok _ _ _ _ _).1 h
  exact ⟨[], by simp, fun _ h => nomatch h⟩

theorem Lays.paid (i : ℕ) : Lays Q (EqM.paid i) := Lays.liftF _

theorem Lays.change (n : String) (f : Fork → Option Fork) : Lays Q (EqM.change n f) := Lays.liftF _

theorem lays_pscRow (p : Psc) (S0 : E) (kept : Aff) : Lays Q (eqPscRow p S0 kept) := by
  unfold eqPscRow
  exact Lays.bind (Lays.mustAs _ _) fun _ => Lays.bind (Lays.change _ _) fun _ => Lays.pure _

/-- Where x returns, the list has grown at its end by k claims, which all meet Q. -/
def LaysN (Q : Claim → Prop) (k : ℕ) {α : Type} (x : EqM α) : Prop :=
  ∀ (front : ℕ) (s s' : St) (a : α), x front s = .ok (a, s') →
    ∃ new : List Claim, s'.2 = s.2 ++ new.toArray ∧ new.length = k ∧ ∀ c ∈ new, Q c

/-- A routine that lays only claims that meet False lays none. -/
theorem LaysN.of_none {α : Type} {x : EqM α} (h : Lays (fun _ => False) x) : LaysN Q 0 x := by
  intro front s s' a e
  obtain ⟨new, e1, q⟩ := h _ _ _ _ e
  cases new with
  | nil => exact ⟨[], e1, rfl, fun _ h => nomatch h⟩
  | cons c l => exact (q c List.mem_cons_self).elim

theorem LaysN.bind {α β : Type} {x : EqM α} {f : α → EqM β} {j k : ℕ} (hx : LaysN Q j x)
    (hf : ∀ a, LaysN Q k (f a)) : LaysN Q (j + k) (x >>= f) := by
  intro front s s' b h
  obtain ⟨a, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨n1, e1, l1, q1⟩ := hx _ _ _ _ h1
  obtain ⟨n2, e2, l2, q2⟩ := hf a _ _ _ _ h2
  refine ⟨n1 ++ n2, by rw [e2, e1]; simp, by rw [List.length_append, l1, l2], fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact q1 c hc
  · exact q2 c hc

theorem LaysN.emit {c : Claim} (hc : Q c) : LaysN Q 1 (EqM.emit c) := by
  intro front s s' a h
  rw [emit_ok h]
  exact ⟨[c], push_one _ _, rfl, fun x hx => by rw [List.mem_singleton.1 hx]; exact hc⟩

theorem LaysN.lays {α : Type} {x : EqM α} {k : ℕ} (h : LaysN Q k x) : Lays Q x := by
  intro front s s' a e
  obtain ⟨new, e1, -, q⟩ := h _ _ _ _ e
  exact ⟨new, e1, q⟩

/-- Closes "this routine, in which no claim is laid, lays none". -/
macro "lays_none" : tactic => `(tactic| focus (
  refine LaysN.of_none ?_
  repeat (first
    | exact Lays.pure _
    | exact Lays.claims
    | exact Lays.mustAs _ _
    | exact Lays.testAs _ _
    | exact Lays.get _ _
    | exact Lays.ask _ _
    | exact Lays.paid _
    | exact Lays.change _ _
    | exact lays_pscRow _ _ _
    | apply Lays.forInList
    | apply Lays.forInArray
    | apply Lays.ite
    | apply Lays.bind
    | (show ∀ _ _, Lays _ _; intro _ _)
    | (show ∀ _, Lays _ _; intro _)
    | (dsimp only)
    | split)
  done))

/-- A claim under its own number. -/
def Plain (c : Claim) : Prop := c.eqFirst = none

/-- A claim with a first exponent of its own. -/
def Own (c : Claim) : Prop := c.eqFirst.isSome = true

/-- eqKeys lays one claim, under its own number. -/
theorem plain_keys (tl : HTailF2) : LaysN Plain 1 (eqKeys tl) := by
  have h : ∃ k, LaysN Plain k (eqKeys tl) ∧ k = 1 := by
    apply Exists.intro
    apply And.intro
    · unfold eqKeys eqPaddingLaid eqJoinAdded
      repeat (first
        | exact LaysN.emit rfl
        | apply LaysN.bind
        | lays_none
        | (dsimp only)
        | intro _)
    · rfl
  obtain ⟨k, hk, rfl⟩ := h
  exact hk

/-- eqCounts lays three claims, each under its own number. -/
theorem plain_counts (tl : HTailF2) : LaysN Plain 3 (eqCounts tl) := by
  have h : ∃ k, LaysN Plain k (eqCounts tl) ∧ k = 3 := by
    apply Exists.intro
    apply And.intro
    · unfold eqCounts eqPlanesAdded
      repeat (first
        | exact LaysN.emit rfl
        | apply LaysN.bind
        | lays_none
        | (dsimp only)
        | intro _)
    · rfl
  obtain ⟨k, hk, rfl⟩ := h
  exact hk

theorem own_tie (tl : HTailF2) (mu : ℕ) : Lays Own (eqTie tl mu) := by
  unfold eqTie
  repeat (first
    | exact Lays.pure _
    | exact Lays.get _ _
    | exact Lays.emit rfl
    | apply Lays.bind
    | (show ∀ _, Lays _ _; intro _)
    | (dsimp only))

theorem own_read (tl : HTailF2) (Fn : HFun) (sg laid : ℕ) (sums : E) :
    Lays Own (eqRead tl Fn sg laid sums) := by
  unfold eqRead
  repeat (first
    | exact Lays.pure _
    | exact Lays.get _ _
    | exact Lays.ask _ _
    | exact Lays.mustAs _ _
    | exact Lays.testAs _ _
    | exact Lays.emit rfl
    | apply Lays.bind
    | (show ∀ _, Lays _ _; intro _)
    | (dsimp only)
    | split)

theorem own_weights (tl : HTailF2) : Lays Own (eqWeights tl) := by
  unfold eqWeights
  exact Lays.bind (Lays.ask _ _) fun _ => Lays.get _ _

theorem own_tail (before : ℕ) (tl : HTailF2) (funs : Array HFun) :
    Lays Own (eqTail before tl funs) := by
  unfold eqTail
  repeat (first
    | exact Lays.pure _
    | exact Lays.claims
    | exact Lays.mustAs _ _
    | exact Lays.get _ _
    | exact Lays.ask _ _
    | exact own_weights _
    | exact own_tie _ _
    | exact own_read _ _ _ _ _
    | apply Lays.forInList
    | apply Lays.forInArray
    | apply Lays.ite
    | apply Lays.bind
    | (show ∀ _ _, Lays _ _; intro _ _)
    | (show ∀ _, Lays _ _; intro _)
    | (dsimp only)
    | split)

/-- **"K8.equations" is plain in front and tail behind: four claims under their own numbers, then
claims with a first exponent.** -/
def K08Front : Prop :=
  ∀ (front : ℕ) (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork) (cls : List Claim),
    equations front tl funs F = .ok (tl', F1, cls) →
    ∃ four rest : List Claim, cls = four ++ rest ∧ four.length = 4 ∧
      (∀ c ∈ four, c.eqFirst = none) ∧ ∀ c ∈ rest, c.eqFirst.isSome = true

theorem k08_front : K08Front := by
  intro front tl tl' funs F F1 cls h
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    obtain ⟨tlx, Fx, arr⟩ := x
    have hcl : arr.toList = cls := congrArg (fun y => y.2.2) (Except.ok.inj h)
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    rw [(eq_must_ok h2).2] at k2
    obtain ⟨z, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
    rw [(eq_ask_ok h3).2] at k3
    obtain ⟨u4, t4, h4, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
    rw [(eq_test_ok h4).2] at k4
    obtain ⟨g', t5, h5, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
    rw [(eq_get_ok h5).2] at k5
    obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
    rw [(eq_must_ok h6).2] at k6
    unfold eqRest at k6
    obtain ⟨before, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
    obtain ⟨eb, rfl⟩ := eq_claims_ok h7
    obtain ⟨tla, s1, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
    obtain ⟨tlb, s2, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
    obtain ⟨n1, e1, l1, q1⟩ := plain_keys tl _ _ _ _ h8
    obtain ⟨n2, e2, l2, q2⟩ := plain_counts tla _ _ _ _ h9
    obtain ⟨n3, e3, q3⟩ := own_tail before tlb funs _ _ _ _ k9
    refine ⟨n1 ++ n2, n3, ?_, ?_, fun c hc => ?_, q3⟩
    · rw [← hcl]
      show arr.toList = _
      have : arr = (#[] ++ n1.toArray ++ n2.toArray) ++ n3.toArray := by
        have e3' : arr = s2.2 ++ n3.toArray := e3
        rw [e3', e2, e1]
      rw [this]
      simp
    · rw [List.length_append, l1, l2]
    · rcases List.mem_append.1 hc with hc | hc
      · exact q1 c hc
      · exact q2 c hc

end Meaning.K8

#print axioms Meaning.K8.k08_front
