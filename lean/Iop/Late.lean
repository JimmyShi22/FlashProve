-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Late.lean: round-by-round soundness for an instance that is fixed late: "the prover has lost,
jointly for a family of statements, up to round n". Definitions and their first laws.

The library states round-by-round soundness by the predicate `Doomed s ε bad` (Iop/Rbr.lean), "the
prover has lost": s is the list of the protocol's rounds, ε has for each round a count of values of
the verifier message, and bad is a property of full transcripts.

Why: the programs write the answer y of a request into its hash chain only at the start of the last
of 25 sub-proofs; the first hash call holds the statement with 0 in the place of y. So a cheating
prover may choose y after it has seen the verifier messages of all earlier rounds. Round-by-round
soundness for each y by itself does not cover that: a union bound over all y would. What does cover
it, at no cost: in the rounds before y is fixed, one set of bad verifier messages serves all y.

Main names:
  `JDoomed n s ε bad`: for a family of goals bad φ (φ: the statements among which the prover may
    still choose): in each of the first n rounds, for every prover message, at most ε_i verifier
    messages leave the prover not lost in this joint sense; after n rounds it has lost for each φ by
    itself (`Doomed`). n at least the number of rounds: the prover has lost towards
    "bad φ for all φ".
  `JDoomed.exists_badFam`: `JDoomed n` gives, for each φ, bad sets (`BadFam`, Iop/Rbr.lean) within
    the errors that agree in the first n rounds.
  `LateSound`: the form in which a protocol proves `JDoomed n`.
  `Reduction.JSound`: the same for reductions, with the two rules of composition (a first reduction
    that does not see φ; a last one after φ is fixed).
  `BatchInteractiveOracleProof.sndBL_iff_sndB`: at early = id and late = none, `SndBL` is `SndB`.

Limits: this file says nothing on any protocol. It does not say that `JDoomed` holds for the model's
chain. It does not say that it is what layer 1 needs: Compile/Batch/Sound.lean takes (Snd-B) in the
late form (`SndBL`, Iop/Batch.lean) as a hypothesis.
Not in a write-up of ours that is not in this repository (lean/CREDITS.md), where the whole instance
stands in the first query (Construction B.5, (F1)).

Terms: lean/GLOSSARY.md: the prover has lost, bad sets, error, shape, programs, layer, (Snd-B),
local round, slot.
-/
import Iop.Batch
import Iop.Compose

namespace Iop
open Prob

/-! ## 1. Lost jointly up to round n -/

section J
variable {Φ : Type}

/-- The prover has lost, jointly for all φ in the first n rounds, and then for each φ by itself. -/
def JDoomed : ℕ → (s : Shape) → Err s → (Φ → Tr s → Prop) → Prop
  | 0, s, ε, bad => ∀ φ, Doomed s ε (bad φ)
  | _ + 1, [], _, bad => ∀ φ, bad φ ()
  | n + 1, r :: s, (e, ε), bad =>
    ∀ m : r.Msg, cnt (fun c : r.Chal => ¬ JDoomed n s ε (fun φ τ => bad φ (m, c, τ))) ≤ e

theorem JDoomed.mono :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) {bad bad' : Φ → Tr s → Prop},
      (∀ φ τ, bad φ τ → bad' φ τ) → JDoomed n s ε bad → JDoomed n s ε bad'
  | 0, s, ε, _, _, h, hd => fun φ => Doomed.mono s ε (h φ) (hd φ)
  | _ + 1, [], _, _, _, h, hd => fun φ => h φ () (hd φ)
  | n + 1, _ :: s, (_, ε), _, _, h, hd => fun m =>
      le_trans (cnt_mono fun c hc hd' =>
        hc (JDoomed.mono n s ε (fun φ τ => h φ (m, c, τ)) hd')) (hd m)

theorem JDoomed.of_forall :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) {bad : Φ → Tr s → Prop}, (∀ φ τ, bad φ τ) → JDoomed n s ε bad
  | 0, s, ε, _, h => fun φ => Doomed.of_forall s ε (h φ)
  | _ + 1, [], _, _, h => fun φ => h φ ()
  | n + 1, _ :: s, (_, ε), _, h => fun m => by
      rw [cnt_false (fun c hc => hc (JDoomed.of_forall n s ε (fun φ τ => h φ (m, c, τ))))]
      exact Nat.zero_le _

/-- Lost jointly is lost for each φ. -/
theorem JDoomed.each :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) {bad : Φ → Tr s → Prop},
      JDoomed n s ε bad → ∀ φ, Doomed s ε (bad φ)
  | 0, _, _, _, h, φ => h φ
  | _ + 1, [], _, _, h, φ => h φ
  | n + 1, _ :: s, (_, ε), bad, h, φ => fun m =>
      le_trans (cnt_mono fun c hc hj =>
        hc (JDoomed.each n s ε (bad := fun φ τ => bad φ (m, c, τ)) hj φ)) (h m)

/-- Jointly up to a later round is stronger. -/
theorem JDoomed.anti :
    ∀ (n n' : ℕ) (s : Shape) (ε : Err s) {bad : Φ → Tr s → Prop},
      n ≤ n' → JDoomed n' s ε bad → JDoomed n s ε bad
  | 0, n', s, ε, _, _, h => JDoomed.each n' s ε h
  | _ + 1, 0, _, _, _, hn, _ => absurd hn (by simp)
  | _ + 1, _ + 1, [], _, _, _, h => h
  | n + 1, n' + 1, _ :: s, (_, ε), bad, hn, h => fun m =>
      le_trans (cnt_mono fun c hc hd =>
        hc (JDoomed.anti n n' s ε (bad := fun φ τ => bad φ (m, c, τ))
            (Nat.le_of_succ_le_succ hn) hd)) (h m)

/-- Lost towards "bad φ for all φ" is lost jointly up to any round. -/
theorem JDoomed.of_all :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) {bad : Φ → Tr s → Prop},
      Doomed s ε (fun τ => ∀ φ, bad φ τ) → JDoomed n s ε bad
  | 0, s, ε, _, h => fun φ => Doomed.mono s ε (fun _ hτ => hτ φ) h
  | _ + 1, [], _, _, h => h
  | n + 1, _ :: s, (_, ε), _, h =>
    fun m => le_trans (cnt_mono fun _ hc hd => hc (JDoomed.of_all n s ε hd)) (h m)

/-- A first part in which nothing depends on φ: if the prover has lost in s towards "it has lost in
t, jointly up to round n", then it has lost in s ++ t jointly up to round |s| + n. -/
theorem JDoomed.append_left :
    ∀ (s t : Shape) (ε : Err s) (ε' : Err t) (n k : ℕ) (bad : Φ → Tr (s ++ t) → Prop), k =
        s.length + n →
      Doomed s ε (fun a => JDoomed n t ε' (fun φ b => bad φ (Tr.app a b))) →
      JDoomed k (s ++ t) (Err.app ε ε') bad
  | [], _, _, _, n, k, _, hk, h => by
      obtain rfl : k = n := by simpa using hk
      exact h
  | r :: s, t, (e, ε), ε', n, k, bad, hk, h => by
      obtain rfl : k = (s.length + n) + 1 := by rw [hk, List.length_cons]; omega
      show ∀ m : r.Msg,
        cnt (fun c : r.Chal =>
            ¬ JDoomed (s.length + n) (s ++ t) (Err.app ε ε') (fun φ τ => bad φ (m, c, τ))) ≤ e
      exact fun m =>
        le_trans (cnt_mono fun c hc hd' =>
            hc (JDoomed.append_left s t ε ε' n _ (fun φ τ => bad φ (m, c, τ)) rfl hd')) (h m)

/-- A last part after φ is fixed. -/
theorem JDoomed.append_right :
    ∀ (n : ℕ) (s t : Shape) (ε : Err s) (ε' : Err t) (bad : Φ → Tr (s ++ t) → Prop), n ≤ s.length →
      JDoomed n s ε (fun φ a => Doomed t ε' (fun b => bad φ (Tr.app a b))) →
      JDoomed n (s ++ t) (Err.app ε ε') bad
  | 0, s, t, ε, ε', bad, _, h => fun φ => Doomed.append s t ε ε' (bad φ) (h φ)
  | _ + 1, [], _, _, _, _, hn, _ => absurd hn (by simp)
  | n + 1, r :: s, t, (e, ε), ε', bad, hn, h => by
      show ∀ m : r.Msg,
        cnt (fun c : r.Chal => ¬ JDoomed n (s ++ t) (Err.app ε ε') (fun φ τ => bad φ (m, c, τ))) ≤ e
      exact fun m =>
        le_trans (cnt_mono fun c hc hd' =>
            hc (JDoomed.append_right n s t ε ε' (fun φ τ => bad φ (m, c, τ))
                (Nat.le_of_succ_le_succ hn) hd')) (h m)

/-- Larger errors are weaker. -/
theorem JDoomed.mono_err :
    ∀ (n : ℕ) (s : Shape) {ε ε' : Err s} {bad : Φ → Tr s → Prop},
      Err.le ε ε' → JDoomed n s ε bad → JDoomed n s ε' bad
  | 0, s, _, _, _, h, hd => fun φ => Doomed.mono_err s h (hd φ)
  | _ + 1, [], _, _, _, _, hd => hd
  | n + 1, _ :: s, (_, _), (_, _), _, h, hd => fun m =>
      le_trans (le_trans (cnt_mono (fun _ hc hd' => hc (JDoomed.mono_err n s h.2 hd'))) (hd m)) h.1

/-- A family may be re-indexed. -/
theorem JDoomed.comap {Ψ : Type} (f : Ψ → Φ) :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) {bad : Φ → Tr s → Prop},
      JDoomed n s ε bad → JDoomed n s ε (fun ψ => bad (f ψ))
  | 0, _, _, _, h => fun ψ => h (f ψ)
  | _ + 1, [], _, _, h => fun ψ => h (f ψ)
  | n + 1, _ :: s, (_, ε), bad, h => fun m =>
      le_trans (cnt_mono fun c hc hd =>
        hc (JDoomed.comap f n s ε (bad := fun φ τ => bad φ (m, c, τ)) hd)) (h m)

end J

/-! ## 2. Families of bad sets that agree in the first n rounds -/

/-- The two families have the same bad sets in the first n rounds. -/
def BadFam.AgreeTo : ℕ → {s : Shape} → BadFam s → BadFam s → Prop
  | 0, _, _, _ => True
  | _ + 1, [], _, _ => True
  | n + 1, _ :: _, (B, k), (B', k') => (∀ m, B m = B' m) ∧ ∀ m c, BadFam.AgreeTo n (k m c) (k' m c)

theorem BadFam.AgreeTo.refl : ∀ (n : ℕ) {s : Shape} (B : BadFam s), BadFam.AgreeTo n B B
  | 0, _, _ => trivial
  | _ + 1, [], _ => trivial
  | n + 1, _ :: _, (_, k) => ⟨fun _ => rfl, fun m c => BadFam.AgreeTo.refl n (k m c)⟩

theorem BadFam.AgreeTo.symm :
    ∀ {n : ℕ} {s : Shape} {B B' : BadFam s}, BadFam.AgreeTo n B B' → BadFam.AgreeTo n B' B
  | 0, _, _, _, _ => trivial
  | _ + 1, [], _, _, _ => trivial
  | _ + 1, _ :: _, (_, _), (_, _), h => ⟨fun m => (h.1 m).symm, fun m c => (h.2 m c).symm⟩

theorem BadFam.AgreeTo.trans :
    ∀ {n : ℕ} {s : Shape} {B B' B'' : BadFam s},
      BadFam.AgreeTo n B B' → BadFam.AgreeTo n B' B'' → BadFam.AgreeTo n B B''
  | 0, _, _, _, _, _, _ => trivial
  | _ + 1, [], _, _, _, _, _ => trivial
  | _ + 1, _ :: _, (_, _), (_, _), (_, _), h, h' =>
    ⟨fun m => (h.1 m).trans (h'.1 m), fun m c => (h.2 m c).trans (h'.2 m c)⟩

/-- Families on s ++ t agree in the first n ≤ |s| rounds if their parts on s do. -/
theorem BadFam.AgreeTo.app :
    ∀ {n : ℕ} {s t : Shape} {B B' : BadFam s} (g g' : Tr s → BadFam t),
      n ≤ s.length → BadFam.AgreeTo n B B' → BadFam.AgreeTo n (BadFam.app B g) (BadFam.app B' g')
  | 0, _, _, _, _, _, _, _, _ => trivial
  | _ + 1, [], _, _, _, _, _, hn, _ => absurd hn (by simp)
  | _ + 1, _ :: _, _, (_, _), (_, _), g, g', hn, h =>
      ⟨h.1, fun m c =>
          BadFam.AgreeTo.app (fun a => g (m, c, a)) (fun a => g' (m, c, a))
            (Nat.le_of_succ_le_succ hn) (h.2 m c)⟩

/-- Lost jointly up to round n, by way of bad sets. If `JDoomed n s ε bad` holds, there are for each
φ a family of bad sets within the errors such that every clean transcript is bad for the prover, and
one more family B₀ within the errors, with which all of them agree in the first n rounds. (B₀ is
there so that something can be said where there is no φ.) -/
theorem JDoomed.exists_badFam {Φ : Type} :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) (bad : Φ → Tr s → Prop), JDoomed n s ε bad →
      ∃ (B₀ : BadFam s) (B : Φ → BadFam s),
        B₀.Within ε ∧
        ∀ φ, (B φ).Within ε ∧ (∀ τ, (B φ).Clean τ → bad φ τ) ∧ BadFam.AgreeTo n B₀ (B φ)
  | 0, s, ε, bad, h => by
      choose B hW hC using fun φ => Doomed.exists_badFam s ε (bad φ) (h φ)
      exact ⟨BadFam.empty s, B, BadFam.empty_within s ε, fun φ => ⟨hW φ, hC φ, trivial⟩⟩
  | _ + 1, [], _, _, h => ⟨(), fun _ => (), trivial, fun φ => ⟨trivial, fun _ _ => h φ, trivial⟩⟩
  | n + 1, r :: s, (e, ε), bad, h => by
      have ih : ∀ (m : r.Msg) (c : r.Chal), ∃ (B₀ : BadFam s) (B : Φ → BadFam s),
          B₀.Within ε ∧
          ∀ φ,
            (B φ).Within ε ∧
            (JDoomed n s ε (fun φ τ => bad φ (m, c, τ)) → ∀ τ, (B φ).Clean τ → bad φ (m, c, τ)) ∧
            BadFam.AgreeTo n B₀ (B φ) := fun m c => by
        by_cases hd : JDoomed n s ε (fun φ τ => bad φ (m, c, τ))
        · obtain ⟨B₀, B, h0, hB⟩ := JDoomed.exists_badFam n s ε _ hd
          exact ⟨B₀, B, h0, fun φ => ⟨(hB φ).1, fun _ => (hB φ).2.1, (hB φ).2.2⟩⟩
        · exact ⟨BadFam.empty s, fun _ => BadFam.empty s, BadFam.empty_within s ε,
            fun _ => ⟨BadFam.empty_within s ε, fun h' => absurd h' hd, BadFam.AgreeTo.refl n _⟩⟩
      choose k₀ k h0 hk using ih
      refine ⟨(fun m => {c | ¬ JDoomed n s ε (fun φ τ => bad φ (m, c, τ))}, k₀),
        fun φ => (fun m => {c | ¬ JDoomed n s ε (fun φ τ => bad φ (m, c, τ))}, fun m c => k m c φ),
        ⟨fun m => h m, h0⟩,
        fun φ =>
          ⟨⟨fun m => h m, fun m c => (hk m c φ).1⟩, ?_, ⟨fun _ => rfl, fun m c => (hk m c φ).2.2⟩⟩⟩
      rintro ⟨m, c, τ⟩ ⟨hc, hτ⟩
      exact (hk m c φ).2.1 (not_not.mp hc) τ hτ

/-- The converse of `JDoomed.exists_badFam`: under the hypotheses below, bad sets that agree in the
first n rounds give "lost jointly up to round n". -/
theorem jDoomed_of_clean {Φ : Type} :
    ∀ (n : ℕ) (s : Shape) (ε : Err s) (B₀ : BadFam s) (B : Φ → BadFam s) (bad : Φ → Tr s → Prop),
      B₀.Within ε →
      (∀ φ, (B φ).Within ε ∧ (∀ τ, (B φ).Clean τ → bad φ τ) ∧ BadFam.AgreeTo n B₀ (B φ)) →
      JDoomed n s ε bad
  | 0, s, ε, _, B, bad, _, h => fun φ => doomed_of_clean s ε (B φ) (bad φ) (h φ).1 (h φ).2.1
  | _ + 1, [], _, _, _, _, _, h => fun φ => (h φ).2.1 () trivial
  | n + 1, _ :: s, (_, ε), (B₀, k₀), B, bad, h0, h => fun m =>
      le_trans (cnt_mono (fun c hc => by
        by_contra hcB
        refine hc (jDoomed_of_clean n s ε (k₀ m c) (fun φ => (B φ).2 m c) _ (h0.2 m c)
            fun φ => ⟨(h φ).1.2 m c, fun τ hτ => (h φ).2.1 (m, c, τ) ⟨?_, hτ⟩, (h φ).2.2.2 m c⟩)
        rw [← (h φ).2.2.1 m]
        exact hcB)) (h0.1 m)

/-- Two goals at once; the errors add (as `Doomed.and`, Iop/Compose.lean). -/
theorem JDoomed.and {Φ : Type} :
    ∀ (n : ℕ) (s : Shape) {ε ε' : Err s} {bad bad' : Φ → Tr s → Prop}, JDoomed n s ε bad →
      JDoomed n s ε' bad' → JDoomed n s (Err.add ε ε') (fun φ τ => bad φ τ ∧ bad' φ τ)
  | 0, s, _, _, _, _, h, h' => fun φ => Doomed.and s (h φ) (h' φ)
  | _ + 1, [], _, _, _, _, h, h' => fun φ => ⟨h φ, h' φ⟩
  | n + 1, _ :: s, (_, _), (_, _), _, _, h, h' => fun m =>
      le_trans
        (cnt_le_add (fun c hc => by
          by_contra hn
          rw [not_or, not_not, not_not] at hn
          exact hc (JDoomed.and n s hn.1 hn.2)))
        (Nat.add_le_add (h m) (h' m))

/-- Round-by-round soundness for statements that are fixed late, in the form in which a protocol
proves it. X: the statements; early x: what of x is fixed at the start; no x: x is false; lost x τ:
τ is bad for a prover of x. For every value x₀ of the early part the prover has lost, jointly up to
round n for all false x with this early part. -/
def LateSound {X : Type} (s : Shape) (n : ℕ) (early : X → X) (ε : Err s)
    (no : X → Prop) (lost : X → Tr s → Prop) : Prop :=
  ∀ x₀, JDoomed (Φ := {x // early x = x₀ ∧ no x}) n s ε (fun x τ => lost x.1 τ)

/-- `LateSound` implies round-by-round soundness for each statement: for every false x the prover
has lost towards lost x. -/
theorem LateSound.each {X : Type} {s : Shape} {n : ℕ} {early : X → X} {ε : Err s} {no : X → Prop}
    {lost : X → Tr s → Prop} (h : LateSound s n early ε no lost) (x : X) (hx : no x) :
    Doomed s ε (lost x) :=
  JDoomed.each n s ε (h (early x)) ⟨x, rfl, hx⟩

/-- At n = 0 `LateSound` is round-by-round soundness for each statement. -/
theorem lateSound_zero_iff {X : Type} {s : Shape} {early : X → X} {ε : Err s}
    {no : X → Prop} {lost : X → Tr s → Prop} :
    LateSound s 0 early ε no lost ↔ ∀ x, no x → Doomed s ε (lost x) :=
  ⟨fun h x hx => h.each x hx, fun h _ x => h x.1 x.2.2⟩

/-! ## 2a. How many verifier messages a partial transcript holds -/

/-- The number of verifier messages of a partial transcript. -/
def PTr.done {s : Shape} : PTr s → ℕ
  | .atP τ => τ.idx
  | .atV τ => τ.idx
  | .full _ => s.length

theorem PTr.done_empty : ∀ s : Shape, (PTr.empty s).done = 0
  | [] => rfl
  | _ :: _ => rfl

theorem PTr.done_cons {r : Round} {s : Shape} (m : r.Msg) (c : r.Chal) :
    ∀ ν : PTr s, (PTr.cons m c ν).done = ν.done + 1
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem AtV.done_snoc : ∀ {s : Shape} (τ : AtV s) (c : τ.round.Chal), (τ.snoc c).done = τ.idx + 1
  | _ :: s, .inl m, c => by
      show (PTr.cons m c (PTr.empty s)).done = 0 + 1
      rw [PTr.done_cons, PTr.done_empty]
  | _ :: _, .inr (m', c', τ), c => by
      show (PTr.cons m' c' (τ.snoc c)).done = τ.idx + 1 + 1
      rw [PTr.done_cons, AtV.done_snoc τ c]

/-- After a verifier message a partial transcript is not at the verifier. -/
theorem AtV.snoc_ne_atV :
    ∀ {s : Shape} (τ : AtV s) (c : τ.round.Chal) (τ' : AtV s), τ.snoc c ≠ .atV τ'
  | _ :: s, .inl m, c, τ' => by
      show PTr.cons m c (PTr.empty s) ≠ _
      cases s <;> exact fun h => by cases h
  | _ :: _, .inr (m', c', τ), c, τ' => by
      show PTr.cons m' c' (τ.snoc c) ≠ _
      intro h
      cases hν : τ.snoc c with
      | atP _ => rw [hν] at h; cases h
      | atV τ'' => exact AtV.snoc_ne_atV τ c τ'' hν
      | full _ => rw [hν] at h; cases h

/-! ## 2b. Reductions: soundness for a family of statements, jointly up to round n -/

namespace Reduction
variable {A B C Φ : Type}

/-- The prover has lost, jointly up to round n, for the statements ia φ, towards "the verifier
rejects or outputs a statement outside LB". -/
def JSound (K : Reduction A B) (n : ℕ) (ia : Φ → A) (LB : B → Prop) (ε : Err K.shape) : Prop :=
  JDoomed (Φ := Φ) n K.shape ε (fun φ τ => ∀ b, K.out (ia φ) τ = some b → ¬ LB b)

/-- Each statement by itself. -/
theorem JSound.zero {K : Reduction A B} {LA : A → Prop} {LB : B → Prop} {ε : Err K.shape}
    (h : K.Sound LA LB ε) {ia : Φ → A} (hia : ∀ φ, ¬ LA (ia φ)) : K.JSound 0 ia LB ε :=
  fun φ => h (ia φ) (hia φ)

/-- A first reduction that does not see which φ it is. On all statements ia φ it does what it does
on one statement a₀, but for a re-writing re φ of its output. If it is sound at a₀ towards a
language LB, and outside LB the second reduction is sound jointly up to round n for the re-written
statements, then the composition is sound jointly up to round |K₁| + n. -/
theorem JSound.seq_left {K₁ : Reduction A B} {K₂ : Reduction B C} {ia : Φ → A} {a₀ : A}
    {re : Φ → B → B} {LB : B → Prop} {LC : C → Prop} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    {n k : ℕ} (hk : k = K₁.shape.length + n)
    (hblind : ∀ φ τ, K₁.out (ia φ) τ = (K₁.out a₀ τ).map (re φ))
    (h₁ : Doomed K₁.shape ε₁ (fun τ => ∀ b, K₁.out a₀ τ = some b → ¬ LB b))
    (h₂ : ∀ b, ¬ LB b → K₂.JSound n (fun φ => re φ b) LC ε₂) :
    (K₁.seq K₂).JSound k ia LC (Err.app ε₁ ε₂) := by
  refine JDoomed.append_left K₁.shape K₂.shape ε₁ ε₂ n k _ hk (Doomed.mono _ _ ?_ h₁)
  intro τ₁ hτ₁
  cases hout : K₁.out a₀ τ₁ with
  | none =>
      refine JDoomed.of_forall _ _ _ fun φ τ₂ c hc => ?_
      rw [seq_out_app, hblind, hout] at hc
      exact absurd hc (by simp)
  | some b =>
      refine JDoomed.mono _ _ _ ?_ (h₂ b (hτ₁ b hout))
      intro φ τ₂ h c hc
      rw [seq_out_app, hblind, hout] at hc
      exact h c hc

/-- A last reduction, after φ is fixed. -/
theorem JSound.seq_right {K₁ : Reduction A B} {K₂ : Reduction B C} {ia : Φ → A} {LB : B → Prop}
    {LC : C → Prop} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape} {n : ℕ} (hn : n ≤ K₁.shape.length)
    (h₁ : K₁.JSound n ia LB ε₁) (h₂ : K₂.Sound LB LC ε₂) :
    (K₁.seq K₂).JSound n ia LC (Err.app ε₁ ε₂) := by
  refine JDoomed.append_right n K₁.shape K₂.shape ε₁ ε₂ _ hn (JDoomed.mono _ _ _ ?_ h₁)
  intro φ τ₁ hτ₁
  cases hout : K₁.out (ia φ) τ₁ with
  | none =>
      refine Doomed.of_forall _ _ fun τ₂ c hc => ?_
      rw [seq_out_app, hout] at hc
      exact absurd hc (by simp)
  | some b =>
      refine Doomed.mono _ _ ?_ (h₂ b (hτ₁ b hout))
      intro τ₂ h c hc
      rw [seq_out_app, hout] at hc
      exact h c hc

end Reduction

/-! ## 3. The rounds up to n are local -/

theorem RoundSplits.LocalTo.app_allLocal :
    ∀ (n : ℕ) (s t : Shape) (A' : RoundSplits t),
      n < s.length → RoundSplits.LocalTo n (s ++ t) (RoundSplits.app (RoundSplits.allLocal s) A')
  | _, [], _, _, h => absurd h (by simp)
  | 0, _ :: _, _, _, _ => rfl
  | n + 1, _ :: s, t, A', h => ⟨rfl, RoundSplits.LocalTo.app_allLocal n s t A' (Nat.lt_of_succ_lt_succ h)⟩

theorem RoundSplits.LocalTo.lt_length :
    ∀ {n : ℕ} {s : Shape} {A : RoundSplits s}, RoundSplits.LocalTo n s A → n < s.length
  | _, [], _, h => by cases ‹ℕ› <;> exact False.elim h
  | 0, _ :: _, (_, _), _ => Nat.succ_pos _
  | _ + 1, _ :: _, (_, _), h => Nat.succ_lt_succ h.2.lt_length

/-! ## 4. With the whole instance in the first query, the late form of (Snd-B) is (Snd-B) -/

/-- The law on verifier messages is kept if the state of some slots is set to 1 throughout. -/
theorem JointLaw.orFlag {N : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool)) (b : Fin N → Bool),
      JointLaw N s A ε St → JointLaw N s A ε fun j => (St j).map fun S τ => b j || S τ
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), St, b, h => by
      intro (m0 : a.M0) (m : Fin N → a.Mj)
      obtain ⟨h1, h2⟩ := h m0 m
      refine ⟨?_, fun v => ?_⟩
      · cases hk : a.kind with
        | lo =>
          simp only [hk] at h1 ⊢
          intro j S' hS' h0
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          obtain ⟨hb, h0'⟩ := Bool.or_eq_false_iff.1 h0
          refine le_trans (cnt_mono fun c hc => ?_) (h1 j S hS h0')
          simpa [hb] using hc
        | sh =>
          simp only [hk] at h1 ⊢
          refine le_trans (cnt_mono ?_) h1
          rintro c ⟨j, S', hS', h0, hc⟩
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          obtain ⟨hb, h0'⟩ := Bool.or_eq_false_iff.1 h0
          exact ⟨j, S, hS, h0', by simpa [hb] using hc⟩
      · have ih := JointLaw.orFlag s A ε _ b (h2 v)
        refine cast (congrArg (JointLaw N s A ε) ?_) ih
        funext j
        beta_reduce
        cases St j <;> rfl

variable {X : Type} {E : ExtSpec}

theorem BatchInteractiveOracleProof.SndB.toL {Q : BatchInteractiveOracleProof X E} {N : ℕ} {L : X → E.Str → Prop}
    {ε : Err Q.loc.shape} (h : Q.SndB N L ε) : Q.SndBL N id none L ε := by
  obtain ⟨State, h1, h2, h3, h4⟩ := h
  exact ⟨fun n hn => (by cases hn), State,
    fun y x hL => Bool.eq_false_iff.2 fun h => hL ((h1 y x).1 h), h2,
    fun _ _ _ _ hn => (by cases hn), fun y x τ _ h => h3 y x τ h, h4⟩

open Classical in
/-- At early = id and late = none, `SndBL` is `SndB`. -/
theorem BatchInteractiveOracleProof.sndBL_iff_sndB
    {Q : BatchInteractiveOracleProof X E} {N : ℕ} {L : X → E.Str → Prop} {ε : Err Q.loc.shape} :
    Q.SndBL N id none L ε ↔ Q.SndB N L ε := by
  refine ⟨?_, BatchInteractiveOracleProof.SndB.toL⟩
  rintro ⟨-, State, h1, h2, -, h3, h4⟩
  refine ⟨fun y x τ => decide (L x y) || State y x τ, fun y x => ?_, fun y x τ m h => ?_,
    fun y x τ h => ?_, fun y x => ?_⟩
  · by_cases hL : L x y
    · simp [hL]
    · have := h1 y x hL
      simp only [id] at this
      simp [hL, this]
  · obtain ⟨ha, hb⟩ := Bool.or_eq_false_iff.1 h
    exact Bool.or_eq_false_iff.2 ⟨ha, h2 y x τ m hb⟩
  · obtain ⟨ha, hb⟩ := Bool.or_eq_false_iff.1 h
    exact h3 y x τ (by simpa using ha) hb
  · have h5 :=
      JointLaw.orFlag _ _ ε _ (fun j => ((x j).map fun xj => decide (L xj y)).getD false) (h4 y x)
    refine cast (congrArg (JointLaw N Q.loc.shape Q.ann ε) ?_) h5
    funext j
    beta_reduce
    cases x j <;> rfl

/-! ## 5. The declarations of this part are not in this library -/




end Iop
