-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Compose.lean: how round-by-round soundness behaves when protocols are composed. The notion is
`Doomed` (Iop/Rbr.lean): the prover is doomed ("has lost" in some comments below) towards `bad`, a
property of transcripts that is bad for it, if, whatever it sends next, at most ε_i values of the
next challenge lead to a prefix at which it is not doomed; after the last round, doomed means that
`bad` holds.

Rules for soundness with relaxation (`Reduction.Sound`): a larger input language; two state
functions, errors add; sequential composition, errors concatenated.

How the notions are formalized.
* A statement (x, y) is one value a : A. The split into an explicit and an implicit part matters for
  queries, not for the rules of this file. A language is a predicate on A.
* A reduction is a list of rounds and the function out(a, τ): `none` is "reject".
* "Sound with relaxation (L, L') and errors ε" is: for every statement outside L the prover is
  doomed (`Iop.Doomed`) towards "the output is not a statement in L'". This file does not prove that
  this is the case if and only if a state function exists. The Lean statements below name no state
  function.
* "At least one round" is not needed: with `Doomed` nothing goes wrong for the empty list of rounds,
  and reductions without rounds are useful for re-bracketing.

Related published work on the sequential composition of reductions, which has not been compared
with this file: Anubhav Baweja,
Pratyush Mishra, Tushar Mopuri and Matan Shtepel, "FICS and FACS: Fast IOPPs and Accumulation via
Code-Switching", ePrint 2025/737; Abhiram Kothapalli and Bryan Parno, "Algebraic Reductions of
Knowledge", ePrint 2022/009. Doomed is a notion of soundness, without witnesses or extractors, and
it takes an explicit bound for each challenge.

Round-by-round soundness is the notion of R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G.
Rothblum, R. Rothblum, ePrint 2018/1004, Definition 5.3.
-/
import Iop.ShapeKit
import Iop.State

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Sets of verifier randomness that restrict one part only -/

/-- A condition on the first part of ρ has the same probability in the longer protocol. -/
theorem prRho_cylFst {s : Shape} (t : Shape) (S : Set (Rho s)) :
    prRho (Rho.cylFst t S) = prRho S := by
  unfold prRho
  rw [← map_unif_equiv (Rho.appEquiv s t), pr_map, ← map_fst_unif (C := Rho s) (D := Rho t), pr_map]
  congr 1
  ext p
  show Rho.fst (Rho.app p.1 p.2) ∈ S ↔ p.1 ∈ S
  rw [Rho.fst_app]

/-- A condition on the second part of ρ has the same probability in the longer protocol. -/
theorem prRho_cylSnd (s : Shape) {t : Shape} (S : Set (Rho t)) :
    prRho (Rho.cylSnd s S) = prRho S := by
  unfold prRho
  rw [← map_unif_equiv (Rho.appEquiv s t), pr_map, ← map_snd_unif (C := Rho s) (D := Rho t), pr_map]
  congr 1
  ext p
  show Rho.snd (s := s) (Rho.app p.1 p.2) ∈ S ↔ p.2 ∈ S
  rw [Rho.snd_app]

/-- A union bound: conditions on the two parts of ρ have at most the sum of their probabilities. -/
theorem prRho_cyl_union_le {s t : Shape} (S : Set (Rho s)) (T : Set (Rho t)) :
    prRho (Rho.cylFst t S ∪ Rho.cylSnd s T) ≤ prRho S + prRho T := by
  rw [← prRho_cylFst t S, ← prRho_cylSnd s T]
  exact pr_union_le _ _ _

/-- The same when the excluded set of the second part depends on the first part of ρ: if for every
first part outside S the set T ρ₁ of excluded second parts has probability at most p, the
probabilities still add. -/
theorem prRho_fibre_le {s t : Shape} (S : Set (Rho s)) (T : Rho s → Set (Rho t))
    (p : ℝ≥0∞) (h : ∀ ρ₁, ρ₁ ∉ S → prRho (T ρ₁) ≤ p) :
    prRho (Rho.cylFst t S ∪ {ρ : Rho (s ++ t) | Rho.snd (s := s) ρ ∈ T (Rho.fst ρ)}) ≤
      prRho S + p := by
  unfold prRho
  rw [← map_unif_equiv (Rho.appEquiv s t), pr_map, unif_prod]
  unfold Prob.prod
  refine pr_bind_le_add _ _ _ S (fun a _ ha => ?_)
  rw [pr_map]
  refine le_trans (pr_mono _ ?_) (h a ha)
  intro b hb
  rcases hb with hb | hb
  · have hb' : Rho.fst (Rho.app a b) ∈ S := hb
    rw [Rho.fst_app] at hb'
    exact absurd hb' ha
  · have hb' : Rho.snd (s := s) (Rho.app a b) ∈ T (Rho.fst (Rho.app a b)) := hb
    rwa [Rho.snd_app, Rho.fst_app] at hb'

/-- `prRho_cylFst` as a count: each ρ of the first part extends to as many ρ of the whole as the
second part has values. -/
theorem cnt_cylFst {s : Shape} (t : Shape) (S : Set (Rho s)) :
    cnt (fun ρ : Rho (s ++ t) => ρ ∈ Rho.cylFst t S) =
      cnt (fun ρ : Rho s => ρ ∈ S) * Fintype.card (Rho t) := by
  rw [← cnt_equiv (Rho.appEquiv s t), ← cnt_fst (D := Rho t)]
  refine cnt_congr fun p => ?_
  show Rho.fst (Rho.app p.1 p.2) ∈ S ↔ p.1 ∈ S
  rw [Rho.fst_app]

theorem cnt_cylSnd (s : Shape) {t : Shape} (S : Set (Rho t)) :
    cnt (fun ρ : Rho (s ++ t) => ρ ∈ Rho.cylSnd s S) =
      Fintype.card (Rho s) * cnt (fun ρ : Rho t => ρ ∈ S) := by
  rw [← cnt_equiv (Rho.appEquiv s t), ← cnt_snd (C := Rho s)]
  refine cnt_congr fun p => ?_
  show Rho.snd (s := s) (Rho.app p.1 p.2) ∈ S ↔ p.2 ∈ S
  rw [Rho.snd_app]


/-! ## 2. Lists of errors: order, maximum, sum, zero

The order `Err.le` and the maximum `Err.max` are defined in Iop/Rbr.lean; that the order is
reflexive and transitive, `Err.max_le`, `Err.Below.mono` (a bound on all errors of a list, as
probabilities, holds for every smaller list) and `Err.Below.max` are in Iop/State.lean. -/

namespace Err

/-- All errors are 0. -/
def zero : (s : Shape) → Err s
  | [] => ()
  | _ :: s => (0, zero s)

/-- The sum of the errors in each round. -/
def add : {s : Shape} → Err s → Err s → Err s
  | [], _, _ => ()
  | _ :: _, (e, ε), (e', ε') => (e + e', add ε ε')

theorem zero_le : ∀ {s : Shape} (ε : Err s), le (zero s) ε
  | [], _ => trivial
  | _ :: _, (_, ε) => ⟨Nat.zero_le _, zero_le ε⟩

theorem le_add_right : ∀ {s : Shape} (a b : Err s), le a (add a b)
  | [], _, _ => trivial
  | _ :: _, (_, a), (_, b) => ⟨Nat.le_add_right _ _, le_add_right a b⟩

theorem le_add_left : ∀ {s : Shape} (a b : Err s), le b (add a b)
  | [], _, _ => trivial
  | _ :: _, (_, a), (_, b) => ⟨Nat.le_add_left _ _, le_add_left a b⟩

theorem max_le_add {s : Shape} (a b : Err s) : le (max a b) (add a b) :=
  max_le (le_add_right a b) (le_add_left a b)

theorem add_zero : ∀ {s : Shape} (a : Err s), add a (zero s) = a
  | [], () => rfl
  | _ :: _, (e, a) => by
      show (e + 0, add a (zero _)) = (e, a)
      rw [add_zero a, Nat.add_zero]

theorem zero_add : ∀ {s : Shape} (a : Err s), add (zero s) a = a
  | [], () => rfl
  | _ :: _, (e, a) => by
      show (0 + e, add (zero _) a) = (e, a)
      rw [zero_add a, Nat.zero_add]

theorem max_self : ∀ {s : Shape} (a : Err s), max a a = a
  | [], () => rfl
  | _ :: _, (e, a) => by
      show ((Max.max e e : ℕ), max a a) = (e, a)
      rw [max_self a, Nat.max_self]

theorem le_app :
    ∀ {s t : Shape} {a a' : Err s} {b b' : Err t},
      le a a' → le b b' → le (Err.app a b) (Err.app a' b')
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, (_, _), (_, _), _, _, h, h' => ⟨h.1, le_app h.2 h'⟩

theorem zero_app : ∀ (s t : Shape), Err.app (zero s) (zero t) = zero (s ++ t)
  | [], _ => rfl
  | _ :: s, t => by
      show ((0 : ℕ), Err.app (zero s) (zero t)) = (0, zero (s ++ t))
      rw [zero_app s t]

theorem max_app : ∀ {s t : Shape} (a a' : Err s) (b b' : Err t),
    max (Err.app a b) (Err.app a' b') = Err.app (max a a') (max b b')
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (e, a), (e', a'), b, b' => by
      show (Nat.max e e', max (Err.app a b) (Err.app a' b')) =
        (Nat.max e e', Err.app (max a a') (max b b'))
      rw [max_app a a' b b']

theorem add_app : ∀ {s t : Shape} (a a' : Err s) (b b' : Err t),
    add (Err.app a b) (Err.app a' b') = Err.app (add a a') (add b b')
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (e, a), (e', a'), b, b' => by
      show (e + e', add (Err.app a b) (Err.app a' b')) = (e + e', Err.app (add a a') (add b b'))
      rw [add_app a a' b b']

/-! How the bound "every error, as a probability, is at most c" (`Err.Below`, the form in which the
compiler (Compile/) takes the errors) behaves. -/

theorem Below.mono_bound : ∀ {s : Shape} {ε : Err s} {c c' : ℝ≥0∞}, c ≤ c' → Below ε c → Below ε c'
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), _, _, h, h' =>
    ⟨_root_.le_trans h'.1 (mul_le_mul_left h _), Below.mono_bound h h'.2⟩

theorem Below.zero : ∀ (s : Shape) (c : ℝ≥0∞), Below (zero s) c
  | [], _ => trivial
  | _ :: s, c => ⟨by simp, Below.zero s c⟩

theorem Below.add :
    ∀ {s : Shape} {ε ε' : Err s} {c c' : ℝ≥0∞}, Below ε c → Below ε' c' → Below (add ε ε') (c + c')
  | [], _, _, _, _, _, _ => trivial
  | r :: _, (e, _), (e', _), c, c', h, h' =>
      ⟨by
        show ((e + e' : ℕ) : ℝ≥0∞) ≤ (c + c') * (Fintype.card r.Chal : ℝ≥0∞)
        rw [Nat.cast_add, add_mul]; exact add_le_add h.1 h'.1,
       Below.add h.2 h'.2⟩

theorem Below.app :
    ∀ {s t : Shape} {ε : Err s} {ε' : Err t} {c : ℝ≥0∞},
      Below ε c → Below ε' c → Below (Err.app ε ε') c
  | [], _, _, _, _, _, h => h
  | _ :: _, _, (_, _), _, _, h, h' => ⟨h.1, Below.app h.2 h'⟩

end Err

/-! ## 3. Rules for "the prover has lost" (is doomed) -/

theorem Doomed.congr (s : Shape) (ε : Err s) {bad bad' : Tr s → Prop} (h : ∀ τ, bad τ ↔ bad' τ) :
    Doomed s ε bad ↔ Doomed s ε bad' :=
  ⟨Doomed.mono s ε fun τ => (h τ).1, Doomed.mono s ε fun τ => (h τ).2⟩

/-- If every full transcript is bad for the prover, it has lost, with any errors; in particular with
all errors 0. -/
theorem Doomed.of_forall :
    ∀ (s : Shape) (ε : Err s) {bad : Tr s → Prop}, (∀ τ, bad τ) → Doomed s ε bad
  | [], _, _, h => h ()
  | _ :: s, (_, ε), _, h => fun m => by
      rw [cnt_false (fun c hc => hc (Doomed.of_forall s ε (fun τ => h (m, c, τ))))]
      exact Nat.zero_le _

/-- Two goals at once; the errors add (the state is the maximum of two state functions).
A prover that is doomed towards each of two goals is doomed towards both together. -/
theorem Doomed.and : ∀ (s : Shape) {ε ε' : Err s} {bad bad' : Tr s → Prop},
    Doomed s ε bad → Doomed s ε' bad' → Doomed s (Err.add ε ε') (fun τ => bad τ ∧ bad' τ)
  | [], _, _, _, _, h, h' => ⟨h, h'⟩
  | _ :: s, (_, _), (_, _), _, _, h, h' => fun m =>
      le_trans
        (cnt_le_add (fun c hc => by
          by_contra hn
          rw [not_or, not_not, not_not] at hn
          exact hc (Doomed.and s hn.1 hn.2)))
        (Nat.add_le_add (h m) (h' m))

/-- Sequential composition, in both directions: with concatenated errors, the prover has lost in s
++ t if and only if it has lost in s towards "it has lost in t". -/
theorem Doomed.append_iff :
    ∀ (s t : Shape) (ε : Err s) (ε' : Err t) (bad : Tr (s ++ t) → Prop),
      Doomed (s ++ t) (Err.app ε ε') bad ↔
      Doomed s ε (fun a => Doomed t ε' (fun b => bad (Tr.app a b)))
  | [], _, _, _, _ => Iff.rfl
  | r :: s, t, (e, ε), ε', bad => by
      show (∀ m : r.Msg,
          cnt (fun c : r.Chal => ¬ Doomed (s ++ t) (Err.app ε ε') (fun τ => bad (m, c, τ))) ≤ e) ↔
        (∀ m : r.Msg,
          cnt (fun c : r.Chal =>
              ¬ Doomed s ε (fun a => Doomed t ε' (fun b => bad (m, c, Tr.app a b)))) ≤ e)
      refine forall_congr' fun m => ?_
      rw [cnt_congr (fun c => not_congr (Doomed.append_iff s t ε ε' (fun τ => bad (m, c, τ))))]

/-- The family of empty bad sets. -/
def BadFam.empty : (s : Shape) → BadFam s
  | [] => ()
  | _ :: s => (fun _ => ∅, fun _ _ => BadFam.empty s)

theorem BadFam.empty_within : ∀ (s : Shape) (ε : Err s), (BadFam.empty s).Within ε
  | [], _ => trivial
  | _ :: s, (_, ε) =>
      ⟨fun _ => (cnt_false (fun c => Set.notMem_empty c)).le.trans (Nat.zero_le _),
        fun _ _ => BadFam.empty_within s ε⟩

/-- Bad sets for two lists of rounds in a row; those of the second part may depend on the transcript
of the first. -/
def BadFam.app : {s t : Shape} → BadFam s → (Tr s → BadFam t) → BadFam (s ++ t)
  | [], _, _, g => g ()
  | _ :: _, _, (B, k), g => (B, fun m c => BadFam.app (k m c) (fun a => g (m, c, a)))

theorem BadFam.clean_app :
    ∀ {s t : Shape} (B : BadFam s) (g : Tr s → BadFam t) (a : Tr s) (b : Tr t),
      (BadFam.app B g).Clean (Tr.app a b) ↔ B.Clean a ∧ (g a).Clean b
  | [], _, _, _, (), _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (B, k), g, (m, c, a), b => by
      show (c ∉ B m ∧ (BadFam.app (k m c) (fun a => g (m, c, a))).Clean (Tr.app a b)) ↔
        ((c ∉ B m ∧ (k m c).Clean a) ∧ (g (m, c, a)).Clean b)
      rw [BadFam.clean_app (k m c) (fun a => g (m, c, a)) a b, and_assoc]

theorem BadFam.within_app :
    ∀ {s t : Shape} {B : BadFam s} {g : Tr s → BadFam t} {ε : Err s} {ε' : Err t},
      B.Within ε → (∀ a, (g a).Within ε') → (BadFam.app B g).Within (Err.app ε ε')
  | [], _, _, _, _, _, _, h => h ()
  | _ :: _, _, (_, _), _, (_, _), _, h, h' =>
    ⟨h.1, fun m c => BadFam.within_app (h.2 m c) (fun a => h' (m, c, a))⟩

/-- The converse of `doomed_of_clean`: a prover that is doomed is doomed by way of bad sets. -/
theorem Doomed.exists_badFam : ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop), Doomed s ε bad →
    ∃ B : BadFam s, B.Within ε ∧ ∀ τ, B.Clean τ → bad τ
  | [], _, _, h => ⟨(), trivial, fun _ _ => h⟩
  | r :: s, (e, ε), bad, h => by
      have ih : ∀ (m : r.Msg) (c : r.Chal), ∃ B : BadFam s, B.Within ε ∧
          (Doomed s ε (fun τ => bad (m, c, τ)) → ∀ τ, B.Clean τ → bad (m, c, τ)) := fun m c => by
        by_cases hd : Doomed s ε (fun τ => bad (m, c, τ))
        · obtain ⟨B, hW, hC⟩ := Doomed.exists_badFam s ε _ hd
          exact ⟨B, hW, fun _ => hC⟩
        · exact ⟨BadFam.empty s, BadFam.empty_within s ε, fun h' => absurd h' hd⟩
      choose k hW hC using ih
      refine ⟨(fun m => {c | ¬ Doomed s ε (fun τ => bad (m, c, τ))}, k), ⟨fun m => h m, hW⟩, ?_⟩
      rintro ⟨m, c, τ⟩ ⟨hc, hτ⟩
      exact hC m c (not_not.mp hc) τ hτ

/-- "The prover has lost" (is doomed) is the same as "bad sets and a backward step": there are bad
sets within the errors such that every transcript without a bad challenge is bad for the prover. -/
theorem doomed_iff_exists_badFam (s : Shape) (ε : Err s) (bad : Tr s → Prop) :
    Doomed s ε bad ↔ ∃ B : BadFam s, B.Within ε ∧ ∀ τ, B.Clean τ → bad τ :=
  ⟨Doomed.exists_badFam s ε bad, fun ⟨B, hW, hC⟩ => doomed_of_clean s ε B bad hW hC⟩

/-! ## 4. Reductions and their soundness -/

/-- A public-coin interactive reduction with a fixed list of rounds from statements in A to
statements in B.
A statement is the pair of the explicit and the implicit instance, taken as one value. After the
rounds the verifier rejects (`none`) or outputs a statement; by convention this is a function of the
input statement and the full transcript.
A proof system is a reduction to the type `Unit` of the one trivial statement. -/
structure Reduction (A B : Type) where
  shape : Shape
  out   : A → Tr shape → Option B

namespace Reduction

variable {A A' B C D : Type}

/-- Round-by-round soundness with relaxation (LA, LB) and errors ε: on every statement outside LA
the prover is doomed, at the start, towards "the verifier rejects or outputs a statement outside
LB".
It is required of every statement a : A, whether or not it is in any relation. -/
def Sound (K : Reduction A B) (LA : A → Prop) (LB : B → Prop) (ε : Err K.shape) : Prop :=
  ∀ a, ¬ LA a → Doomed K.shape ε (fun τ => ∀ b, K.out a τ = some b → ¬ LB b)





/-! ### 4.1 Rules that leave the protocol as it is -/

section SameProtocol
variable {K : Reduction A B} {LA LA' : A → Prop} {LB LB' : B → Prop} {ε ε' : Err K.shape}

/-- Consequence: the input language may grow and the output language may shrink. -/
theorem Sound.conseq (h : K.Sound LA LB ε) (hA : ∀ a, LA a → LA' a) (hB : ∀ b, LB' b → LB b) :
    K.Sound LA' LB' ε :=
  fun a ha =>
    Doomed.mono _ _ (fun _ hτ b hb hLB => hτ b hb (hB b hLB)) (h a fun hLA => ha (hA a hLA))

/-- A larger input language. In particular a reduction that is sound is sound under every
promise. -/
theorem Sound.larger (h : K.Sound LA LB ε) (S : A → Prop) : K.Sound (fun a => LA a ∨ S a) LB ε :=
  h.conseq (fun _ => Or.inl) (fun _ => id)

/-- Larger errors are weaker. -/
theorem Sound.mono_err (h : K.Sound LA LB ε) (hε : Err.le ε ε') : K.Sound LA LB ε' :=
  fun a ha => Doomed.mono_err _ hε (h a ha)

/-- Two state functions: the languages unite and the errors add. -/
theorem Sound.union (h : K.Sound LA LB ε) (h' : K.Sound LA' LB' ε') :
    K.Sound (fun a => LA a ∨ LA' a) (fun b => LB b ∨ LB' b) (Err.add ε ε') := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b hb hor => hor.elim (hτ.1 b hb) (hτ.2 b hb))
    (Doomed.and _ (h a fun x => ha (Or.inl x)) (h' a fun x => ha (Or.inr x)))

/-- Two input languages, one output language: the larger error in each round. A statement outside
the intersection is outside one of the two languages, and which one is known before the protocol
starts. -/
theorem Sound.inter (h : K.Sound LA LB ε) (h' : K.Sound LA' LB ε') :
    K.Sound (fun a => LA a ∧ LA' a) LB (Err.max ε ε') := by
  intro a ha
  by_cases h1 : LA a
  · exact Doomed.mono_err _ (Err.le_max_right ε ε') (h' a fun h2 => ha ⟨h1, h2⟩)
  · exact Doomed.mono_err _ (Err.le_max_left ε ε') (h a h1)

/-- One protocol, two pairs of languages (for challenges that serve two purposes at once): soundness
for the intersection of the input languages and that of the output languages, with the larger error
in each round. -/
theorem Sound.both (h : K.Sound LA LB ε) (h' : K.Sound LA' LB' ε') :
    K.Sound (fun a => LA a ∧ LA' a) (fun b => LB b ∧ LB' b) (Err.max ε ε') :=
  (h.conseq (fun _ => id) fun _ hb => hb.1).inter (h'.conseq (fun _ => id) fun _ hb => hb.2)

/-- A proof by cases on the statement, with the larger error in each round: soundness for the
statements with P and soundness for those without P give soundness. -/
theorem Sound.by_cases (P : A → Prop) (h : K.Sound (fun a => LA a ∨ ¬ P a) LB ε)
    (h' : K.Sound (fun a => LA a ∨ P a) LB ε') : K.Sound LA LB (Err.max ε ε') :=
  (h.inter h').conseq
    (fun _ hh => hh.1.elim id fun hn => hh.2.elim id fun hp => absurd hp hn) (fun _ => id)

/-- Any family of input languages with one error list: soundness for their intersection. -/
theorem Sound.iInter {ι : Sort*} {LAs : ι → A → Prop} (h : ∀ i, K.Sound (LAs i) LB ε) :
    K.Sound (fun a => ∀ i, LAs i a) LB ε := by
  intro a ha
  obtain ⟨i, hi⟩ := not_forall.mp ha
  exact h i a hi

/-- Nothing is to be shown if every statement is in the input language, or no statement in the
output language. -/
theorem sound_of_forall (ε : Err K.shape) (h : ∀ a, LA a) : K.Sound LA LB ε := fun a ha =>
  absurd (h a) ha

theorem sound_of_forall_not (ε : Err K.shape) (h : ∀ b, ¬ LB b) : K.Sound LA LB ε :=
  fun _ _ => Doomed.of_forall _ _ fun _ b _ => h b

end SameProtocol

/-! ### 4.2 Side conditions: the frame rule -/

section Frame
variable {K : Reduction A B} {LA S S₂ : A → Prop} {LB S' S₂' : B → Prop} {ε : Err K.shape}



/-- Frame rule. A condition may be added on both sides if the one on the
output implies the one on the input; for this implication the languages of the reduction itself may
be assumed. (So the added condition need not be on copied components: the output condition may be
about an object that the prover has sent, the input condition about the true object, if LB says that
the two agree.) -/
theorem Sound.frame_and_of (h : K.Sound LA LB ε)
    (hc : ∀ a τ b, K.out a τ = some b → LA a → LB b → S' b → S a) :
    K.Sound (fun a => LA a ∧ S a) (fun b => LB b ∧ S' b) ε := by
  intro a ha
  by_cases hLA : LA a
  · exact Doomed.of_forall _ _ fun τ b hb hLB => ha ⟨hLA, hc a τ b hb hLA hLB.1 hLB.2⟩
  · exact Doomed.mono _ _ (fun _ hτ b hb hLB => hτ b hb hLB.1) (h a hLA)


end Frame

/-! ### 4.3 Sequential composition -/

/-- The first reduction followed by the second on its output. If the first rejects, the rounds of
the second still take place and the verifier rejects at the end (by convention).
Bracket longer compositions to the right, K₁.seq (K₂.seq K₃): the lists of rounds of the two
bracketings are equal by a lemma only, not by definition, and no associativity is stated. -/
@[reducible] def seq (K₁ : Reduction A B) (K₂ : Reduction B C) : Reduction A C where
  shape := K₁.shape ++ K₂.shape
  out a τ := (K₁.out a (Tr.fst τ)).bind fun b => K₂.out b (Tr.snd (s := K₁.shape) τ)

theorem seq_out_app (K₁ : Reduction A B) (K₂ : Reduction B C) (a : A)
    (τ₁ : Tr K₁.shape) (τ₂ : Tr K₂.shape) :
    (K₁.seq K₂).out a (Tr.app τ₁ τ₂) = (K₁.out a τ₁).bind fun b => K₂.out b τ₂ := by
  show (K₁.out a (Tr.fst (Tr.app τ₁ τ₂))).bind
      (fun b => K₂.out b (Tr.snd (s := K₁.shape) (Tr.app τ₁ τ₂))) = _
  rw [Tr.fst_app, Tr.snd_app]

/-- Sequential composition: if both reductions are sound and the middle languages agree, the
composed reduction is sound, and its errors are those of the first followed by those of the second.
-/
theorem Sound.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {LA : A → Prop}
    {LB : B → Prop} {LC : C → Prop} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    (h₁ : K₁.Sound LA LB ε₁) (h₂ : K₂.Sound LB LC ε₂) :
    (K₁.seq K₂).Sound LA LC (Err.app ε₁ ε₂) := by
  intro a ha
  refine Doomed.append K₁.shape K₂.shape ε₁ ε₂ _ (Doomed.mono _ _ ?_ (h₁ a ha))
  intro τ₁ hτ₁
  cases hout : K₁.out a τ₁ with
  | none =>
      refine Doomed.of_forall _ _ fun τ₂ c hc => ?_
      rw [seq_out_app, hout] at hc
      exact absurd hc (by simp)
  | some b =>
      refine Doomed.mono _ _ ?_ (h₂ b (hτ₁ b hout))
      intro τ₂ h c hc
      rw [seq_out_app, hout] at hc
      exact h c hc


/-! ### 4.4 A lemma on `Option.map` -/

private theorem forall_map_eq_some {o : Option B} {f : B → D} {P : D → Prop} :
    (∀ p, o.map f = some p → P p) ↔ ∀ b, o = some b → P (f b) := by
  cases o <;> simp










end Reduction

end Iop
