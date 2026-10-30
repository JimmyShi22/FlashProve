-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyStep.lean: a calculus of steps, to prove a long written protocol sound block by
block.

A written protocol with many blocks (some repeated a variable number of times, some nested in
others) is proved sound by passing a false claim from block to block: if the claim before a block is
false then, but for few verifier messages, the claim after it is false, or the verifier refuses.
This file gives that argument one form, and rules that join blocks, so that the whole protocol's
rounds, error counts, tests and soundness statement are made from the blocks' by the same terms.

A step from states X to states X' holds a list of written rounds, an error count for each round, a
test in the field on a state and a transcript of these rounds (`ok`), and the state after the rounds
(`nx`). A state holds all that the argument needs: what the verifier holds (claims, points, rows put
aside for a later test, counters), what was sent, and values that no verifier computes, such as the
one decoding of a word that was sent. So a claim is a predicate on states alone.

`Step.Sem S Φ Φ'` says: from a state of which Φ is false the prover has lost (the library's
`Doomed`, Iop/Rbr.lean), with the step's error counts, towards "a test of work fails, or the step's
test fails, or Φ' is false of the next state".

A step holds a list of rounds and not a shape. Transcripts of a joined list are cut by functions
that are defined by recursion on the first list (`fstT`, `sndT`, beside `joinT` of
OnBytes/Slice/Unfold.lean). So the shape of a composed step is the shape of its list of rounds by
definition, and no rule of this file has a cast in its statement or its proof.

Main definitions.
 `uW`, `passT`          the shape of a list of written rounds; all its tests of work pass.
 `fstT`, `sndT`, `appE`  the two parts of a joined transcript; two lists of error counts joined.
 `Step`, `Step.Sem`     a step, and its soundness statement.
 `Step.pure`, `Step.nil`, `Step.one`, `Step.idle`   a step without rounds; the empty step; a step
                        of one round; rounds in which nothing is tested but work.
 `Step.seq`             one step after another.
 `Step.iter`            n steps in a row, where the type of the state depends on the number of steps
                        taken.
 `Step.many`            a step for each member of a list, in a row.
 `Step.lens`            a step on small states, used on large ones.
 `Step.guard`           a step with one more test, of the state before it.
 `Step.Keeps`           a fact passes a step.
 `Step.SemT`            the statement in the form that leaves open what rounds follow.
Main theorems.
 `doomed_join`          the library's `Doomed.append` over a joined list of rounds.
 `Step.Sem.seq`, `.iter`, `.many`, `.lens`, `.lens_of`, `.pure`   the statement passes to composed
                        steps.
 `Step.Sem.conseq`      a weaker claim before, a stronger claim after.
 `Step.Sem.skip`        rounds in which nothing can be won, with any error counts.
 `Step.Sem.conj`, `.frame`, `.test`   two claims at once; a claim that rides along; a test in the
                        middle, after which the second claim alone is left.
 `Step.Keeps`, `Step.Sem.inv`, `.under`   a fact that is true all along: it passes the steps by
                        rules of its own, and is at hand in a step's statement.
 `Step.Sem.fixed`       a claim on a value that was fixed earlier, if there is one.
 `Step.Sem.guard`, `.guard_gives`   what a step tests of the state before it is at hand in its
                        statement, and may be assumed in the claim after it. `Step.Keeps.guard`: a
                        fact passes such a step.
 `Step.Sem.all`         a family of claims at once.
 `Step.Sem.doomed`, `Step.Sem.of_bad`   the statement towards any predicate.
 `Step.Sem.final`       where the last claim is `True`, the prover has lost towards a no.
 `Step.Sem.toT`, `.ofT`, `Step.SemT.seq`   the statement is equivalent to the form that leaves open
                        what rounds follow (`Step.SemT`), so a block's statement may come in either
                        form, and the rule for one step after another holds in that form too. The
                        rules are proved in the form without such rounds. There they need no
                        equation between shapes: (a ++ b) ++ t and a ++ (b ++ t) are not the same by
                        definition.
Not claimed. Nothing on any one protocol, on the sizes of error counts, or on any verifier's text.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.ManyCloses

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run

/-! ## Written transcripts, cut in two -/

/-- The shape of a list of written rounds. -/
abbrev uW (ds : List PQ.RD) : Shape := PQ.uL (ckP .two) ds

/-- All tests of work of a written transcript pass. -/
def passT (ds : List PQ.RD) (τ : Tr (uW ds)) : Prop :=
  PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true

/-- The first part of a transcript of a joined list of rounds. -/
def fstT : (a b : List PQ.RD) → Tr (uW (a ++ b)) → Tr (uW a)
  | [], _, _ => ()
  | _ :: a, b, (m, c, τ) => (m, c, fstT a b τ)

/-- The second part of a transcript of a joined list of rounds. -/
def sndT : (a b : List PQ.RD) → Tr (uW (a ++ b)) → Tr (uW b)
  | [], _, τ => τ
  | _ :: a, b, (_, _, τ) => sndT a b τ

/-- The first part of a joined transcript. -/
theorem fstT_joinT : ∀ (a b : List PQ.RD) (x : Tr (uW a)) (y : Tr (uW b)),
    fstT a b (joinT a b x y) = x
  | [], _, (), _ => rfl
  | d :: a, b, (m, c, x), y => by
    show ((m, c, fstT a b (joinT a b x y)) : Tr (uW (d :: a))) = (m, c, x)
    rw [fstT_joinT a b x y]

/-- The second part of a joined transcript. -/
theorem sndT_joinT : ∀ (a b : List PQ.RD) (x : Tr (uW a)) (y : Tr (uW b)),
    sndT a b (joinT a b x y) = y
  | [], _, _, _ => rfl
  | _ :: a, b, (_, _, x), y => sndT_joinT a b x y

/-- A transcript of a joined list of rounds is its two parts joined. -/
theorem joinT_fstT_sndT : ∀ (a b : List PQ.RD) (τ : Tr (uW (a ++ b))),
    joinT a b (fstT a b τ) (sndT a b τ) = τ
  | [], _, _ => rfl
  | d :: a, b, (m, c, τ) => by
    show ((m, c, joinT a b (fstT a b τ) (sndT a b τ)) : Tr (uW (d :: (a ++ b)))) = (m, c, τ)
    rw [joinT_fstT_sndT a b τ]

/-- A transcript of a joined list of rounds is made of two transcripts. -/
theorem exists_joinT (a b : List PQ.RD) (τ : Tr (uW (a ++ b))) : ∃ x y, τ = joinT a b x y :=
  ⟨_, _, (joinT_fstT_sndT a b τ).symm⟩

/-- The tests of work of a joined transcript pass if and only if they pass in both parts. -/
theorem passT_joinT (a b : List PQ.RD) (x : Tr (uW a)) (y : Tr (uW b)) :
    passT (a ++ b) (joinT a b x y) ↔ passT a x ∧ passT b y := by
  unfold passT
  rw [pass_joinT, Bool.and_eq_true]

/-- Two lists of error counts, joined. -/
def appE : (a b : List PQ.RD) → Err (uW a) → Err (uW b) → Err (uW (a ++ b))
  | [], _, _, ε' => ε'
  | _ :: a, b, (e, ε), ε' => (e, appE a b ε ε')

/-- Sequential composition over a joined list of rounds: the error counts are joined. -/
theorem doomed_join : ∀ (a b : List PQ.RD) (ε : Err (uW a)) (ε' : Err (uW b))
    (bad : Tr (uW (a ++ b)) → Prop),
    Doomed (uW a) ε (fun x => Doomed (uW b) ε' fun y => bad (joinT a b x y)) →
    Doomed (uW (a ++ b)) (appE a b ε ε') bad
  | [], _, _, _, _, h => h
  | _ :: a, b, (_, ε), ε', bad, h => fun m =>
    le_trans (cnt_mono fun c hc hd' => hc (doomed_join a b ε ε' (fun τ => bad (m, c, τ)) hd')) (h m)

/-- No rounds behind: the empty shape can be taken off the end. -/
theorem doomed_app_nil : ∀ (s : Shape) (ε : Err s) (bad : Tr (s ++ []) → Prop),
    Doomed (s ++ []) (Err.app ε ()) bad → Doomed s ε fun a => bad (Tr.app a ())
  | [], _, _, h => h
  | _ :: s, (_, ε), bad, h => fun m =>
    le_trans (cnt_mono fun c hc hd => hc (doomed_app_nil s ε (fun τ => bad (m, c, τ)) hd)) (h m)

/-! ## Steps -/

/-- A step from states X to states X'. rds: its written rounds. err: an error count for each. ok:
its test in the field, on the state before it and its rounds' transcript; tests of work are not in
it. nx: the state after it. -/
structure Step (X X' : Type) where
  rds : List PQ.RD
  err : Err (uW rds)
  ok : X → Tr (uW rds) → Prop
  nx : X → Tr (uW rds) → X'

namespace Step

variable {X Y Z X' A A' M : Type}

/-- The step's soundness statement. From a state of which the claim Φ is false, the prover has lost
in the step's rounds towards: a test of work fails, or the step's test fails, or the claim Φ' is
false of the next state. -/
def Sem (S : Step X X') (Φ : X → Prop) (Φ' : X' → Prop) : Prop :=
  ∀ x, ¬ Φ x → Doomed (uW S.rds) S.err fun τ => passT S.rds τ → S.ok x τ → ¬ Φ' (S.nx x τ)

/-- A step without rounds: the test p, the next state f. -/
def pure (p : X → Prop) (f : X → X') : Step X X' := ⟨[], (), fun x _ => p x, fun x _ => f x⟩

/-- The empty step. -/
def nil : Step X X := pure (fun _ => True) id

/-- A step of one round d with the error count e: the test p and the next state f see the state, the
prover's message and the verifier's. -/
def one (d : PQ.RD) (e : ℕ) (p : X → (wRound d).Msg → (wRound d).Chal → Prop)
    (f : X → (wRound d).Msg → (wRound d).Chal → X') : Step X X' :=
  ⟨[d], (e, ()), fun x τ => p x τ.1 τ.2.1, fun x τ => f x τ.1 τ.2.1⟩

/-- Rounds in which nothing is tested but work, and which leave the state as it is. -/
def idle (ds : List PQ.RD) (ε : Err (uW ds)) : Step X X := ⟨ds, ε, fun _ _ => True, fun x _ => x⟩

/-- One step after another. -/
def seq (S : Step X Y) (T : Step Y Z) : Step X Z where
  rds := S.rds ++ T.rds
  err := appE S.rds T.rds S.err T.err
  ok x τ := S.ok x (fstT S.rds T.rds τ) ∧ T.ok (S.nx x (fstT S.rds T.rds τ)) (sndT S.rds T.rds τ)
  nx x τ := T.nx (S.nx x (fstT S.rds T.rds τ)) (sndT S.rds T.rds τ)

/-- n steps in a row. The type of the state after i steps is X i. The first step is followed by the
n - 1 steps of the family that begins one later. -/
def iter : (n : ℕ) → (X : ℕ → Type) → (∀ i, Step (X i) (X (i + 1))) → Step (X 0) (X n)
  | 0, _, _ => nil
  | n + 1, X, S => (S 0).seq (iter n (fun i => X (i + 1)) fun i => S (i + 1))

/-- A step for each member of a list, in a row. -/
def many (S : A → Step X X) : List A → Step X X
  | [] => nil
  | a :: l => (S a).seq (many S l)

/-- A step on small states, used on large ones: get takes the small state out, put lays the small
state after the step into the large one. -/
def lens (S : Step A A') (get : X → A) (put : X → A' → X') : Step X X' where
  rds := S.rds
  err := S.err
  ok x τ := S.ok (get x) τ
  nx x τ := put x (S.nx (get x) τ)

/-- The step S with one more test, of the state before it. -/
def guard (S : Step X X') (F : X → Prop) : Step X X' :=
  ⟨S.rds, S.err, fun x τ => F x ∧ S.ok x τ, S.nx⟩

/-- One more step in front of n steps in a row. -/
theorem iter_succ (n : ℕ) (X : ℕ → Type) (S : ∀ i, Step (X i) (X (i + 1))) :
    iter (n + 1) X S = (S 0).seq (iter n (fun i => X (i + 1)) fun i => S (i + 1)) := rfl

/-- The step of the first member, then those of the others. -/
theorem many_cons (S : A → Step X X) (a : A) (l : List A) :
    many S (a :: l) = (S a).seq (many S l) := rfl

/-! ### What a composed step tests and yields, on joined transcripts -/

/-- What one step after another tests, on a joined transcript. -/
theorem seq_ok (S : Step X Y) (T : Step Y Z) (x : X) (a : Tr (uW S.rds)) (b : Tr (uW T.rds)) :
    (S.seq T).ok x (joinT S.rds T.rds a b) ↔ S.ok x a ∧ T.ok (S.nx x a) b := by
  show S.ok x (fstT _ _ (joinT _ _ a b)) ∧
    T.ok (S.nx x (fstT _ _ (joinT _ _ a b))) (sndT _ _ (joinT _ _ a b)) ↔ _
  rw [fstT_joinT, sndT_joinT]

/-- The state after one step after another, on a joined transcript. -/
theorem seq_nx (S : Step X Y) (T : Step Y Z) (x : X) (a : Tr (uW S.rds)) (b : Tr (uW T.rds)) :
    (S.seq T).nx x (joinT S.rds T.rds a b) = T.nx (S.nx x a) b := by
  show T.nx (S.nx x (fstT _ _ (joinT _ _ a b))) (sndT _ _ (joinT _ _ a b)) = _
  rw [fstT_joinT, sndT_joinT]

namespace Sem

variable {S : Step X X'} {Φ Φ₁ Φ₂ Ψ : X → Prop} {Φ' Φ₁' Φ₂' Ψ' : X' → Prop}

/-- The statement towards any predicate that holds wherever a test of work fails, wherever the
step's test fails and wherever the claim after the step is false. -/
theorem doomed (h : S.Sem Φ Φ') (x : X) (hx : ¬ Φ x) (bad : Tr (uW S.rds) → Prop)
    (hp : ∀ τ, ¬ passT S.rds τ → bad τ) (ho : ∀ τ, ¬ S.ok x τ → bad τ)
    (hn : ∀ τ, ¬ Φ' (S.nx x τ) → bad τ) : Doomed (uW S.rds) S.err bad :=
  Doomed.mono _ _ (fun τ hτ => by
    by_cases h1 : passT S.rds τ
    · by_cases h2 : S.ok x τ
      · exact hn τ (hτ h1 h2)
      · exact ho τ h2
    · exact hp τ h1) (h x hx)

/-- The converse of `doomed`. -/
theorem of_bad (h : ∀ x, ¬ Φ x → ∀ bad : Tr (uW S.rds) → Prop, (∀ τ, ¬ passT S.rds τ → bad τ) →
    (∀ τ, ¬ S.ok x τ → bad τ) → (∀ τ, ¬ Φ' (S.nx x τ) → bad τ) → Doomed (uW S.rds) S.err bad) :
    S.Sem Φ Φ' := fun x hx =>
  h x hx _ (fun _ h1 h2 => absurd h2 h1) (fun _ h1 _ h2 => absurd h2 h1) fun _ h1 _ _ => h1

/-- Where the claim after the step is `True`, the prover has lost towards: a test of work or the
step's test fails. -/
theorem final (h : S.Sem Φ fun _ => True) (x : X) (hx : ¬ Φ x) :
    Doomed (uW S.rds) S.err fun τ => ¬ (passT S.rds τ ∧ S.ok x τ) :=
  Doomed.mono _ _ (fun _ hτ hc => hτ hc.1 hc.2 trivial) (h x hx)

/-- A claim before the step that follows from Φ, a claim after it from which Φ' follows. -/
theorem conseq (h : S.Sem Φ Φ') (h1 : ∀ x, Φ x → Ψ x) (h2 : ∀ x', Ψ' x' → Φ' x') : S.Sem Ψ Ψ' :=
  fun x hx => Doomed.mono _ _ (fun _ hτ hp ho hn => hτ hp ho (h2 _ hn)) (h x fun hΦ => hx (h1 x hΦ))

/-- Rounds in which nothing can be won: whatever is sent and drawn, the claim after them gives the
claim before them. Any error counts will do. -/
theorem skip (h : ∀ x τ, S.ok x τ → Φ' (S.nx x τ) → Φ x) : S.Sem Φ Φ' := fun x hx =>
  doomed_of_all _ _ _ fun τ _ ho hn => hx (h x τ ho hn)

/-- Two claims at once, with the same error counts: if one of them is false before the step, one of
them is false after it. -/
theorem conj (h1 : S.Sem Φ₁ Φ₁') (h2 : S.Sem Φ₂ Φ₂') :
    S.Sem (fun x => Φ₁ x ∧ Φ₂ x) fun x' => Φ₁' x' ∧ Φ₂' x' := fun x hx => by
  by_cases hΦ : Φ₁ x
  · exact Doomed.mono _ _ (fun _ hτ hp ho hn => hτ hp ho hn.2) (h2 x fun h => hx ⟨hΦ, h⟩)
  · exact Doomed.mono _ _ (fun _ hτ hp ho hn => hτ hp ho hn.1) (h1 x hΦ)

/-- A claim that rides along: the step does not make it true. -/
theorem frame {R : X → Prop} {R' : X' → Prop} (h : S.Sem Φ Φ')
    (hR : ∀ x τ, R' (S.nx x τ) → R x) : S.Sem (fun x => Φ x ∧ R x) fun x' => Φ' x' ∧ R' x' :=
  h.conj (skip fun x τ _ hn => hR x τ hn)

/-- A test in the middle. The step's statement ends at `True`: if Φ is false the prover has lost in
these rounds. A second claim rides along and is what is left after the step. -/
theorem test {R : X → Prop} {R' : X' → Prop} (h : S.Sem Φ fun _ => True)
    (hR : ∀ x τ, R' (S.nx x τ) → R x) : S.Sem (fun x => Φ x ∧ R x) R' :=
  (h.frame hR).conseq (fun _ hx => hx) fun _ hx => ⟨trivial, hx⟩

/-- A fact that is true all along, such as the length of a list in the state. I gives I' after the
step. A claim "if I then Φ" is false where I holds and Φ does not; so a step's statement can be
proved with I at hand, and I' is at hand for the next step. -/
theorem inv {I : X → Prop} {I' : X' → Prop} (hI : ∀ x τ, I x → I' (S.nx x τ))
    (h : S.Sem (fun x => I x → Φ x) Φ') : S.Sem (fun x => I x → Φ x) fun x' => I' x' → Φ' x' :=
  fun x hx => Doomed.mono _ _
    (fun τ hτ hp ho hn => hτ hp ho (hn (hI x τ (by_contra fun hi => hx fun h' => absurd h' hi))))
    (h x hx)

/-- A claim on a value that was fixed earlier, if there is one. g and g' read the value off the
states; the step leaves it as it is. If the statement holds for each value m, it holds for "there is
a value, and the claim holds of it". Where there is no value nothing can be won; the error counts
are the same. -/
theorem fixed {g : X → Option M} {g' : X' → Option M} {P : M → X → Prop} {P' : M → X' → Prop}
    (hg : ∀ x τ, g' (S.nx x τ) = g x) (h : ∀ m, S.Sem (P m) (P' m)) :
    S.Sem (fun x => ∃ m, g x = some m ∧ P m x) fun x' => ∃ m, g' x' = some m ∧ P' m x' :=
  fun x hx => by
  cases hm : g x with
  | none =>
    refine doomed_of_all _ _ _ fun τ _ _ hn => ?_
    obtain ⟨m, h1, _⟩ := hn
    rw [hg, hm] at h1
    cases h1
  | some m =>
    refine Doomed.mono _ _ (fun τ hτ hp ho hn => ?_) (h m x fun hP => hx ⟨m, hm, hP⟩)
    obtain ⟨m', h1, h2⟩ := hn
    rw [hg, hm] at h1
    cases h1
    exact hτ hp ho h2

end Sem

/-- A step without rounds: its test and the claim after it give the claim before it. -/
theorem Sem.pure {p : X → Prop} {f : X → X'} {Φ : X → Prop} {Φ' : X' → Prop}
    (h : ∀ x, p x → Φ' (f x) → Φ x) : (Step.pure p f).Sem Φ Φ' :=
  Sem.skip fun x _ ho hn => h x ho hn

/-- The empty step keeps every claim. -/
theorem Sem.nil {Φ : X → Prop} : (Step.nil : Step X X).Sem Φ Φ := Sem.pure fun _ _ h => h

/-- One step after another. -/
theorem Sem.seq {S : Step X Y} {T : Step Y Z} {Φ : X → Prop} {Ψ : Y → Prop} {Ω : Z → Prop}
    (hS : S.Sem Φ Ψ) (hT : T.Sem Ψ Ω) : (S.seq T).Sem Φ Ω := fun x hx => by
  refine doomed_join S.rds T.rds S.err T.err _ (hS.doomed x hx _ ?_ ?_ ?_)
  · intro a ha
    exact doomed_of_all _ _ _ fun b hp => absurd ((passT_joinT _ _ a b).1 hp).1 ha
  · intro a ha
    exact doomed_of_all _ _ _ fun b _ ho => absurd ((seq_ok S T x a b).1 ho).1 ha
  · intro a ha
    refine Doomed.mono _ _ (fun b hb hp ho => ?_) (hT _ ha)
    rw [seq_nx]
    exact hb ((passT_joinT _ _ a b).1 hp).2 ((seq_ok S T x a b).1 ho).2

/-- n steps in a row, with a claim Φ i on the state after i steps. -/
theorem Sem.iter : ∀ (n : ℕ) (X : ℕ → Type) (S : ∀ i, Step (X i) (X (i + 1)))
    (Φ : ∀ i, X i → Prop), (∀ i, i < n → (S i).Sem (Φ i) (Φ (i + 1))) →
    (Step.iter n X S).Sem (Φ 0) (Φ n)
  | 0, _, _, _, _ => Sem.nil
  | n + 1, X, S, Φ, h =>
    (h 0 (Nat.succ_pos n)).seq
      (Sem.iter n (fun i => X (i + 1)) (fun i => S (i + 1)) (fun i => Φ (i + 1)) fun i hi =>
        h (i + 1) (Nat.succ_lt_succ hi))

/-- A step for each member of a list, with a claim that may depend on the members still to come. -/
theorem Sem.many {S : A → Step X X} (Φ : List A → X → Prop) : ∀ l : List A,
    (∀ a l', (a :: l') <:+ l → (S a).Sem (Φ (a :: l')) (Φ l')) → (Step.many S l).Sem (Φ l) (Φ [])
  | [], _ => Sem.nil
  | a :: l, h =>
    (h a l (List.suffix_refl _)).seq
      (Sem.many Φ l fun a' l' hs => h a' l' (hs.trans (List.suffix_cons a l)))

/-- A step on small states, used on large ones. For each large state of which Φ is false there are
claims φ, φ' on small states for which the step's statement holds: φ is false of the small state
taken out, and Φ' of the large state after the step gives φ' of the small one. -/
theorem Sem.lens {S : Step A A'} {get : X → A} {put : X → A' → X'} {Φ : X → Prop}
    {Φ' : X' → Prop}
    (h : ∀ x, ¬ Φ x → ∃ (φ : A → Prop) (φ' : A' → Prop), S.Sem φ φ' ∧ ¬ φ (get x) ∧
      ∀ a', Φ' (put x a') → φ' a') : (S.lens get put).Sem Φ Φ' := fun x hx => by
  obtain ⟨φ, φ', hS, h1, h2⟩ := h x hx
  exact Doomed.mono _ _ (fun τ hτ hp ho hn => hτ hp ho (h2 _ hn)) (hS _ h1)

/-- The same with one pair of claims for all large states. -/
theorem Sem.lens_of {S : Step A A'} {get : X → A} {put : X → A' → X'} {φ : A → Prop}
    {φ' : A' → Prop} {Φ' : X' → Prop} (h : S.Sem φ φ') (h2 : ∀ x a', Φ' (put x a') → φ' a') :
    (S.lens get put).Sem (fun x => φ (get x)) Φ' :=
  Sem.lens fun x hx => ⟨φ, φ', h, hx, h2 x⟩

/-! ### Facts that are true all along -/

/-- A fact passes the step: if I holds of the state before it, I' holds of the state after it,
whatever is sent and drawn. Meant for what does not depend on the prover, such as the length of a
list in the state. -/
def Keeps (S : Step X X') (I : X → Prop) (I' : X' → Prop) : Prop := ∀ x τ, I x → I' (S.nx x τ)

namespace Keeps

/-- A fact passes a step without rounds if it passes the step's map. -/
theorem pure {p : X → Prop} {f : X → X'} {I : X → Prop} {I' : X' → Prop}
    (h : ∀ x, I x → I' (f x)) : (Step.pure p f).Keeps I I' := fun x _ hx => h x hx

/-- A fact passes the empty step. -/
theorem nil {I : X → Prop} : (Step.nil : Step X X).Keeps I I := fun _ _ h => h

/-- A fact passes rounds that leave the state as it is. -/
theorem idle {ds : List PQ.RD} {ε : Err (uW ds)} {I : X → Prop} :
    (Step.idle ds ε : Step X X).Keeps I I := fun _ _ h => h

/-- A fact passes a step of one round if it passes the step's map, whatever is sent and drawn. -/
theorem one {d : PQ.RD} {e : ℕ} {p : X → (wRound d).Msg → (wRound d).Chal → Prop}
    {f : X → (wRound d).Msg → (wRound d).Chal → X'} {I : X → Prop} {I' : X' → Prop}
    (h : ∀ x m c, I x → I' (f x m c)) : (Step.one d e p f).Keeps I I' :=
  fun x τ hx => h x τ.1 τ.2.1 hx

/-- A fact passes one step after another. -/
theorem seq {S : Step X Y} {T : Step Y Z} {I : X → Prop} {J : Y → Prop} {L : Z → Prop}
    (hS : S.Keeps I J) (hT : T.Keeps J L) : (S.seq T).Keeps I L :=
  fun x _ hx => hT _ _ (hS x _ hx)

/-- A fact passes n steps in a row. -/
theorem iter : ∀ (n : ℕ) (X : ℕ → Type) (S : ∀ i, Step (X i) (X (i + 1))) (I : ∀ i, X i → Prop),
    (∀ i, i < n → (S i).Keeps (I i) (I (i + 1))) → (Step.iter n X S).Keeps (I 0) (I n)
  | 0, _, _, _, _ => nil
  | n + 1, X, S, I, h =>
    (h 0 (Nat.succ_pos n)).seq
      (iter n (fun i => X (i + 1)) (fun i => S (i + 1)) (fun i => I (i + 1)) fun i hi =>
        h (i + 1) (Nat.succ_lt_succ hi))

/-- A fact passes a step for each member of a list. It may depend on the members still to come. -/
theorem many {S : A → Step X X} (I : List A → X → Prop) : ∀ l : List A,
    (∀ a l', (a :: l') <:+ l → (S a).Keeps (I (a :: l')) (I l')) →
    (Step.many S l).Keeps (I l) (I [])
  | [], _ => nil
  | a :: l, h =>
    (h a l (List.suffix_refl _)).seq
      (many I l fun a' l' hs => h a' l' (hs.trans (List.suffix_cons a l)))

/-- A fact on large states passes a step on small states if it passes whatever is laid in. -/
theorem lens {S : Step A A'} {get : X → A} {put : X → A' → X'} {I : X → Prop} {I' : X' → Prop}
    (h : ∀ x a', I x → I' (put x a')) : (S.lens get put).Keeps I I' := fun x _ hx => h x _ hx

end Keeps

/-- A statement that was proved without a fact holds beside it. -/
theorem Sem.under {S : Step X X'} {Φ : X → Prop} {Φ' : X' → Prop} {I : X → Prop}
    {I' : X' → Prop} (h : S.Sem Φ Φ') (hI : S.Keeps I I') :
    S.Sem (fun x => I x → Φ x) fun x' => I' x' → Φ' x' :=
  Sem.inv hI (h.conseq (fun _ hx _ => hx) fun _ hx => hx)

/-- A family of claims at once, with the same error counts: if one of them is false before the step,
that one is false after it. -/
theorem Sem.all {ι : Sort _} {S : Step X X'} {P : ι → X → Prop} {P' : ι → X' → Prop}
    (h : ∀ i, S.Sem (P i) (P' i)) : S.Sem (fun x => ∀ i, P i x) fun x' => ∀ i, P' i x' :=
  fun x hx => by
  obtain ⟨i, hi⟩ := not_forall.1 hx
  exact Doomed.mono _ _ (fun _ hτ hp ho hn => hτ hp ho (hn i)) (h i x hi)

/-- A statement that asks F of the state before the step holds of the step that tests F. -/
theorem Sem.guard {S : Step X X'} {F Φ : X → Prop} {Φ' : X' → Prop}
    (h : S.Sem (fun x => F x → Φ x) Φ') : (S.guard F).Sem Φ Φ' := fun x hx => by
  by_cases hF : F x
  · exact Doomed.mono _ _ (fun τ hτ hp ho => hτ hp ho.2) (h x fun h' => hx (h' hF))
  · exact doomed_of_all _ _ _ fun τ _ ho => absurd ho.1 hF

/-- What a step has tested of the state before it may be assumed in the claim after it: I' follows
from the test, whatever is sent and drawn. -/
theorem Sem.guard_gives {S : Step X X'} {F Φ : X → Prop} {Φ' I' : X' → Prop}
    (h : (S.guard F).Sem Φ Φ') (hI : ∀ x τ, F x → I' (S.nx x τ)) :
    (S.guard F).Sem Φ fun x' => I' x' → Φ' x' := fun x hx =>
  Doomed.mono _ _ (fun τ hτ hp ho hn => hτ hp ho (hn (hI x τ ho.1))) (h x hx)

/-- A fact passes a step with one more test as it passes the step. -/
theorem Keeps.guard {S : Step X X'} {F : X → Prop} {I : X → Prop} {I' : X' → Prop}
    (h : S.Keeps I I') : (S.guard F).Keeps I I' := h

/-! ### The form with rounds behind -/

/-- The step's statement in the form that leaves open what follows: t are any rounds behind the
step's. The blocks' statements of OnBytes/Slice/ChainSem.lean have this form. -/
def SemT (S : Step X X') (Φ : X → Prop) (Φ' : X' → Prop) : Prop :=
  ∀ x, ¬ Φ x → ∀ (t : Shape) (εt : Err t) (bad : Tr (uW S.rds ++ t) → Prop),
    (∀ a b, ¬ passT S.rds a → bad (Tr.app a b)) → (∀ a b, ¬ S.ok x a → bad (Tr.app a b)) →
    (∀ a, ¬ Φ' (S.nx x a) → Doomed t εt fun b => bad (Tr.app a b)) →
    Doomed (uW S.rds ++ t) (Err.app S.err εt) bad

/-- The statement gives the form with rounds behind. -/
theorem Sem.toT {S : Step X X'} {Φ : X → Prop} {Φ' : X' → Prop} (h : S.Sem Φ Φ') :
    S.SemT Φ Φ' := fun x hx t εt bad hp ho hn =>
  Doomed.append _ t S.err εt bad (h.doomed x hx _
    (fun a ha => doomed_of_all _ _ _ fun b => hp a b ha)
    (fun a ha => doomed_of_all _ _ _ fun b => ho a b ha) hn)

/-- The form with rounds behind gives the statement: no rounds behind. -/
theorem Sem.ofT {S : Step X X'} {Φ : X → Prop} {Φ' : X' → Prop} (h : S.SemT Φ Φ') :
    S.Sem Φ Φ' := fun x hx => by
  have h1 := h x hx [] ()
    (fun τ => passT S.rds (Tr.fst τ) → S.ok x (Tr.fst τ) → ¬ Φ' (S.nx x (Tr.fst τ)))
    (fun a b ha hp => absurd (by rwa [Tr.fst_app] at hp) ha)
    (fun a b ha _ ho => absurd (by rwa [Tr.fst_app] at ho) ha)
    (fun a ha => by
      show _ → _ → ¬ Φ' (S.nx x (Tr.fst (Tr.app (t := []) a ())))
      rw [Tr.fst_app]
      exact fun _ _ => ha)
  refine Doomed.mono _ _ (fun a ha => ?_) (doomed_app_nil _ _ _ h1)
  rwa [Tr.fst_app] at ha

/-- One step after another, in the form with rounds behind. -/
theorem SemT.seq {S : Step X Y} {T : Step Y Z} {Φ : X → Prop} {Ψ : Y → Prop} {Ω : Z → Prop}
    (hS : S.SemT Φ Ψ) (hT : T.SemT Ψ Ω) : (S.seq T).SemT Φ Ω :=
  Sem.toT (Sem.seq (Sem.ofT hS) (Sem.ofT hT))

end Step

end OnBytes.Slice
