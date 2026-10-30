-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeySound.lean: three chains of steps, joined over four seams, give the soundness of
the protocol in three stretches.

OnBytes/Slice/Plain3.lean makes a protocol from three lists of written rounds, four seams (rounds in
which nothing is drawn and which the decision does not look at) and any decision on three views.
OnBytes/Slice/KeyStep.lean has steps, each with its list of rounds. This file takes the protocol at
the lists of three steps. The state after the first step is the state before the second, and so on;
so what a later chain needs of an earlier one crosses a seam as a value.

The shape of that protocol is, by definition, the seams and the three steps' shapes joined. So there
is no cast in this file. In `sound3_at`, where the lists of rounds are given from elsewhere, the
equations are used once, by substitution.

Main definitions.
 `Acc3`     the yes in the field of three steps in a row, on their three transcripts.
 `err3`     the error counts: the three steps', and 0 at each seam.
 `with3`    the data of a protocol in three stretches, with the three lists of rounds laid in.
Main theorems.
 `doomed_round`   a round after which the prover has lost whatever is sent and drawn.
 `doomed3`        if the three steps' statements hold in a row and end at `True`, then from a state
                  of which the first claim is false the prover has lost, towards any predicate that
                  holds wherever a test of work or the yes in the field fails.
 `sound3`         round-by-round soundness of the protocol in three stretches, for any language
                  outside of which the first claim is false, and any decision whose yes gives the
                  yes in the field.
 `sound3_at`      the same at three lists of rounds that are given from elsewhere and are equal to
                  the steps' lists.
Not claimed. That any decision's yes gives the yes in the field. That any step's statement holds.
Nothing on the sizes of the error counts.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyStep
import OnBytes.Slice.Plain3Views

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- A round after which the prover has lost, whatever is sent and drawn, costs nothing. -/
theorem doomed_round (r : Round) (e : ℕ) (s : Shape) (ε : Err s) (bad : Tr (r :: s) → Prop)
    (h : ∀ m c, Doomed s ε fun τ => bad (m, c, τ)) : Doomed (r :: s) (e, ε) bad := fun m =>
  le_trans (le_of_eq (cnt_false fun c hc => hc (h m c))) (Nat.zero_le _)

section
variable {X0 X1 X2 X3 : Type} (K1 : Step X0 X1) (K2 : Step X1 X2) (K3 : Step X2 X3)

/-- The yes in the field of three steps in a row: each step's test, at the state that the steps
before it have made. -/
def Acc3 (x : X0) (τ₁ : Tr (uW K1.rds)) (τ₂ : Tr (uW K2.rds)) (τ₃ : Tr (uW K3.rds)) : Prop :=
  K1.ok x τ₁ ∧ K2.ok (K1.nx x τ₁) τ₂ ∧ K3.ok (K2.nx (K1.nx x τ₁) τ₂) τ₃

/-- The shape: a seam, the first step's rounds, two seams, the second step's, a seam, the third
step's. -/
abbrev sh3 (r0 r1 r2 r3 : Round) : Shape :=
  r0 :: (uW K1.rds ++ (r1 :: r2 :: (uW K2.rds ++ (r3 :: uW K3.rds))))

/-- The error counts: the three steps', and 0 at each seam. -/
def err3 (r0 r1 r2 r3 : Round) : Err (sh3 K1 K2 K3 r0 r1 r2 r3) :=
  (0, Err.app K1.err (0, 0, Err.app K2.err (0, K3.err)))

variable {K1 K2 K3}

/-- Three steps over four seams. -/
theorem doomed3 {Φ0 : X0 → Prop} {Φ1 : X1 → Prop} {Φ2 : X2 → Prop} (h1 : K1.Sem Φ0 Φ1)
    (h2 : K2.Sem Φ1 Φ2) (h3 : K3.Sem Φ2 fun _ => True) (r0 r1 r2 r3 : Round) (x : X0)
    (hx : ¬ Φ0 x) (bad : Tr (sh3 K1 K2 K3 r0 r1 r2 r3) → Prop)
    (hb : ∀ m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃,
      ¬ (passT K1.rds τ₁ ∧ passT K2.rds τ₂ ∧ passT K3.rds τ₃ ∧ Acc3 K1 K2 K3 x τ₁ τ₂ τ₃) →
      bad (m0, c0, Tr.app τ₁ (m1, c1, m2, c2, Tr.app τ₂ (m3, c3, τ₃)))) :
    Doomed (sh3 K1 K2 K3 r0 r1 r2 r3) (err3 K1 K2 K3 r0 r1 r2 r3) bad := by
  refine doomed_round r0 0 _ _ _ fun m0 c0 => ?_
  have t1 : ∀ τ₁ : Tr (uW K1.rds), ¬ (passT K1.rds τ₁ ∧ K1.ok x τ₁) →
      ∀ b : Tr (r1 :: r2 :: (uW K2.rds ++ (r3 :: uW K3.rds))), bad (m0, c0, Tr.app τ₁ b) := by
    intro τ₁ h b
    obtain ⟨m1, c1, m2, c2, b⟩ := b
    obtain ⟨τ₂, b, rfl⟩ := exists_app (s := uW K2.rds) b
    obtain ⟨m3, c3, τ₃⟩ := b
    exact hb _ _ _ _ _ _ _ _ _ _ _ fun hh => h ⟨hh.1, hh.2.2.2.1⟩
  refine Doomed.append (uW K1.rds) _ K1.err _ _ (h1.doomed x hx _
    (fun τ₁ hp => doomed_of_all _ _ _ (t1 τ₁ fun h => hp h.1))
    (fun τ₁ ho => doomed_of_all _ _ _ (t1 τ₁ fun h => ho h.2)) fun τ₁ hn1 => ?_)
  refine doomed_round r1 0 _ _ _ fun m1 c1 => doomed_round r2 0 _ _ _ fun m2 c2 => ?_
  have t2 : ∀ τ₂ : Tr (uW K2.rds), ¬ (passT K2.rds τ₂ ∧ K2.ok (K1.nx x τ₁) τ₂) →
      ∀ b : Tr (r3 :: uW K3.rds),
        bad (m0, c0, Tr.app τ₁ (m1, c1, m2, c2, Tr.app τ₂ b)) := by
    intro τ₂ h b
    obtain ⟨m3, c3, τ₃⟩ := b
    exact hb _ _ _ _ _ _ _ _ _ _ _ fun hh => h ⟨hh.2.1, hh.2.2.2.2.1⟩
  refine Doomed.append (uW K2.rds) _ K2.err _ _ (h2.doomed _ hn1 _
    (fun τ₂ hp => doomed_of_all _ _ _ (t2 τ₂ fun h => hp h.1))
    (fun τ₂ ho => doomed_of_all _ _ _ (t2 τ₂ fun h => ho h.2)) fun τ₂ hn2 => ?_)
  refine doomed_round r3 0 _ _ _ fun m3 c3 => ?_
  exact Doomed.mono _ _
    (fun τ₃ h => hb _ _ _ _ _ _ _ _ _ _ _ fun hh => h ⟨hh.2.2.1, hh.2.2.2.2.2⟩) (h3.final _ hn2)

end

/-- The data of a protocol in three stretches, with three lists of rounds laid in. -/
@[reducible] def with3 (G : Stretches) (a b c : List PQ.RD) : Stretches :=
  { G with C := ckP .two, ds₁ := a, ds₂ := b, ds₃ := c }

/-- The protocol in three stretches is sound. G holds the seams, the stored table's size
and openings and the keys. The protocol is taken at the rounds of three steps whose statements hold
in a row, from Φ0 to `True`. x₀ makes the first state of the stored table. Lg is any language
outside of which the first claim is false. dec is any decision such that a yes of the protocol gives
the yes in the field. -/
theorem sound3 (G : Stretches) {X0 X1 X2 X3 : Type} {K1 : Step X0 X1} {K2 : Step X1 X2}
    {K3 : Step X2 X3} {Φ0 : X0 → Prop} {Φ1 : X1 → Prop} {Φ2 : X2 → Prop} (h1 : K1.Sem Φ0 Φ1)
    (h2 : K2.Sem Φ1 Φ2) (h3 : K3.Sem Φ2 fun _ => True) (x₀ : (Fin (2 ^ G.a) → PQ.SgX) → X0)
    (Lg : Unit → (Fin (2 ^ G.a) → PQ.SgX) → Prop) (hL : ∀ y, ¬ Lg () y → ¬ Φ0 (x₀ y))
    (dec : PQ.View → PQ.View → PQ.View → Bool)
    (hsem : ∀ y τ₁ τ₂ τ₃, (with3 G K1.rds K2.rds K3.rds).accOn y τ₁ τ₂ τ₃ dec = true →
      Acc3 K1 K2 K3 (x₀ y) τ₁ τ₂ τ₃) :
    (Plain3 (with3 G K1.rds K2.rds K3.rds) dec).Sound Lg
      (err3 K1 K2 K3 G.s0.r G.s1.r G.s2.r G.s3.r) := by
  intro u y hy
  cases u
  refine doomed3 h1 h2 h3 _ _ _ _ (x₀ y) (hL y hy) _ ?_
  intro m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃ hn
  refine Bool.eq_false_iff.2 fun ha => hn ?_
  have ha' := ((with3 G K1.rds K2.rds K3.rds).accept_whole dec y m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3
    τ₃).symm.trans ha
  have hp := (with3 G K1.rds K2.rds K3.rds).accOn_true dec y τ₁ τ₂ τ₃ ha'
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hsem y τ₁ τ₂ τ₃ ha'⟩

/-- The same at lists of rounds that are given from elsewhere. G holds three lists of rounds,
say those of a description of a program's run. Asked of G: its three lists are the three steps'
lists, and its types of verifier messages are those of all written rounds here. What is asked of the
decision speaks of the steps' lists. The error counts are those of `sound3`, carried along the
equations; what is said of them here is that they are all at most c as probabilities, if those of
`sound3` are. -/
theorem sound3_at (G : Stretches) {X0 X1 X2 X3 : Type} {K1 : Step X0 X1} {K2 : Step X1 X2}
    {K3 : Step X2 X3} (hC : G.C = ckP .two) (e1 : G.ds₁ = K1.rds) (e2 : G.ds₂ = K2.rds)
    (e3 : G.ds₃ = K3.rds) {Φ0 : X0 → Prop} {Φ1 : X1 → Prop} {Φ2 : X2 → Prop}
    (h1 : K1.Sem Φ0 Φ1) (h2 : K2.Sem Φ1 Φ2) (h3 : K3.Sem Φ2 fun _ => True)
    (x₀ : (Fin (2 ^ G.a) → PQ.SgX) → X0) (Lg : Unit → (Fin (2 ^ G.a) → PQ.SgX) → Prop)
    (hL : ∀ y, ¬ Lg () y → ¬ Φ0 (x₀ y)) (dec : PQ.View → PQ.View → PQ.View → Bool)
    (hsem : ∀ y τ₁ τ₂ τ₃, (with3 G K1.rds K2.rds K3.rds).accOn y τ₁ τ₂ τ₃ dec = true →
      Acc3 K1 K2 K3 (x₀ y) τ₁ τ₂ τ₃) (c : ℝ≥0∞)
    (hb : Err.Below (err3 K1 K2 K3 G.s0.r G.s1.r G.s2.r G.s3.r) c) :
    ∃ εs, (Plain3 G dec).Sound Lg εs ∧ Err.Below εs c := by
  cases G
  dsimp only at hC e1 e2 e3
  subst hC e1 e2 e3
  exact ⟨_, sound3 _ h1 h2 h3 x₀ Lg hL dec hsem, hb⟩

end OnBytes.Slice
