-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowLit.lean: the proofs that each of the two forms of round-by-round knowledge soundness of
Ior/Know.lean gives the other, with the same errors; from the working form: for at least one round.

What a reduction is, and what "the prover has lost" means: the head of Ior/Know.lean.

Main names:
  `know_of_literal` proves `Spec.know_of_literal` (Ior/Know.lean). A knowledge state function with
    its three laws, one extractor a round and the count of each round give the working form
    (`Reduction.Know`) with the same error list; the extractor of the working form is got by
    composing the rounds' extractors backwards, the last round's first. The proof is one induction
    on the shape (`doomed_of_kstate`).
  `literal_of_know` proves `Spec.literal_of_know` (Ior/Know.lean). The working form gives the form
    with a knowledge state function (`HasRbrKnowledge`) for a protocol with at least one round, with
    the same error list, the relations read on the sum of the two types of witnesses (`onLeft`,
    `onRight`), the round extractors made from the extractor (`RExt.ofFull`). The state function is
    named (`kSt`): before the last verifier message only witnesses of the input relation (`.inl`:
    valid or not) are in state 1, after it only witnesses of the output relation.
  `know_iff_literal` proves `Spec.know_iff_literal` (stated here). The round trip: for one extractor
    on full transcripts and at least one round the two forms are equivalent, with the same errors;
    see its docstring.

Limits: this file says nothing on running times or queries. The state function of the second
direction is defined with classical logic (it asks whether the prover has lost); it is no algorithm.
In the first direction only one half of the law for the empty transcript and one half of the law for
full transcripts are used.
Terms: lean/GLOSSARY.md.
-/
import Ior.Know

set_option autoImplicit false

namespace Iop
open Prob

/-! ## 1. From the form with a knowledge state function to the working form -/

/-- The induction. If state 1 at the empty transcript gives G, no prover message leads from state 0
to state 1, and in each round at most the allowed number of verifier messages have a witness in
state 1 whose extraction was in state 0, then the prover has lost at the start towards "every
witness in state 1 at the end is extracted into G". -/
theorem doomed_of_kstate {S : Type} :
    ∀ (s : Shape) (ε : Err s) (St : PTr s → S → Bool) (Ex : RExt S s) (G : S → Prop),
      (∀ x, St (PTr.empty s) x = true → G x) →
      (∀ (τ : AtP s) (m : τ.round.Msg) x, St (.atP τ) x = false → St (.atV (τ.snoc m)) x = false) →
      (∀ τ : AtV s,
        cnt (fun c : τ.round.Chal =>
            ∃ x, St (.atV τ) (Ex.at τ c x) = false ∧ St (τ.snoc c) x = true) ≤ τ.err ε) →
      Doomed s ε (fun τ => ∀ x, St (.full τ) x = true → G (Ex.back τ x))
  | [], _, _, _, _, hE, _, _ => fun x hx => hE x hx
  | _ :: s, (_, ε), St, (e, k), G, hE, hP, hV => fun m =>
      le_trans (cnt_mono fun c hc => by
        by_contra hno
        refine hc (doomed_of_kstate s ε (fun t => St (PTr.cons m c t)) (k m c)
            (fun x => G (e m c x)) ?_ ?_ ?_)
        · intro x hx
          apply hE
          by_contra h0
          exact hno ⟨x, hP (Sum.inl ()) m (e m c x) (Bool.eq_false_of_not_eq_true h0), hx⟩
        · intro τ m' x h
          exact hP (Sum.inr (m, c, τ)) m' x h
        · intro τ
          exact hV (Sum.inr (m, c, τ))) (hV (Sum.inl m))

theorem know_of_literal : Spec.know_of_literal := by
  intro A B S K on RA RB Ex ε ⟨St, h⟩ a ha
  obtain ⟨hK, hV⟩ := h a ha
  refine Doomed.mono _ _ ?_
    (doomed_of_kstate K.shape ε (St a) (Ex a) (RA a) (fun x hx => (hK.empty x).1 hx) hK.prover hV)
  intro τ hτ b w hb hw
  exact hτ w ((hK.full τ w).2 ⟨b, hb, hw⟩)

/-! ## 2. From the working form to the form with a knowledge state function

The statement is fixed and does not appear: P is "a valid witness of the input statement", Q τ w is
"after τ the verifier outputs a statement of which w is a valid witness", e is the extractor on full
transcripts. -/

section Back
variable {WA WB : Type}

/-- The target of the working form. -/
def kBad {s : Shape} (P : WA → Prop) (Q : Tr s → WB → Prop) (e : Tr s → WB → WA) : Tr s → Prop :=
  fun τ => ∀ w, Q τ w → P (e τ w)

/-- The knowledge state function (as a proposition; "holds" is state 1). -/
def kSt (s : Shape) (ε : Err s) (P : WA → Prop) (Q : Tr s → WB → Prop) (e : Tr s → WB → WA) :
    PTr s → WA ⊕ WB → Prop
  | .atP τ, .inl w => P w ∨ ¬ Lost s ε (kBad P Q e) (.atP τ)
  | .atV τ, .inl w => P w ∨ ¬ Lost s ε (kBad P Q e) (.atV τ)
  | .full _, .inl _ => False
  | .atP _, .inr _ => False
  | .atV _, .inr _ => False
  | .full τ, .inr w => Q τ w

/-- After a first round (m, c) it is the state function of the remaining rounds. -/
theorem kSt_cons {r : Round} {s : Shape} (e₀ : ℕ) (ε : Err s) (P : WA → Prop)
    (Q : Tr (r :: s) → WB → Prop) (e : Tr (r :: s) → WB → WA) (m : r.Msg) (c : r.Chal) :
    ∀ (t : PTr s) (x : WA ⊕ WB),
      kSt (r :: s) (e₀, ε) P Q e (PTr.cons m c t) x ↔
      kSt s ε P (fun τ => Q (m, c, τ)) (fun τ => e (m, c, τ)) t x
  | .atP _, .inl _ => Iff.rfl
  | .atV _, .inl _ => Iff.rfl
  | .full _, .inl _ => Iff.rfl
  | .atP _, .inr _ => Iff.rfl
  | .atV _, .inr _ => Iff.rfl
  | .full _, .inr _ => Iff.rfl

/-- The law for the empty transcript: this is where the working form itself is used. -/
theorem kSt_empty :
    ∀ (s : Shape) (ε : Err s) (P : WA → Prop) (Q : Tr s → WB → Prop) (e : Tr s → WB → WA), s ≠ [] →
      Doomed s ε (kBad P Q e) → ∀ x, kSt s ε P Q e (PTr.empty s) x ↔ Sum.elim P (fun _ => False) x
  | [], _, _, _, _, h, _, _ => absurd rfl h
  | _ :: _, (_, _), _, _, _, _, hD, .inl _ => ⟨fun h => h.elim id fun hn => absurd hD hn, Or.inl⟩
  | _ :: _, (_, _), _, _, _, _, _, .inr _ => Iff.rfl

/-- The law for prover moves. -/
theorem kSt_prover (s : Shape) (ε : Err s) (P : WA → Prop) (Q : Tr s → WB → Prop)
    (e : Tr s → WB → WA) (τ : AtP s) (m : τ.round.Msg) :
    ∀ x, ¬ kSt s ε P Q e (.atP τ) x → ¬ kSt s ε P Q e (.atV (τ.snoc m)) x
  | .inl _, h0, h1 =>
    h1.elim (fun p => h0 (Or.inl p)) fun hn => h0 (Or.inr fun hl => hn (Lost.prover s ε _ τ m hl))
  | .inr _, _, h1 => h1

/-- One verifier message. If some witness is in state 1 after it while its extraction was in state 0
before it, then the prover had lost before it and has not lost after it. -/
theorem kSt_step :
    ∀ (s : Shape) (ε : Err s) (P : WA → Prop) (Q : Tr s → WB → Prop) (e : Tr s → WB → WA)
        (τ : AtV s) (c : τ.round.Chal) (x : WA ⊕ WB),
      ¬ kSt s ε P Q e (.atV τ) ((RExt.ofFull s e).at τ c x) → kSt s ε P Q e (τ.snoc c) x →
      Lost s ε (kBad P Q e) (.atV τ) ∧ ¬ Lost s ε (kBad P Q e) (τ.snoc c)
  | [_], (_, _), _, _, _, .inl _, _, .inl _, _, h1 => False.elim h1
  | [_], (_, _), _, _, _, .inl _, _, .inr w, h0, h1 =>
    ⟨by_contra fun h => h0 (Or.inr h), fun hl => h0 (Or.inl (hl w h1))⟩
  | [_], (_, _), _, _, _, .inr (_, _, τ), _, _, _, _ => Empty.elim τ
  | _ :: _ :: _, (_, _), _, _, _, .inl _, _, .inl _, h0, h1 =>
      ⟨by_contra fun h => h0 (Or.inr h),
        fun hl => h1.elim (fun hp => h0 (Or.inl hp)) fun hn => hn hl⟩
  | _ :: _ :: _, (_, _), _, _, _, .inl _, _, .inr _, _, h1 => False.elim h1
  | _ :: r' :: s, (e₀, ε), P, Q, e, .inr (m, c', τ), c, x, h0, h1 =>
      have h := kSt_step (r' :: s) ε P (fun t => Q (m, c', t)) (fun t => e (m, c', t)) τ c x
        (fun h => h0 ((kSt_cons e₀ ε P Q e m c' (.atV τ) _).2 h))
        ((kSt_cons e₀ ε P Q e m c' (τ.snoc c) x).1 h1)
      ⟨h.1, fun hl => h.2 ((lost_cons e₀ ε (kBad P Q e) m c' (τ.snoc c)).1 hl)⟩

/-- The count of a round. -/
theorem kSt_count (s : Shape) (ε : Err s) (P : WA → Prop) (Q : Tr s → WB → Prop)
    (e : Tr s → WB → WA) (τ : AtV s) :
    cnt (fun c : τ.round.Chal =>
        ∃ x, ¬ kSt s ε P Q e (.atV τ) ((RExt.ofFull s e).at τ c x) ∧ kSt s ε P Q e (τ.snoc c) x) ≤
      τ.err ε := by
  by_cases hL : Lost s ε (kBad P Q e) (.atV τ)
  · exact le_trans (cnt_mono fun c ⟨x, h0, h1⟩ => (kSt_step s ε P Q e τ c x h0 h1).2)
      (Lost.verifier s ε _ τ hL)
  · rw [cnt_false fun c ⟨x, h0, h1⟩ => hL (kSt_step s ε P Q e τ c x h0 h1).1]
    exact Nat.zero_le _

/-- For a shape with at least one round, all round extractors made from one extractor on full
transcripts, applied in turn to a witness of the output relation, give what that extractor gives. -/
theorem RExt.back_ofFull :
    ∀ (s : Shape), s ≠ [] →
      ∀ (e : Tr s → WB → WA) (τ : Tr s) (w : WB), (RExt.ofFull s e).back τ (.inr w) = .inl (e τ w)
  | [], h, _, _, _ => absurd rfl h
  | [_], _, _, (_, _, ()), _ => rfl
  | _ :: r' :: s, _, e, (m, c, τ), w =>
    RExt.back_ofFull (r' :: s) (List.cons_ne_nil _ _) (fun t => e (m, c, t)) τ w

end Back

open Classical in
theorem literal_of_know : Spec.literal_of_know := by
  intro A B WA WB K on RA RB ext ε hne h
  refine ⟨fun a t x =>
      decide (kSt K.shape ε (RA a) (fun τ w => ∃ b, K.out a τ = some b ∧ RB b w) (ext a) t x),
    fun a ha => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro x
    rw [decide_eq_true_iff,
      kSt_empty K.shape ε _ _ _ hne
        (Doomed.mono _ _ (fun τ hτ w ⟨b, hb, hw⟩ => hτ b w hb hw) (h a ha))]
    cases x <;> exact Iff.rfl
  · intro τ m x h0
    rw [decide_eq_false_iff_not] at h0 ⊢
    exact kSt_prover K.shape ε _ _ _ τ m x h0
  · intro τ x
    rw [decide_eq_true_iff]
    cases x with
    | inl w => exact ⟨False.elim, fun ⟨_, _, hf⟩ => hf⟩
    | inr w => exact Iff.rfl
  · intro τ
    simp only [decide_eq_true_iff, decide_eq_false_iff_not]
    exact kSt_count K.shape ε _ _ _ τ

namespace Spec
open Reduction

/-- States: the two forms are equivalent: at least one round, one extractor on full transcripts; the
relations read on the sum (`onLeft`, `onRight`), the round extractors made from that extractor
(`RExt.ofFull`), same errors. -/
def know_iff_literal : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    K.shape ≠ [] →
    (K.Know on RA RB ext ε ↔
      K.HasRbrKnowledge on (onLeft (WB := WB) RA) (onRight (WA := WA) RB)
        (fun a => RExt.ofFull K.shape (ext a)) ε)

end Spec

theorem know_iff_literal : Spec.know_iff_literal := by
  intro A B WA WB K on RA RB ext ε hne
  refine ⟨literal_of_know A B WA WB K on RA RB ext ε hne, fun h a ha => ?_⟩
  refine Doomed.mono _ _ ?_ (know_of_literal A B (WA ⊕ WB) K on _ _ _ ε h a ha)
  intro τ hτ b w hb hw
  have h1 : onLeft RA a ((RExt.ofFull K.shape (ext a)).back τ (.inr w)) := hτ b (.inr w) hb hw
  rw [RExt.back_ofFull K.shape hne] at h1
  exact h1

end Iop
