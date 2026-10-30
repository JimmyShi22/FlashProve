-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Carry.lean: round-by-round soundness is carried from one protocol to another along
maps of messages.

Why. The library proves soundness for protocols whose messages are field elements and whose oracles
have one symbol at a position. The protocol that a file holds has machine words, columns of words
and hash blocks. This file has the one theorem that joins the two kinds. It holds for all shapes.

The setting. A shape is the library's list of a protocol's rounds (Iop/Shape.lean). A round's error
count is the number of verifier messages that may let a prover that has lost escape; "the prover has
lost towards a goal" is Iop/Rbr.lean's `Doomed` (OnBytes/Slice/README.md, "The vocabulary"). Two
shapes s (the written one) and s' (the one with a soundness theorem) have the same number of rounds.
For each round there are a map of prover messages from s to s' and a map of verifier messages from s
to s' that may be undefined at some values. Both may depend on all that was sent before. No map
needs to be injective or onto. What is asked:
 1. in each round at most w verifier messages of s go to one verifier message of s'
    (`Carry.Fib`; the numbers w, one for each round, are a list of the type `Err s`);
 2. a transcript that the written verifier accepts has an image, and the other verifier accepts
    the image. The converse is not asked;
 3. maps of statements and of external oracles such that a statement whose image is in the language
    of s' is in the language of s.
Then each error count of s' times w is an error count for s (`sound_carry`). As probabilities the
errors grow by at most a factor k if w * |Chal'| ≤ k * |Chal| in each round (`below_mulErr`).

What the freedom is for. A verifier message without an image stands for a test on the verifier
message that fails, such as a proof of work that is not met. A map of prover messages that depends
on the past can fill in what the written prover does not send because the verifier can compute it,
such as a coefficient of a round polynomial that follows from the running claim.

Main definitions: `Carry`, `Carry.tr`, `Carry.Fib`, `mulErr`, `Rate`.
Main theorems: `Carry.doomed`, `sound_carry`, `below_mulErr`.

Not claimed. Nothing is said of completeness or zero knowledge: they speak of an honest prover,
and a theorem about a verifier does not need them.
-/
import Prob.Count
import Iop.InteractiveOracleProof

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob
open scoped ENNReal

/-- Maps from a shape s to a shape s', round by round: the map of prover messages; the map of
verifier messages, which may look at the round's prover message and is `none` where it is
undefined; and the maps of the later rounds, which may depend on this round's two messages.
There is no such thing between shapes of different lengths. -/
def Carry : Shape → Shape → Type
  | [], [] => Unit
  | r :: s, r' :: s' =>
      (r.Msg → r'.Msg) × (r.Msg → r.Chal → Option r'.Chal) × (r.Msg → r.Chal → Carry s s')
  | [], _ :: _ => Empty
  | _ :: _, [] => Empty

namespace Carry

/-- The image of a full transcript. It is `none` if a verifier message has no image. -/
def tr : {s s' : Shape} → Carry s s' → Tr s → Option (Tr s')
  | [], [], _, _ => some ()
  | _ :: _, _ :: _, (fm, fc, k), (m, c, τ) =>
      (fc m c).bind fun c' => (tr (k m c) τ).map fun τ' => (fm m, c', τ')
  | [], _ :: _, F, _ => nomatch F
  | _ :: _, [], F, _ => nomatch F

/-- In each round at most w verifier messages go to one verifier message, whatever was sent
before. The list ws holds the numbers w. -/
def Fib : {s s' : Shape} → Carry s s' → Err s → Prop
  | [], [], _, _ => True
  | r :: _, r' :: _, (_, fc, k), (w, ws) =>
      (∀ (m : r.Msg) (c' : r'.Chal), cnt (fun c => fc m c = some c') ≤ w) ∧ ∀ m c, Fib (k m c) ws
  | [], _ :: _, _, _ => True
  | _ :: _, [], _, _ => True

/-- The image of a transcript, one round unfolded. -/
theorem tr_cons {r r' : Round} {s s' : Shape} (fm : r.Msg → r'.Msg)
    (fc : r.Msg → r.Chal → Option r'.Chal) (k : r.Msg → r.Chal → Carry s s') (m : r.Msg)
    (c : r.Chal) (τ : Tr s) :
    tr (s := r :: s) (s' := r' :: s') (fm, fc, k) (m, c, τ) =
      (fc m c).bind fun c' => (tr (k m c) τ).map fun τ' => (fm m, c', τ') := rfl

end Carry

/-- The error counts for s that follow from error counts for s': each is multiplied by the
number w of its round. (Where s is longer than s' the count is 0; no `Carry` exists there.) -/
def mulErr : (s s' : Shape) → Err s → Err s' → Err s
  | [], _, _, _ => ()
  | _ :: s, [], (_, ws), _ => (0, mulErr s [] ws ())
  | _ :: s, _ :: s', (w, ws), (e, ε) => (e * w, mulErr s s' ws ε)

/-- In each round w * |Chal'| ≤ k * |Chal|: a value of the image is at most k times as likely as
under the uniform law. -/
def Rate : (s s' : Shape) → Err s → ℝ≥0∞ → Prop
  | [], _, _, _ => True
  | _ :: _, [], _, _ => True
  | r :: s, r' :: s', (w, ws), k =>
      (w : ℝ≥0∞) * (Fintype.card r'.Chal : ℝ≥0∞) ≤ k * (Fintype.card r.Chal : ℝ≥0∞) ∧
        Rate s s' ws k

/-- If the goal holds of every transcript, the prover has lost towards it, with any error counts. -/
theorem doomed_of_all : ∀ (s : Shape) (ε : Err s) (bad : Tr s → Prop), (∀ τ, bad τ) → Doomed s ε bad
  | [], _, _, h => h ()
  | _ :: s, (_, ε), _, h => fun m =>
      le_trans (le_of_eq (cnt_false fun c hc => hc (doomed_of_all s ε _ fun τ => h (m, c, τ))))
        (Nat.zero_le _)

/-- If at most w elements go to one value, then a set of values has at most w times as many
elements that go into it. Elements without a value are not counted. -/
theorem cnt_some_le {U K : Type} [Fintype U] [Fintype K] (φ : U → Option K) {w : ℕ}
    (hw : ∀ c, cnt (fun a => φ a = some c) ≤ w) (P : K → Prop) :
    cnt (fun a => ∃ c, φ a = some c ∧ P c) ≤ cnt P * w := by
  classical
  have h1 : cnt (fun a => ∃ c, φ a = some c ∧ P c)
      ≤ cnt (fun a => ∃ c ∈ Finset.univ.filter P, φ a = some c) :=
    cnt_mono fun _ ⟨c, hc, hP⟩ => ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ c, hP⟩, hc⟩
  have h2 : cnt (fun a => ∃ c ∈ Finset.univ.filter P, φ a = some c)
      ≤ ∑ c ∈ Finset.univ.filter P, cnt (fun a => φ a = some c) :=
    cnt_exists_mem_le (Finset.univ.filter P) (fun c a => φ a = some c)
  have h3 : ∑ c ∈ Finset.univ.filter P, cnt (fun a => φ a = some c)
      ≤ ∑ _c ∈ Finset.univ.filter P, w := Finset.sum_le_sum fun c _ => hw c
  have h4 : (Finset.univ.filter P).card = cnt P := (cnt_eq_card_filter P).symm
  rw [Finset.sum_const, smul_eq_mul, h4] at h3
  exact h1.trans (h2.trans h3)

/-- **The prover's loss is carried back.** Let the prover have lost in s' towards the goal bad'.
Let the goal bad hold of every transcript of s without an image, and of every transcript whose
image is in bad'. Then the prover has lost in s towards bad, with each error count times w. -/
theorem Carry.doomed : ∀ {s s' : Shape} (F : Carry s s') (ws : Err s), F.Fib ws → ∀ (ε : Err s')
    (bad : Tr s → Prop) (bad' : Tr s' → Prop), (∀ τ, F.tr τ = none → bad τ) →
    (∀ τ τ', F.tr τ = some τ' → bad' τ' → bad τ) → Doomed s' ε bad' →
    Doomed s (mulErr s s' ws ε) bad
  | [], [], _, _, _, _, _, _, _, h, hd => h () () rfl hd
  | r :: s, r' :: s', (fm, fc, k), (w, ws), hF, (e, ε), bad, bad', h0, h, hd => fun m => by
      show cnt (fun c : r.Chal => ¬ Doomed s (mulErr s s' ws ε) (fun τ => bad (m, c, τ))) ≤ e * w
      have key : ∀ c : r.Chal, ¬ Doomed s (mulErr s s' ws ε) (fun τ => bad (m, c, τ)) →
          ∃ c', fc m c = some c' ∧ ¬ Doomed s' ε (fun τ' => bad' (fm m, c', τ')) := by
        intro c hc
        cases hfc : fc m c with
        | none =>
          refine absurd (doomed_of_all s _ _ fun τ => h0 (m, c, τ) ?_) hc
          rw [Carry.tr_cons, hfc]
          rfl
        | some c' =>
          refine ⟨c', rfl, fun hd' => hc ?_⟩
          refine Carry.doomed (k m c) ws (hF.2 m c) ε _ _ ?_ ?_ hd'
          · intro τ hτ
            refine h0 (m, c, τ) ?_
            rw [Carry.tr_cons, hfc, hτ]
            rfl
          · intro τ τ' hτ hb
            refine h (m, c, τ) (fm m, c', τ') ?_ hb
            rw [Carry.tr_cons, hfc, hτ]
            rfl
      exact (cnt_mono key).trans
        ((cnt_some_le (fc m) (hF.1 m) _).trans (Nat.mul_le_mul_right w (hd (fm m))))
  | [], _ :: _, F, _, _, _, _, _, _, _, _ => nomatch F
  | _ :: _, [], F, _, _, _, _, _, _, _, _ => nomatch F

/-- **Round-by-round soundness is carried along a change of types.** Q is the written protocol, Q'
the one with a soundness theorem. fx and fy translate statements and external oracles; the maps F
may depend on both.
hL: a statement whose translation is in the language L' is in the language L.
hacc: what Q accepts has an image that Q' accepts. -/
theorem sound_carry {X X' : Type} {E E' : ExtSpec} (Q : InteractiveOracleProof X E) (Q' : InteractiveOracleProof X' E')
    (F : X → E.Str → Carry Q.shape Q'.shape) (ws : Err Q.shape) (hF : ∀ x y, (F x y).Fib ws)
    (fx : X → X') (fy : E.Str → E'.Str)
    (L : X → E.Str → Prop) (L' : X' → E'.Str → Prop) (ε : Err Q'.shape)
    (hL : ∀ x y, L' (fx x) (fy y) → L x y)
    (hacc : ∀ x y τ, Q.accept x y τ = true →
      ∃ τ', (F x y).tr τ = some τ' ∧ Q'.accept (fx x) (fy y) τ' = true)
    (h : Q'.Sound L' ε) : Q.Sound L (mulErr Q.shape Q'.shape ws ε) := fun x y hn =>
  Carry.doomed (F x y) ws (hF x y) ε (fun τ => Q.accept x y τ = false)
    (fun τ' => Q'.accept (fx x) (fy y) τ' = false)
    (fun τ hτ => by
      show Q.accept x y τ = false
      cases ha : Q.accept x y τ with
      | false => rfl
      | true =>
        obtain ⟨τ', h1, _⟩ := hacc x y τ ha
        rw [hτ] at h1
        cases h1)
    (fun τ τ' hτ hb => by
      show Q.accept x y τ = false
      have hb' : Q'.accept (fx x) (fy y) τ' = false := hb
      cases ha : Q.accept x y τ with
      | false => rfl
      | true =>
        obtain ⟨τ'', h1, h2⟩ := hacc x y τ ha
        rw [hτ] at h1
        cases h1
        rw [hb'] at h2
        cases h2)
    (h (fx x) (fy y) fun hl => hn (hL x y hl))

/-- **The errors as probabilities.** If all error counts of s' are at most the probability c, then
those that follow for s are at most k * c. -/
theorem below_mulErr : ∀ (s s' : Shape) (ws : Err s) (k c : ℝ≥0∞) (ε : Err s'), Rate s s' ws k →
    Err.Below ε c → Err.Below (mulErr s s' ws ε) (k * c)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, [], (_, ws), k, c, _, _, _ =>
      ⟨by simp, below_mulErr s [] ws k c () (by cases s <;> trivial) trivial⟩
  | r :: s, r' :: s', (w, ws), k, c, (e, ε), hR, hB => by
      refine ⟨?_, below_mulErr s s' ws k c ε hR.2 hB.2⟩
      have h1 : (e : ℝ≥0∞) ≤ c * (Fintype.card r'.Chal : ℝ≥0∞) := hB.1
      have h2 : (w : ℝ≥0∞) * (Fintype.card r'.Chal : ℝ≥0∞)
          ≤ k * (Fintype.card r.Chal : ℝ≥0∞) := hR.1
      calc ((e * w : ℕ) : ℝ≥0∞) = (e : ℝ≥0∞) * (w : ℝ≥0∞) := Nat.cast_mul e w
        _ ≤ (c * (Fintype.card r'.Chal : ℝ≥0∞)) * (w : ℝ≥0∞) := by gcongr
        _ = c * ((w : ℝ≥0∞) * (Fintype.card r'.Chal : ℝ≥0∞)) := by ring
        _ ≤ c * (k * (Fintype.card r.Chal : ℝ≥0∞)) := by gcongr
        _ = k * c * (Fintype.card r.Chal : ℝ≥0∞) := by ring

end OnBytes.Slice

#print axioms OnBytes.Slice.Carry.doomed
#print axioms OnBytes.Slice.sound_carry
#print axioms OnBytes.Slice.below_mulErr
