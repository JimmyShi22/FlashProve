-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/Kit.lean: helper lemmas for composed protocols with slots.

The protocols are protocols with slots (`BatchInteractiveOracleProof`, Iop/Batch.lean). The file has annotations
(`RoundSplits`) of parts, and the soundness property (Snd-B), `SndB`, from sets of bad values. Terms:
lean/GLOSSARY.md: batch, slot.

(Snd-B) from bad values (`BatchInteractiveOracleProof.sndB_of_badFam`). Let each statement (x, Π), Π the external
string, outside the language have a family of sets of bad values (`Iop.BadFam`): for each round a
set of values of the challenge that is fixed before that challenge. Put State(Π, τ) = 1 if (x, Π) is
in the language or some challenge of the partial transcript τ of a slot is bad. It depends on Π and
one slot's transcript. A prover message never changes it, and it changes from 0 to 1 exactly at a
bad value. (On a full transcript this state may be 1 although the verifier rejects; (Snd-B) allows
that.) So (Snd-B) holds if every full transcript of a slot without a bad value is rejected, and if
the bad sets are small (`JWithin`).

Notation: from Iop/Batch.lean: `BatchInteractiveOracleProof X E`: a batch IOP with instances in X and the external
oracle(s) E: the local verifier, and the annotation of its shape; the number N of slots is an
argument of the properties; `Q.SndB N L ε`: (Snd-B) for the language L of pairs (x, Π): there is a
function State(Π, τ) ∈ {0,1} of the external oracle and a partial local transcript of a non-empty
slot such that: State(Π, x_j) = 1 if and only if (x_j, Π) is in L; a prover message never changes 0
to 1; if State(Π, τ_j) = 0 for a complete τ_j, then V_j rejects; and the law on verifier messages
(`JointLaw`) holds, for every Π and every instance vector; `a`: a `RAnn r`: the annotation of one
round r of the local shape: its kind, and the splitting of a prover message of the local transcript
into (m_0, m_j); `a.join m0 mj`: the prover message of a local transcript; `a.kind.All N C`: the
verifier message of the whole batch; `a.kind.slot : a.kind.All N C → Fin N → C`; `RAnn.Coherent`:
the data of an annotation fit together; `ε`: an `Err s` (Iop/Rbr.lean): one number for each round:
how many values of the challenge may lead from a doomed transcript to one that is not doomed.
-/
import Iop.Batch
import Iop.Compose
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop

open Prob

/-! ## 1. Annotations of rounds and of composed lists of rounds -/

theorem RoundSplits.const_coherent {f : ∀ r : Round, RAnn r} (h : ∀ r, (f r).Coherent) :
    ∀ s : Shape, (RoundSplits.const f s).Coherent
  | [] => trivial
  | r :: s => ⟨h r, RoundSplits.const_coherent h s⟩

theorem RoundSplits.app_coherent :
    ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t}, A.Coherent → B.Coherent → (RoundSplits.app A B).Coherent
  | [], _, _, _, _, h => h
  | _ :: _, _, (_, _), _, h, h' => ⟨h.1, RoundSplits.app_coherent h.2 h'⟩

/-! ## 2. The state: some challenge so far is bad (`BadFam.dirty`) -/

open Classical in
/-- Some challenge of the partial transcript is bad. -/
def BadFam.dirty : {s : Shape} → BadFam s → PTr s → Bool
  | [], _, _ => false
  | _ :: _, _, .atP (.inl _) => false
  | _ :: _, _, .atV (.inl _) => false
  | _ :: _, (B, k), .atP (.inr (m, c, τ)) => decide (c ∈ B m) || BadFam.dirty (k m c) (.atP τ)
  | _ :: _, (B, k), .atV (.inr (m, c, τ)) => decide (c ∈ B m) || BadFam.dirty (k m c) (.atV τ)
  | _ :: _, (B, k), .full (m, c, τ) => decide (c ∈ B m) || BadFam.dirty (k m c) (.full τ)

theorem BadFam.dirty_empty : ∀ {s : Shape} (B : BadFam s), B.dirty (PTr.empty s) = false
  | [], _ => rfl
  | _ :: _, _ => rfl

open Classical in
theorem BadFam.dirty_cons {r : Round} {s : Shape} (B : BadFam (r :: s)) (m : r.Msg) (c : r.Chal) :
    ∀ τ : PTr s, B.dirty (PTr.cons m c τ) = (decide (c ∈ B.1 m) || (B.2 m c).dirty τ)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

open Classical in
/-- A prover message does not change the state. -/
theorem BadFam.dirty_snoc :
    ∀ {s : Shape} (B : BadFam s) (τ : AtP s) (m : τ.round.Msg),
      B.dirty (.atV (τ.snoc m)) = B.dirty (.atP τ)
  | _ :: _, _, .inl _, _ => rfl
  | _ :: _, (B, k), .inr (m', c', τ), m => by
      show (decide (c' ∈ B m') || (k m' c').dirty (.atV (τ.snoc m))) =
        (decide (c' ∈ B m') || (k m' c').dirty (.atP τ))
      rw [BadFam.dirty_snoc (k m' c') τ m]

open Classical in
/-- A full transcript is in state 0 if and only if it has no bad value. -/
theorem BadFam.dirty_full :
    ∀ {s : Shape} (B : BadFam s) (τ : Tr s), B.dirty (.full τ) = false ↔ B.Clean τ
  | [], _, _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | _ :: _, (B, k), (m, c, τ) => by
      show (decide (c ∈ B m) || (k m c).dirty (.full τ)) = false ↔ (c ∉ B m ∧ (k m c).Clean τ)
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, BadFam.dirty_full (k m c) τ]

/-- The state function of a slot: a flag (the statement is true, or a bad value has occurred
already), or some later challenge is bad. -/
def stOf {s : Shape} (p : Bool × BadFam s) : PTr s → Bool := fun τ =>
  p.1 || p.2.dirty τ

/-! ## 3. The two conditions on bad sets -/

open Classical in
/-- What becomes of the flag and the bad sets of a slot after one round. -/
def stepOf {r : Round} {s : Shape} (p : Bool × BadFam (r :: s))
    (m : r.Msg) (c : r.Chal) : Bool × BadFam s :=
  (p.1 || decide (c ∈ p.2.1 m), p.2.2 m c)

/-- The bad sets are within the errors, jointly. G j holds the flag and the bad sets of slot j
(`none`: the slot is empty). In a local round the bad set of each slot in state 0 has at most e
elements; in a shared round so does the union of the bad sets of the slots in state 0. -/
def JWithin (N : ℕ) : (s : Shape) → RoundSplits s → Err s → (Fin N → Option (Bool × BadFam s)) → Prop
  | [], _, _, _ => True
  | r :: s, (a, A), (e, ε), G =>
      ∀ (m0 : a.M0) (m : Fin N → a.Mj),
        (match a.kind with
          | .lo =>
            ∀ j p,
              G j = some p → p.1 = false → cnt (fun c : r.Chal => c ∈ p.2.1 (a.join m0 (m j))) ≤ e
          | .sh =>
            cnt (fun c : r.Chal =>
                ∃ j p, G j = some p ∧ p.1 = false ∧ c ∈ p.2.1 (a.join m0 (m j))) ≤ e) ∧
        ∀ v : a.kind.All N r.Chal,
          JWithin N s A ε fun j => (G j).map fun p => stepOf p (a.join m0 (m j)) (a.kind.slot v j)

theorem stOf_atV {r : Round} {s : Shape} (p : Bool × BadFam (r :: s)) (m : r.Msg) :
    stOf p (.atV (Sum.inl m)) = p.1 := by
  show (p.1 || false) = p.1
  rw [Bool.or_false]

theorem stOf_cons {r : Round} {s : Shape} (p : Bool × BadFam (r :: s)) (m : r.Msg)
    (c : r.Chal) (τ : PTr s) :
    stOf p (PTr.cons m c τ) = stOf (stepOf p m c) τ := by
  show (p.1 || p.2.dirty (PTr.cons m c τ)) = ((p.1 || _) || (p.2.2 m c).dirty τ)
  rw [BadFam.dirty_cons, Bool.or_assoc]

open Classical in
theorem stOf_flip {r : Round} {s : Shape} (p : Bool × BadFam (r :: s)) (m : r.Msg) (c : r.Chal)
    (h0 : stOf p (.atV (Sum.inl m)) = false) (h1 : stOf p (PTr.cons m c (PTr.empty s)) = true) :
    p.1 = false ∧ c ∈ p.2.1 m := by
  rw [stOf_atV] at h0
  rw [stOf_cons] at h1
  have h2 : ((p.1 || decide (c ∈ p.2.1 m)) || (p.2.2 m c).dirty (PTr.empty s)) = true := h1
  rw [BadFam.dirty_empty, Bool.or_false, h0, Bool.false_or, decide_eq_true_eq] at h2
  exact ⟨h0, h2⟩

/-- `JWithin` gives the condition on challenges (`JointLaw`) of (Snd-B). -/
theorem jointLaw_of_jWithin (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (G : Fin N → Option (Bool × BadFam s)),
      JWithin N s A ε G → JointLaw N s A ε fun j => (G j).map stOf
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), G, h => by
      intro m0 m
      obtain ⟨h1, h2⟩ := h m0 m
      refine ⟨?_, fun v => ?_⟩
      · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
        cases k
        · refine le_trans (cnt_mono ?_) h1
          rintro c ⟨j, S, hS, hS0, hS1⟩
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hS
          exact ⟨j, p, hp, stOf_flip p _ c hS0 hS1⟩
        · intro j S hS hS0
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hS
          refine le_trans (cnt_mono fun c hc => (stOf_flip p _ c hS0 hc).2) (h1 j p hp ?_)
          rwa [stOf_atV] at hS0
      · have h3 := jointLaw_of_jWithin N s A ε _ (h2 v)
        have h4 : (fun j =>
              ((G j).map fun p => stepOf p (a.join m0 (m j)) (a.kind.slot v j)).map stOf) =
            fun j =>
              ((G j).map stOf).map fun S τ =>
                  S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) τ) := by
          funext j
          cases G j with
          | none => rfl
          | some p => exact congrArg some (funext fun τ => (stOf_cons p _ _ τ).symm)
        rw [h4] at h3
        exact h3

/-! ## 4. How `JWithin` is shown -/

/-- Larger errors are weaker. -/
theorem JWithin.mono (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) {ε ε' : Err s} (G : Fin N → Option (Bool × BadFam s)),
      Err.le ε ε' → JWithin N s A ε G → JWithin N s A ε' G
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), (e', ε'), G, hle, h => by
      intro m0 m
      obtain ⟨h1, h2⟩ := h m0 m
      refine ⟨?_, fun v => JWithin.mono N s A _ hle.2 (h2 v)⟩
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
      cases k
      · exact le_trans h1 hle.1
      · exact fun j p hp h0 => le_trans (h1 j p hp h0) hle.1

/-- Slots in state 1 ask for nothing. -/
theorem jWithin_of_flags (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (G : Fin N → Option (Bool × BadFam s)),
      (∀ j p, G j = some p → p.1 = true) → JWithin N s A ε G
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), G, h => by
      intro m0 m
      refine ⟨?_, fun v => jWithin_of_flags N s A ε _ fun j p hp => ?_⟩
      · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
        cases k
        · rw [cnt_false]
          · exact Nat.zero_le _
          · rintro c ⟨j, p, hp, h0, _⟩
            rw [h j p hp] at h0
            cases h0
        · intro j p hp h0
          rw [h j p hp] at h0
          cases h0
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        show (p'.1 || _) = true
        rw [h j p' hp', Bool.true_or]

/-- Local rounds: it is enough that the bad sets of each slot are within the errors
(`BadFam.Within`). -/
theorem jWithin_of_within (N : ℕ) (f : ∀ r : Round, RAnn r) (hf : ∀ r, (f r).kind = .lo) :
    ∀ (s : Shape) (ε : Err s) (G : Fin N → Option (Bool × BadFam s)),
      (∀ j p, G j = some p → p.2.Within ε) → JWithin N s (RoundSplits.const f s) ε G
  | [], _, _, _ => trivial
  | r :: s, (e, ε), G, h => by
      show JWithin N (r :: s) (f r, RoundSplits.const f s) (e, ε) G
      intro m0 m
      refine ⟨?_, fun v => jWithin_of_within N f hf s ε _ fun j p hp => ?_⟩
      · rw [hf r]
        exact fun j p hp _ => (h j p hp).1 _
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        exact (h j p' hp').2 _ _

/-- Shared rounds in which only the shared component is sent: if all slots have the same bad sets,
and these are within the errors, `JWithin` holds, since the union is one bad set. -/
theorem jWithin_of_same (N : ℕ) :
    ∀ (s : Shape) (ε : Err s) (B₀ : BadFam s) (G : Fin N → Option (Bool × BadFam s)), B₀.Within ε →
      (∀ j p, G j = some p → p.2 = B₀) → JWithin N s (RoundSplits.const (RAnn.ofShared .sh) s) ε G
  | [], _, _, _, _, _ => trivial
  | r :: s, (e, ε), B₀, G, hW, h => by
      show JWithin N (r :: s) (RAnn.ofShared .sh r, RoundSplits.const (RAnn.ofShared .sh) s) (e, ε) G
      intro m0 m
      refine ⟨?_, fun v => jWithin_of_same N s ε (B₀.2 m0 v) _ (hW.2 m0 v) fun j p hp => ?_⟩
      · refine le_trans (cnt_mono ?_) (hW.1 m0)
        rintro c ⟨j, p, hp, _, hc⟩
        rw [h j p hp] at hc
        exact hc
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        show p'.2.2 m0 v = B₀.2 m0 v
        rw [h j p' hp']

/-- Two parts in a row. The bad sets of the second may depend on the slot's transcript of the first.
A slot that has met a bad value in the first is in state 1 in the second. -/
theorem JWithin.app (N : ℕ) :
    ∀ (s t : Shape) (A : RoundSplits s) (A' : RoundSplits t) (ε : Err s) (ε' : Err t)
        (G : Fin N → Option (Bool × BadFam s)) (g : Fin N → Tr s → BadFam t),
      JWithin N s A ε G →
      (∀ τ : BTr N s A, JWithin N t A' ε' fun j =>
        (G j).map fun p => (p.1 || p.2.dirty (.full (τ.slot j)), g j (τ.slot j))) →
      JWithin N (s ++ t) (RoundSplits.app A A') (Err.app ε ε') fun j =>
        (G j).map fun p => (p.1, BadFam.app p.2 (g j))
  | [], t, A0, A', _, ε', G, g, _, h => by
      have h1 := h ()
      have h2 : (fun j =>
            (G j).map fun p : Bool × BadFam [] =>
              (p.1 || p.2.dirty (.full (BTr.slot (N := N) (s := []) (A := A0) j ())),
                g j (BTr.slot (N := N) (s := []) (A := A0) j ()))) =
          fun j => (G j).map fun p => (p.1, BadFam.app p.2 (g j)) := by
        funext j
        cases G j with
        | none => rfl
        | some p => exact congrArg some (Prod.ext (Bool.or_false _) rfl)
      rw [h2] at h1
      exact h1
  | r :: s, t, (a, A), A', (e, ε), ε', G, g, hG, h => by
      show JWithin N (r :: (s ++ t)) (a, RoundSplits.app A A') (e, Err.app ε ε') _
      intro m0 m
      obtain ⟨h1, h2⟩ := hG m0 m
      refine ⟨?_, fun v => ?_⟩
      · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
        cases k
        · refine le_trans (cnt_mono ?_) h1
          rintro c ⟨j, p, hp, h0, hc⟩
          obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
          exact ⟨j, p', hp', h0, hc⟩
        · intro j p hp h0
          obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
          exact h1 j p' hp' h0
      · have ih := JWithin.app N s t A A' ε ε'
          (fun j => (G j).map fun p => stepOf p (a.join m0 (m j)) (a.kind.slot v j))
          (fun j b => g j (a.join m0 (m j), a.kind.slot v j, b)) (h2 v) (fun τ => by
            have h3 := h ((m0, m), v, τ)
            have h4 : (fun j =>
              (G j).map fun p : Bool × BadFam (r :: s) =>
                (p.1 || p.2.dirty (.full (BTr.slot (A := (a, A)) j ((m0, m), v, τ))),
                  g j (BTr.slot (A := (a, A)) j ((m0, m), v, τ))))
                = fun j =>
                    ((G j).map fun p => stepOf p (a.join m0 (m j)) (a.kind.slot v j)).map fun p =>
                  (p.1 || p.2.dirty (.full (τ.slot j)),
                    g j (a.join m0 (m j), a.kind.slot v j, τ.slot j)) := by
              funext j
              cases G j with
              | none => rfl
              | some p => exact congrArg some (Prod.ext (Bool.or_assoc _ _ _).symm rfl)
            rw [h4] at h3
            exact h3)
        have h5 : (fun j =>
            ((G j).map fun p => stepOf p (a.join m0 (m j)) (a.kind.slot v j)).map fun p =>
              (p.1, BadFam.app p.2 fun b => g j (a.join m0 (m j), a.kind.slot v j, b)))
            = fun j =>
                ((G j).map fun p : Bool × BadFam (r :: s) =>
                    (p.1, BadFam.app p.2 (g j))).map fun p =>
              stepOf p (a.join m0 (m j)) (a.kind.slot v j) := by
          funext j
          cases G j with
          | none => rfl
          | some p => rfl
        rw [h5] at ih
        exact ih

open Classical in
/-- (Snd-B), `SndB`, from sets of bad values: every full transcript of a slot for a false statement
without a bad value is rejected (`hclean`), and the bad sets are within the errors, jointly
(`hJ`). -/
theorem BatchInteractiveOracleProof.sndB_of_badFam {X : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E) (N : ℕ)
    (L : X → E.Str → Prop) (ε : Err Q.loc.shape) (bad : X → E.Str → BadFam Q.loc.shape)
    (hclean : ∀ x y, ¬ L x y → ∀ τ, (bad x y).Clean τ → Q.loc.accept x y τ = false)
    (hJ : ∀ y (x : Fin N → Option X),
      JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (decide (L xj y), bad xj y)) :
    Q.SndB N L ε := by
  refine ⟨fun y x => stOf (decide (L x y), bad x y), fun y x => ?_, fun y x τ m h => ?_,
    fun y x τ h => ?_, fun y x => ?_⟩
  · show (decide (L x y) || (bad x y).dirty (PTr.empty _)) = true ↔ L x y
    rw [BadFam.dirty_empty, Bool.or_false, decide_eq_true_eq]
  · show (decide (L x y) || (bad x y).dirty (.atV (τ.snoc m))) = false
    rw [BadFam.dirty_snoc]
    exact h
  · have h' : (decide (L x y) || (bad x y).dirty (.full τ)) = false := h
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h'
    exact hclean x y h'.1 τ ((BadFam.dirty_full _ τ).mp h'.2)
  · have h1 := jointLaw_of_jWithin N _ _ ε _ (hJ y x)
    have h2 : (fun j => ((x j).map fun xj => (decide (L xj y), bad xj y)).map stOf)
        = fun j => (x j).map fun xj => stOf (decide (L xj y), bad xj y) := by
      funext j
      cases x j <;> rfl
    rw [h2] at h1
    exact h1

end Iop
