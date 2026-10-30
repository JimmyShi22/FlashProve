-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchKProofs.lean: proofs of five statements of Ior/Batch.lean on (Snd-B) with a witness
(`SndBK`).

(Snd-B) (`BatchInteractiveOracleProof.SndB`, Iop/Batch.lean; late form: `SndBL`) is round-by-round soundness of a
batch IOP by a state function: errors for one slot in local rounds, joint errors in shared rounds. A
slot is one of the N places of a batch, each with one instance or empty, with its own local
transcript.
`SndBK` (Ior/Batch.lean) is (Snd-B) with a witness: round-by-round knowledge soundness for the
instances of a batch, with a witness map that reads a witness off the instance and the prover's
oracles.
`Q.guard R wit` (Ior/Batch.lean) is Q with a verifier that also rejects when the extracted witness
is valid; `SndBK` says that the guarded protocol has (Snd-B), in the late form of Iop/Batch.lean,
for the empty language.
What `early`, `late` are: the head of Ior/Batch.lean.
The law on verifier messages (`JointLaw`, Iop/Batch.lean): a state function is moved from 0 to 1 by
at most ε_i values of the verifier message of round i (for one slot in a local round; for some slot,
jointly, in a shared round).
The errors of the fully joint law (`Err.jointAll`, Ior/Batch.lean): N e |Chal|^(N-1) tuples in a
local round (as a probability: N times the error of one instance), e in a shared round.

Main names (each proves the statement of the same name in `Iop.Spec`, Ior/Batch.lean, under that
statement's hypotheses):
  `sndBK_iff`: `SndBK` written out, when the whole instance stands in the first query (early = id,
    late = none);
  `sndB_of_sndBK`: `SndBK` gives (Snd-B), in the late form (`BatchInteractiveOracleProof.SndBL`, Iop/Batch.lean) with
    the same early and late, for the language of the relation, with the same errors and the same
    state function;
  `sndBK_of_sndB`: (Snd-B) gives `SndBK` (early = id, late = none) when the instance determines the
    witness: the state of a true statement is set to 0 throughout;
  `jointAll_of_sndBK`: the fully joint list of errors: a union bound over the slots on the tuples of
    a local round;
  `one_of_sndBK`: the list for one fixed instance: the state function of one slot gives "the prover
    has lost at the start" (`Doomed`) for the local protocol.

Limits: this file says nothing on any protocol. It says nothing on the late form beyond early = id,
late = none, but for `sndB_of_sndBK`. It says nothing on a converse of `jointAll_of_sndBK` or of
`one_of_sndBK`. `jointAll_of_sndBK` gives up the bound for each single slot in a local round,
`one_of_sndBK` gives up the joint bound in a shared round.
What the entries of the fully joint list count: see "Mind:" in the docstring of `Err.jointAll`
(Ior/Batch.lean). Bad sets from a state function, and back, are in Ior/BatchKProofsBad.lean.
Terms: lean/GLOSSARY.md: batch IOP, error, guard, local round, local transcript, slot, (Snd-B).
-/
import Ior.Batch
import Iop.BatchSound
import Prob.Count

set_option autoImplicit false

namespace Iop
open Prob

namespace BatchK
variable {X W : Type} {E : ExtSpec}

/-! ## 1. The guarded verifier -/

/-- The guarded verifier rejects if and only if: should the verifier accept, the extracted witness
is valid. -/
theorem guard_accept_false (Q : BatchInteractiveOracleProof X E) (R : X → E.Str → W → Prop)
    (wit : X → Orcs Q.loc.shape → W) (x : X) (y : E.Str) (τ : Tr Q.loc.shape) :
    (Q.guard R wit).loc.accept x y τ = false ↔
    (Q.loc.accept x y τ = true → R x y (wit x τ.read)) := by
  classical
  show (Q.loc.accept x y τ && !decide (R x y (wit x τ.read))) = false ↔ _
  cases Q.loc.accept x y τ <;> simp

/-! ## 2. The state of some slots set to 0 throughout -/

/-- The law on verifier messages is kept if the state of some slots is set to 0 throughout (b j =
false: slot j is set to 0). -/
theorem jointLaw_andFlag {N : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool)) (b : Fin N → Bool),
      JointLaw N s A ε St → JointLaw N s A ε fun j => (St j).map fun S τ => b j && S τ
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
          cases hb : b j with
          | false =>
            rw [cnt_false]
            · exact Nat.zero_le _
            · intro c hc
              simp at hc
          | true =>
            refine le_trans (cnt_mono fun c hc => ?_) (h1 j S hS (by simpa [hb] using h0))
            simpa [hb] using hc
        | sh =>
          simp only [hk] at h1 ⊢
          refine le_trans (cnt_mono ?_) h1
          rintro c ⟨j, S', hS', h0, hc⟩
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          obtain ⟨hb, hc'⟩ := Bool.and_eq_true_iff.1 hc
          exact ⟨j, S, hS, by simpa [hb] using h0, hc'⟩
      · have ih := jointLaw_andFlag s A ε _ b (h2 v)
        refine cast (congrArg (JointLaw N s A ε) ?_) ih
        funext j
        beta_reduce
        cases St j <;> rfl

/-! ## 3. Tuples of a local round -/

/-- For a non-empty set C and tuples of N values of C: if at most e values of C have the property P,
then at most e times |C|^(N-1) tuples have it at coordinate j. -/
theorem cnt_coord_le {C : Type} [Fintype C] [Nonempty C] {N : ℕ} (j : Fin N) (P : C → Prop)
    {e : ℕ} (h : cnt P ≤ e) :
    cnt (fun v : Fin N → C => P (v j)) ≤ e * Fintype.card C ^ (N - 1) := by
  classical
  have h1 := cnt_pi_coord (A := fun _ : Fin N => C) j P
  have hN : N = (N - 1) + 1 := (Nat.sub_add_cancel j.pos).symm
  have h2 : Fintype.card (Fin N → C) = Fintype.card C ^ (N - 1) * Fintype.card C := by
    rw [Fintype.card_fun, Fintype.card_fin, ← pow_succ, ← hN]
  rw [h2, ← Nat.mul_assoc] at h1
  rw [Nat.eq_of_mul_eq_mul_right Fintype.card_pos h1]
  exact Nat.mul_le_mul_right _ h

/-- From the law on verifier messages to the fully joint law. -/
theorem jointLawAll_of_jointLaw (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool)),
      JointLaw N s A ε St → JointLawAll N s A (Err.jointAll N A ε) St
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), St, h => by
      intro m0 m
      obtain ⟨h1, h2⟩ := h m0 m
      refine ⟨?_, fun v => jointLawAll_of_jointLaw N s A ε _ (h2 v)⟩
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
      cases k
      · exact h1
      · show cnt (fun v : Fin N → r.Chal =>
            ∃ j S,
              St j = some S ∧
              S (.atV (Sum.inl (sp.symm (m0, m j)))) = false ∧
              S (PTr.cons (sp.symm (m0, m j)) (v j) (PTr.empty s)) = true) ≤
          N * e * Fintype.card r.Chal ^ (N - 1)
        have := cnt_exists_le_mul (C := Fin N → r.Chal)
            (ι := Fin N) (fun j v => ∃ S, St j = some S ∧
            S (.atV (Sum.inl (sp.symm (m0, m j)))) = false ∧
            S (PTr.cons (sp.symm (m0, m j)) (v j) (PTr.empty s)) = true)
            (e * Fintype.card r.Chal ^ (N - 1))
            (fun j => cnt_coord_le j (fun c => ∃ S, St j = some S ∧
              S (.atV (Sum.inl (sp.symm (m0, m j)))) = false ∧ S (PTr.cons (sp.symm (m0, m j)) c (PTr.empty s)) = true) (by
              cases hS : St j with
              | none =>
                rw [cnt_false]
                · exact Nat.zero_le _
                · rintro c ⟨S, hS', -⟩
                  cases hS'
              | some S =>
                by_cases h0 : S (.atV (Sum.inl (sp.symm (m0, m j)))) = false
                · refine le_trans (cnt_mono ?_) (h1 j S hS h0)
                  rintro c ⟨S', hS', -, hc⟩
                  obtain rfl : S = S' := Option.some.inj hS'
                  exact hc
                · rw [cnt_false]
                  · exact Nat.zero_le _
                  · rintro c ⟨S', hS', h0', -⟩
                    obtain rfl : S = S' := Option.some.inj hS'
                    exact h0 h0'))
        rw [Fintype.card_fin, ← Nat.mul_assoc] at this
        exact this

/-! ## 4. One slot -/

/-- The verifier message of the whole batch in which every slot sees c. -/
def rep {C : Type} (N : ℕ) : (k : Kind) → C → k.All N C
  | .sh, c => c
  | .lo, c => fun _ => c

theorem slot_rep {C : Type} {N : ℕ} (k : Kind) (c : C) (j : Fin N) : k.slot (rep N k c) j = c := by
  cases k <;> rfl

/-- If a state function S on local transcripts
   stands in some slot j0 of a vector with the law on verifier messages,
   no prover message moves it from 0 to 1,
   it is 0 at the start,
   and at its value 0 on a full transcript "bad" holds,
then the prover has lost at the start (`Doomed s ε bad`), with the same errors. -/
theorem doomed_of_jointLaw {N : ℕ} (j0 : Fin N) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool))
        (S : PTr s → Bool) (bad : Tr s → Prop),
      St j0 = some S → BatchH4.ProverLaw s S → JointLaw N s A ε St → S (PTr.empty s) = false →
      (∀ τ, S (.full τ) = false → bad τ) → Doomed s ε bad
  | [], _, _, _, _, _, _, _, _, h0, hf => hf () h0
  | r :: s, (a, A), (e, ε), St, S, bad, hS, hP, hJ, h0, hf => by
      intro msg
      obtain ⟨⟨m0, mj⟩, rfl⟩ := a.split.symm.surjective msg
      obtain ⟨h1, h2⟩ := hJ m0 (fun _ => mj)
      have hV : S (.atV (Sum.inl (a.split.symm (m0, mj)))) = false := hP (Sum.inl ()) _ h0
      have hc : cnt
            (fun c : r.Chal => S (PTr.cons (a.split.symm (m0, mj)) c (PTr.empty s)) = true) ≤
          e := by
        cases hk : a.kind with
        | lo =>
          simp only [hk] at h1
          exact h1 j0 S hS hV
        | sh =>
          simp only [hk] at h1
          exact le_trans (cnt_mono fun c hc => ⟨j0, S, hS, hV, hc⟩) h1
      refine le_trans (cnt_mono fun c hc' => ?_) hc
      by_contra hn
      refine hc'
        (doomed_of_jointLaw j0 s A ε _ (fun τ => S (PTr.cons (a.split.symm (m0, mj)) c τ)) _ ?_
          (hP.tail _ c) (h2 (rep N a.kind c)) (Bool.eq_false_iff.2 hn) (fun τ h => hf (_, c, τ) h))
      beta_reduce
      rw [hS, slot_rep]
      rfl

end BatchK

open BatchK

/-! ## 5. The five statements -/

theorem sndBK_iff : Spec.sndBK_iff := by
  intro X W E Q N R wit ε
  constructor
  · rintro ⟨-, State, h1, h2, -, h3, h4⟩
    exact ⟨State, fun y x => h1 y x id, h2,
      fun y x τ h0 => (guard_accept_false Q R wit x y τ).1 (h3 y x τ id h0), h4⟩
  · rintro ⟨State, h1, h2, h3, h4⟩
    exact ⟨fun n hn => (by cases hn), State, fun y x _ => h1 y x, h2,
      fun _ _ _ _ hn => (by cases hn),
      fun y x τ _ h0 => (guard_accept_false Q R wit x y τ).2 (h3 y x τ h0), h4⟩

theorem sndB_of_sndBK : Spec.sndB_of_sndBK := by
  intro X W E Q N early late R wit ε
  rintro ⟨h0, State, h1, h2, h3, h4, h5⟩
  refine ⟨h0, State, fun y x _ => h1 y x id, h2, fun y x τ _ => h3 y x τ id,
    fun y x τ hL hs => ?_, h5⟩
  have h6 := (guard_accept_false Q R wit x y τ).1 (h4 y x τ id hs)
  exact Bool.eq_false_iff.2 fun ha => hL ⟨_, h6 ha⟩

theorem sndBK_of_sndB : Spec.sndBK_of_sndB := by
  classical
  intro X W E Q N L R d ε
  rintro ⟨State, h1, h2, h3, h4⟩ hLR
  refine (sndBK_iff X W E Q N R (fun x _ => d x) ε).2 ⟨fun y x τ => !decide (L x y) && State y x τ,
    fun y x => ?_, fun y x τ m h => ?_, fun y x τ h ha => ?_, fun y x => ?_⟩
  · by_cases hL : L x y
    · simp [hL]
    · have : State y x (PTr.empty Q.loc.shape) = false :=
        Bool.eq_false_iff.2 fun h => hL ((h1 y x).1 h)
      simp [this]
  · by_cases hL : L x y
    · simp [hL]
    · have h' : State y x (.atP τ) = false := by simpa [hL] using h
      simp [h2 y x τ m h']
  · by_cases hL : L x y
    · exact hLR x y hL
    · have h' : State y x (.full τ) = false := by simpa [hL] using h
      rw [h3 y x τ h'] at ha
      cases ha
  · have h5 :=
      jointLaw_andFlag _ _ ε _ (fun j => ((x j).map fun xj => !decide (L xj y)).getD false) (h4 y x)
    refine cast (congrArg (JointLaw N Q.loc.shape Q.ann ε) ?_) h5
    funext j
    beta_reduce
    cases x j <;> rfl

theorem jointAll_of_sndBK : Spec.jointAll_of_sndBK := by
  intro X W E Q N R wit ε h
  obtain ⟨State, h1, h2, h3, h4⟩ := (sndBK_iff X W E Q N R wit ε).1 h
  exact ⟨State, h1, h2, h3, fun y x => jointLawAll_of_jointLaw N _ _ ε _ (h4 y x)⟩

theorem one_of_sndBK : Spec.one_of_sndBK := by
  intro X W E Q N R wit ε hN h x y
  obtain ⟨State, h1, h2, h3, h4⟩ := (sndBK_iff X W E Q N R wit ε).1 h
  exact doomed_of_jointLaw ⟨0, hN⟩ _ Q.ann ε _ (State y x) _ rfl (h2 y x)
    (h4 y fun _ => some x) (h1 y x) (h3 y x)

end Iop
