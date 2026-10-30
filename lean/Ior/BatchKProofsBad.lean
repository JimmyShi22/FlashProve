-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchKProofsBad.lean: state functions and sets of bad values for batches give each other, with
the same errors.

A definition, and theorems with their proofs. Blocks/Batch/Kit.lean shows (Snd-B) from families of
sets of bad values that are within the errors, jointly (`JWithin`: `BatchInteractiveOracleProof.sndB_of_badFam`,
under its two hypotheses `hclean`, `hJ`). Here is the converse, and both directions for (Snd-B) with
a witness (`SndBK`, Ior/Batch.lean).
(Snd-B) (`BatchInteractiveOracleProof.SndB`, Iop/Batch.lean; late form: `SndBL`) is round-by-round soundness of a
batch IOP by a state function: errors for one slot in local rounds, joint errors in shared rounds. A
family of bad sets (`BadFam`, Iop/Rbr.lean) has for each round a set of values of the verifier
message, fixed before that message. A slot is one of the N places of a batch, each with one instance
or empty, with its own local transcript.
`Q.guard R wit` (Ior/Batch.lean) is Q with a verifier that also rejects when the extracted witness
is valid; `SndBK` says that the guarded protocol has (Snd-B), in the late form of Iop/Batch.lean,
for the empty language.
`early`, `late`: how an instance is written into the hash chain of its slot: early x into the first
query, x itself into the query of the round late (see the docstring of `BatchInteractiveOracleProof.SndBL`,
Iop/Batch.lean).
y : `E.Str` is the external oracle (shared by the slots). The flag of a slot: the statement is true,
or a bad value has occurred already (`stOf`, `JWithin`, Blocks/Batch/Kit.lean). In
`BatchInteractiveOracleProof.SndB.exists_badFam` it begins as "the statement is true". For `SndBK`, (Snd-B) of the
guarded protocol for the empty language, it begins as 0.
"Jointly" (`JWithin`, Blocks/Batch/Kit.lean): G j holds the flag and the bad sets of slot j (none:
the slot is empty); in a local round the bad set of each slot in state 0 has at most e elements (e:
the round's error); in a shared round the union of the bad sets of the slots in state 0 has at most
e elements.
The law on verifier messages (`JointLaw`, Iop/Batch.lean): a state function is moved from 0 to 1 by
at most ε_i values of the verifier message of round i (for one slot in a local round; for some slot,
jointly, in a shared round). `ProverLaw` (Iop/BatchSound.lean): a prover message never changes 0 to
1.

Main names:
  `BatchInteractiveOracleProof.sndBK_iff_badFam`: at early = id, late = none, `SndBK` holds if and only if there are
    bad sets, for every statement, with two properties: (1) they are within the errors jointly, from
    flag 0; (2) on every full local transcript without a bad value the verifier rejects or the
    extracted witness is valid.
  `BatchInteractiveOracleProof.SndB.exists_badFam`: the converse for (Snd-B); see its docstring.

Why: bad sets compose by `JWithin.app` (two parts in a row), state functions do not compose as
readily.
Limits: this file says nothing on the late form beyond early = id, late = none, and nothing on any
protocol.
Terms: lean/GLOSSARY.md: bad values, error, external oracles, guard, local round, (Snd-B).
-/
import Ior.BatchKProofs
import Blocks.Batch.Kit

set_option autoImplicit false

namespace Iop
open Prob

/-- The bad values of a state function: in each round, after the prover message m, the values of the
verifier message that move the state from 0 to 1. -/
def BadFam.ofState : (s : Shape) → (PTr s → Bool) → BadFam s
  | [], _ => ()
  | _ :: s, S =>
    (fun m => {c | S (.atV (Sum.inl m)) = false ∧ S (PTr.cons m c (PTr.empty s)) = true},
      fun m c => BadFam.ofState s fun τ => S (PTr.cons m c τ))

namespace BatchK

/-- A state function that starts at 0 and that no prover message moves from 0 to 1 is 0 on every
full transcript without a bad value. -/
theorem ofState_clean :
    ∀ (s : Shape) (S : PTr s → Bool), BatchH4.ProverLaw s S → S (PTr.empty s) = false →
      ∀ τ : Tr s, (BadFam.ofState s S).Clean τ → S (.full τ) = false
  | [], _, _, h0, (), _ => h0
  | _ :: s, S, hP, h0, (m, c, τ), ⟨hc, hτ⟩ =>
      ofState_clean s (fun τ => S (PTr.cons m c τ)) (hP.tail m c)
        (Bool.eq_false_iff.2 fun h => hc ⟨hP (Sum.inl ()) m h0, h⟩) τ hτ

/-- The law on verifier messages gives the laws on the bad sets of the state functions
(`BadFam.ofState`), whatever the flags are. -/
theorem jWithin_ofState (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool))
        (G : Fin N → Option (Bool × BadFam s)),
      (∀ j, (G j).map Prod.snd = (St j).map (BadFam.ofState s)) →
      JointLaw N s A ε St → JWithin N s A ε G
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), St, G, hG, h => by
      intro m0 m
      obtain ⟨h1, h2⟩ := h m0 m
      have key : ∀ j p,
          G j = some p → ∃ S, St j = some S ∧ p.2 = BadFam.ofState (r :: s) S := fun j p hp => by
        have h3 := hG j
        rw [hp] at h3
        obtain ⟨S, hS, hS'⟩ := Option.map_eq_some_iff.1 h3.symm
        exact ⟨S, hS, hS'.symm⟩
      refine ⟨?_,
        fun v =>
          jWithin_ofState N s A ε
            (fun j => (St j).map fun S τ => S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) τ)) _
            (fun j => ?_) (h2 v)⟩
      · cases hk : a.kind with
        | lo =>
          simp only [hk] at h1 ⊢
          intro j p hp _
          obtain ⟨S, hS, hp2⟩ := key j p hp
          rw [hp2]
          by_cases h0 : S (.atV (Sum.inl (a.join m0 (m j)))) = false
          · exact le_trans (cnt_mono fun c hc => hc.2) (h1 j S hS h0)
          · rw [cnt_false]
            · exact Nat.zero_le _
            · exact fun c hc => h0 hc.1
        | sh =>
          simp only [hk] at h1 ⊢
          refine le_trans (cnt_mono ?_) h1
          rintro c ⟨j, p, hp, -, hc⟩
          obtain ⟨S, hS, hp2⟩ := key j p hp
          rw [hp2] at hc
          exact ⟨j, S, hS, hc.1, hc.2⟩
      · beta_reduce
        cases hp : G j with
        | none =>
          have h3 := hG j
          rw [hp] at h3
          cases hS : St j with
          | none => rfl
          | some S => rw [hS] at h3; cases h3
        | some p =>
          obtain ⟨S, hS, hp2⟩ := key j p hp
          rw [hS]
          show some (p.2.2 _ _) = _
          rw [hp2]
          rfl

end BatchK

open BatchK

variable {X W : Type} {E : ExtSpec}

open Classical in
/-- (Snd-B) gives sets of bad values: the converse of `BatchInteractiveOracleProof.sndB_of_badFam`
(Blocks/Batch/Kit.lean), with the same errors. -/
theorem BatchInteractiveOracleProof.SndB.exists_badFam
    {Q : BatchInteractiveOracleProof X E} {N : ℕ} {L : X → E.Str → Prop} {ε : Err Q.loc.shape} (h : Q.SndB N L ε) :
    ∃ bad : X → E.Str → BadFam Q.loc.shape,
      (∀ x y, ¬ L x y → ∀ τ, (bad x y).Clean τ → Q.loc.accept x y τ = false) ∧
      ∀ y (x : Fin N → Option X),
        JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (decide (L xj y), bad xj y) := by
  obtain ⟨State, h1, h2, h3, h4⟩ := h
  refine ⟨fun x y => BadFam.ofState _ (State y x),
    fun x y hL τ hτ =>
      h3 y x τ (ofState_clean _ _ (h2 y x) (Bool.eq_false_iff.2 fun h => hL ((h1 y x).1 h)) τ hτ),
    fun y x => jWithin_ofState N _ _ ε _ _ (fun j => ?_) (h4 y x)⟩
  cases x j <;> rfl

/-- `SndBK` at early = id, late = none gives sets of bad values, for every statement, with the same
errors. -/
theorem BatchInteractiveOracleProof.SndBK.exists_badFam {Q : BatchInteractiveOracleProof X E} {N : ℕ} {R : X → E.Str → W → Prop}
    {wit : X → Orcs Q.loc.shape → W} {ε : Err Q.loc.shape} (h : Q.SndBK N id none R wit ε) :
    ∃ bad : X → E.Str → BadFam Q.loc.shape,
      (∀ x y τ, (bad x y).Clean τ → Q.loc.accept x y τ = true → R x y (wit x τ.read)) ∧
      ∀ y (x : Fin N → Option X),
        JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (false, bad xj y) := by
  obtain ⟨State, h1, h2, h3, h4⟩ := (sndBK_iff X W E Q N R wit ε).1 h
  refine ⟨fun x y => BadFam.ofState _ (State y x),
    fun x y τ hτ => h3 y x τ (ofState_clean _ _ (h2 y x) (h1 y x) τ hτ),
    fun y x => jWithin_ofState N _ _ ε _ _ (fun j => ?_) (h4 y x)⟩
  cases x j <;> rfl

/-- `SndBK` at early = id, late = none, from sets of bad values: on every full local transcript
without a bad value the verifier rejects or the extracted witness is valid (`hclean`), and the bad
sets of all statements are within the errors, jointly (`hJ`). -/
theorem BatchInteractiveOracleProof.sndBK_of_badFam (Q : BatchInteractiveOracleProof X E) (N : ℕ) (R : X → E.Str → W → Prop)
    (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape) (bad : X → E.Str → BadFam Q.loc.shape)
    (hclean : ∀ x y τ, (bad x y).Clean τ → Q.loc.accept x y τ = true → R x y (wit x τ.read))
    (hJ : ∀ y (x : Fin N → Option X),
      JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (false, bad xj y)) :
    Q.SndBK N id none R wit ε := by
  refine (sndBK_iff X W E Q N R wit ε).2 ⟨fun y x => stOf (false, bad x y), fun y x => ?_,
    fun y x τ m h => ?_, fun y x τ h => ?_, fun y x => ?_⟩
  · show (false || (bad x y).dirty (PTr.empty _)) = false
    rw [BadFam.dirty_empty]
    rfl
  · show (false || (bad x y).dirty (.atV (τ.snoc m))) = false
    rw [BadFam.dirty_snoc]
    exact h
  · have h' : (false || (bad x y).dirty (.full τ)) = false := h
    rw [Bool.false_or] at h'
    exact hclean x y τ ((BadFam.dirty_full _ τ).mp h')
  · have h1 := jointLaw_of_jWithin N _ _ ε _ (hJ y x)
    have h2 : (fun j => ((x j).map fun xj => ((false : Bool), bad xj y)).map stOf) =
        fun j => (x j).map fun xj => stOf (false, bad xj y) := by
      funext j
      cases x j <;> rfl
    rw [h2] at h1
    exact h1

/-- The two together. -/
theorem BatchInteractiveOracleProof.sndBK_iff_badFam (Q : BatchInteractiveOracleProof X E) (N : ℕ) (R : X → E.Str → W → Prop)
    (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape) :
    Q.SndBK N id none R wit ε ↔
    ∃ bad : X → E.Str → BadFam Q.loc.shape,
      (∀ x y τ, (bad x y).Clean τ → Q.loc.accept x y τ = true → R x y (wit x τ.read)) ∧
      ∀ y (x : Fin N → Option X),
        JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (false, bad xj y) :=
  ⟨fun h => h.exists_badFam, fun ⟨bad, h1, h2⟩ => Q.sndBK_of_badFam N R wit ε bad h1 h2⟩

end Iop
