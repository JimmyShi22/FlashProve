-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WideIndex.lean: an accepted key fixes one index: the index's part of index binding, alone.


This file is about index binding, the soundness notion of a commit-and-prove argument: its part on
the index alone, without the claim on the instance.
Definitions, statements and proofs: an assembly. Over the compiler's typed oracles.

Read the title so: the statement is about one accepted pair (x, π) a run: but for ε, the encoded
index of that proof's session decodes to E_i(key, trC). "One index" because E_i reads the key and
the committer's trace alone, not the proof. "For all proofs under the key at once" is not said.
The compiler's theorems have one binding clause, one number bounding the round errors of all three
lists (offline test, link, session). What they say of the index does not need the session's list.

Main names, each statement under its hypotheses:
  `idxR`: the relation on (index i, instance, w : an index or nothing): w = some i.
  `L.witIdx`: the "witness map" of a session that returns what the encoded index of the session
    decodes to. It reads the encoded index alone: no oracle, no plain part, no verifier message.
  `Spec.soundAtKT_index`: for this relation and this map a session has knowledge soundness with all
    errors 0 (the claim "the encoded index does not decode, or it decodes to what it decodes to" is
    always true); the offline list and the link's list are the interface's own.
  `IdxBelow εT εL c₀ o`: in the offline list and in the link's list each round's error is ≤ c₀
    (with work in o: once that round's bits count). Nothing is asked of the session's list by this
    condition.


  `extractorIdx D o`: E_i: as always: the interface's decoder on what the committer's trace
    determines under the key's first root. E_w(key, trC, x, π, trP): the decoder on what the two
    traces determine under the root of the further encoded index that the proof names (the root
    stands in the key).
  `epsIdx D κ₀ c₀ o`: (tC + tP + tVB + 1) · κ₀^K · c₀ + 2 (tC + tP + tVB + 2)² / 2^λ: a bound at c₀,
    defined here; no statement of this library is made at it.
  `Spec.indexWire`: index binding (ZKCP/Gen.lean) of `Gen.withW (Option I) (argBKE W WP p)` for
    `idxR`, at `epsB W N`, for any interface with `L.SoundKT idxR L.witIdx N.εs` and any wire with
    `W.OKG`. In words: but for that bound, if the verifier accepts any (x, π) under the key, then
    E_i(key, trC) is an index i, and the further encoded index on which the proof's session runs
    decodes to the same i.








Limits: this file says nothing on x: a witness of x for i needs the session's list (the compiler's
theorems). It says nothing on a claim that a session's preamble leaves on the index. One pair (x, π)
a run. The event is "the verifier accepts", which includes the session's check: a key whose offline
proof and link verify while no session is ever accepted is not spoken of. tVB counts all queries of
the verifier, the session's too. K (`D.dr.K`) is the largest number of blocks of a round of all
three protocols, the session's too. It says nothing on running times.
What c₀ rests on is not said here: it bounds all rounds of the two lists: at a protocol not only the
fold of the encoded index, but every round of the offline phase's preamble, of the oracle messages
that the offline test and the link send themselves, and of their closing tests. c₀ is free of an
assumed theorem on codes only if all these stand where the needed facts are proved.

Terms: lean/GLOSSARY.md.
-/
import CompileK.WideZero

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

theorem Err.timesShared_zero (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s), Err.timesShared N A (Err.zero s) = Err.zero s
  | [], _ => rfl
  | _ :: s, (a, A) => by
      show ((match a.kind with | .lo => 0 | .sh => N * 0), Err.timesShared N A (Err.zero s)) =
        (0, Err.zero s)
      rw [Err.timesShared_zero N s A]
      cases a.kind <;> rfl

variable {I X Wn : Type}

/-- w is the index. -/
def idxR : I → X → Option I → Prop := fun i _ w => w = some i

/-- What the encoded index of the session decodes to. -/
def BatchProtocol.witIdx (L : BatchProtocol I X) : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Option I :=
  fun _ y _ => L.decodeIndex y

namespace Spec

/-- States: for "the index" a session has all errors 0, if the interface has `SoundAtKT` for some
relation, map and lists. -/
def soundAtKT_index : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtKT Rno wit εT εL εB → L.SoundAtKT idxR L.witIdx εT εL (Err.zero _)

end Spec

theorem soundAtKT_index : Spec.soundAtKT_index := by
  intro I X Wn L Rno wit εT εL εB h
  obtain ⟨hB0, -⟩ := (sndBKT_laws X Wn _ L.onlineBatch L.maxBatchSize L.early L.late (L.relB Rno) wit εB).1 h.sndB
  refine ⟨h.sndT, h.sndL,
    (sndBKT_laws X (Option I) _ L.onlineBatch L.maxBatchSize L.early L.late (L.relB idxR) L.witIdx (Err.zero _)).2
      ⟨hB0, fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_, ?_⟩⟩
  · intro y x τ _ _
    show L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ L.decodeIndex y = some i
    cases hd : L.decodeIndex y with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl, rfl⟩
  · intro y x
    have hj := BatchH4.jointLaw_of_verLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann (Err.zero _) (fun j => (x j).map fun _ _ => false) (fun j S hS τ _ => by
                                 obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hS
                                 exact (le_of_eq (cnt_false fun _ hc => by cases hc)).trans (Nat.zero_le _))
    rwa [Err.timesShared_zero] at hj

end Iop

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type}

/-- Every round of the offline list and of the link's list has error at most c₀, counting its work.
-/
def IdxBelow {Nn : Type} {L : BatchProtocol I X} (εT : Err L.offline.shape) (εL : Err L.link.shape) (c₀ : ℝ≥0∞) :
    Option (Work Nn L) → Prop
  | none => Err.Below εT c₀ ∧ Err.Below εL c₀
  | some w => Err.BelowG w.gT εT c₀ ∧ Err.BelowG w.gL εL c₀

/-- The two extractors. -/
def extractorIdx {Nn : Type} [Inhabited Nn] {L : BatchProtocol I X} {lam : ℕ}
    (D : DataK L lam) (o : Option (Work Nn L)) :
    Gen.Extractor (spec lam (D.WO o).K (D.LO o)) I X (Option I)
      (IVKK lam (D.LO o)) (PrfK lam (D.LO o)) :=
  Gen.totalE none (extractorBKTo (D.WO o) 0 (D.LO o).witIdx)

/-- The bound. -/
def epsIdx {Nn : Type} [Inhabited Nn] {L : BatchProtocol I X} {lam : ℕ} (D : DataK L lam)
    (κ₀ c₀ : ℝ≥0∞) (o : Option (Work Nn L)) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVB (D.WO o) + 1 : ℕ) : ℝ≥0∞) * (κ₀ ^ D.dr.K * c₀) +
    2 * ((tC + tP + tVB (D.WO o) + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

namespace Spec

/-- Index binding for `idxR` at `epsB W N`, for any interface and any wire with `W.OKG`. (not all
hypotheses are named here: see the statement below) -/
def indexWire : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L)
      (p : Params) (N : LH.Nums),
    L.SoundKT idxR L.witIdx N.εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → L.onlineBatch.loc.shape ≠ [] →
    Gen.HasIndexBindingWith (Gen.relPairW idxR idxR fun _ _ _ h => h)
      (Gen.withW (Option I) (argBKE W WP p))
      (Gen.totalE none (extractorBKTo W 0 L.witIdx)) (epsB W N)

end Spec

theorem indexWire : Spec.indexWire := by
  intro I X lam L W WP p N hS hlT hlL hlB hco hW hne
  have hb := bindingUpTo I X (Option I) lam L W WP p 0 idxR idxR L.witIdx N (fun _ _ _ h => h) hS
    (fun _ _ _ _ _ _ _ => rfl) hlT hlL hlB hco hW hne
  have h := Gen.binding_total _ _ _ _ _ _ _ _ idxR idxR (fun _ _ _ h => h) _ none _ (fun _ _ => 0)
    hb (missLe_zero W WP p L.witIdx)
  simpa only [add_zero] using h

end Compile.Batch
