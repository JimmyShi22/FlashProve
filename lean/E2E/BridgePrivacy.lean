-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgePrivacy.lean: FROM A SENTENCE ON ONE REQUEST's HONEST PROVER TO THE PREMISES ON PROVERS OF
THE STATEMENT OF INDEX PRIVACY AT THE COMPILED ARGUMENT (`OnBytes.WholeKey.PremW`,
Johnson/WholeKey/Premises.lean): the clauses on the SESSION's prover of its fields `ext`, `runVals`,
`good` and `stops`. By calls. Each sentence of another file's stands here as a HYPOTHESIS BY NAME:
none of them is proved here.

The setting. L: an object with OOD samples. Fm: a family of honest provers of one request's
protocol by the copy's number (E2E/HonestFamily.lean). hT, hL: honest provers of the key file's
protocol and of the link: FREE LETTERS.

  `proversOf hT hL Fm`: the three honest provers as the statement takes them; the session's is
    `Fm.glue`.
  `sessionAt_proversOf`: the statement's "session's prover at a fixed number" is `Fm.at n`: by
    unfolding.
Hypotheses by name.
  `OneExact Fm sim Tied`: outside the part of the abort set that may hang on the private input, at
    EVERY verifier randomness, the honest output IS the named simulator's, at tied inputs.
  `ValidTied Tied ok Gs Ryes`: every valid pair of the object is tied: at every index in the range
    ok, every OOD seed in Gs, every committer's randomness and number. `ValidTied.mono`: it goes to
    every smaller ok, Gs and relation.
  `HidZero Fm W`: that part of the abort set does not hang on the proof-of-work test bits.
  `HidSmall Fm Tied z`: its measure is at most z at tied inputs.
What is shown.
  `extB_of`: the clause B of `ExtEnc`, from the family's external strings being the encoded index.
  **`goodB_of_exact`**: the clause B of `Sims.Good` AT ERROR 0: the set that it measures is EMPTY.
    No law on the wires and no blindness is spent: `OneExact` speaks at every verifier randomness,
    so at those with the test bits 0.
  **`stopsB_of_small`**: the clause B of `StopsSmall` at z: by `HidZero` the set that it measures is
    the set that `HidSmall` measures.
  `runValsB_of`: the clause B of `RunVals`, from a law on the plain parts at every verifier
    randomness.
  `extEnc_of`, `good_of_exact`, `stops_of_small`: the statement's own structures `ExtEnc`,
    `Sims.Good`, `StopsSmall` at `proversOf hT hL Fm`: the session's clause from the above; the key
    file's and the link's clauses are taken from a value of the same structure at any other family
    (they do not read the family).

Limits.
- CONDITIONAL THROUGHOUT. At hypotheses that nothing meets these theorems say nothing. No member
  is shown here.
- "ERROR 0" IS NO RESULT BY ITSELF: the statement of index privacy has a place for the measure of
  the stops that hang on the private input, and NONE for the public stops' measure, nor for the
  share of runs in which a verifier's test rejects and fixed substitutes are shown. Nor has it a
  place for the committer's randomness and OOD seeds at which every run is rejected. A family whose
  PUBLIC abort set is everything meets `OneExact` and `HidSmall` at 0. It is to be said only beside
  what is shown on acceptance OF THE SAME FAMILY (E2E/BridgeAccept.lean).
- The clauses on the key file's prover and on the link's are not treated here (the key file's:
  E2E/KeyBridge.lean, from hypotheses by name). The link's two numbers enter the statement's error
  with the number of copies as a factor.
- Of the field `coins` nothing is treated here.
- WHO PICKS THE NUMBER is not said here. `Family.glue` lays it inside the private input's type, so
  by type a caller may let it hang on the index; the sentences that are taken as hypotheses are
  written for a number that is fixed in front of index, coins and instance. That the number enters
  what is shown as the front round's number and in no other way is asked nowhere in this folder.


-/
import E2E.HonestFamily
import Johnson.WholeKey.Premises

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}

/-- The three honest provers as the statements on the compiled argument take them. -/
def proversOf (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
    (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)) : ThreeProvers L :=
  ⟨hT, hL, Fm.glue⟩

variable (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed))

theorem sessionAt_proversOf (n : ℕ) : sessionAt (proversOf hT hL Fm) n = Fm.at n := rfl

/-- The type of a session's simulators, one for each number (`Sims.B`). -/
abbrev SimB (L : HolographicProtocol I X) : Type :=
  ℕ → X × L.Rec → (ρ : Rho L.onlineBatch.loc.shape) →
    ((oneExternalString L.wordLength L.Symbol).Pos → Option (oneExternalString L.wordLength L.Symbol).Sym) → PMF (Option (DView L.onlineBatch.loc))

/-- **Hypothesis by name**: at tied inputs, at every verifier randomness outside `Hid`, the honest
output is the named simulator's. -/
def OneExact (sim : SimB L) (Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) : Prop :=
  ∀ n w x, Tied n w x → ∀ ρ, ρ ∉ (Fm.at n).Hid w x →
    (Fm.at n).output w x ρ = sim n x ρ (L.onlineBatch.loc.extAns x ρ ((Fm.at n).ext w))

/-- **Hypothesis by name**: every valid pair of the object is tied. -/
def ValidTied (Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) : Prop :=
  ∀ n i r e x, ok i → Gs e → Ryes i x → Tied n (i, r, e) (x, L.recOf i r e)

/-- It goes to every smaller range of indices, set of OOD seeds and relation. -/
theorem ValidTied.mono {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {ok ok' : I → Prop}
    {Gs Gs' : L.OutOfDomainSeed → Prop} {Ryes Ryes' : I → X → Prop} (h : ValidTied Tied ok Gs Ryes)
    (h1 : ∀ i, ok' i → ok i) (h2 : ∀ e, Gs' e → Gs e) (h3 : ∀ i x, Ryes' i x → Ryes i x) :
    ValidTied Tied ok' Gs' Ryes' :=
  fun n i r e x a b c => h n i r e x (h1 i a) (h2 e b) (h3 i x c)

/-- The family's external strings are the encoded index. -/
def ExtIsEnc : Prop := ∀ n i r e, Fm.ext n (i, r, e) = L.encodeIndex i r

theorem extB_of (h : ExtIsEnc Fm) :
    ∀ i r e n, (proversOf hT hL Fm).B.ext (i, r, e, n) = L.encodeIndex i r := fun i r e n => h n i r e

variable {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- **The clause B of `Sims.Good` at error 0**: the set is empty. "Error 0" is no result by itself:
this file's Limits. -/
theorem goodB_of_exact {sim : SimB L} {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop}
    {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} (h1 : OneExact Fm sim Tied)
    (h2 : ValidTied Tied ok Gs Ryes) (he : ExtIsEnc Fm) :
    ∀ n i r e x, ok i → Gs e → Ryes i x →
      pr (unif (Rho L.onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∉
            (sessionAt (proversOf hT hL Fm) n).Hid (i, r, e) (x, L.recOf i r e) ∧
          (sessionAt (proversOf hT hL Fm) n).output (i, r, e) (x, L.recOf i r e)
            (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) ≠
          sim n (x, L.recOf i r e) (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ)
            (L.onlineBatch.loc.extAns (x, L.recOf i r e)
              (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) (L.encodeIndex i r))} ≤ 0 := by
  intro n i r e x hi hg hx
  have hempty : {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∉
            (sessionAt (proversOf hT hL Fm) n).Hid (i, r, e) (x, L.recOf i r e) ∧
          (sessionAt (proversOf hT hL Fm) n).output (i, r, e) (x, L.recOf i r e)
            (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) ≠
          sim n (x, L.recOf i r e) (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ)
            (L.onlineBatch.loc.extAns (x, L.recOf i r e)
              (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) (L.encodeIndex i r))} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => hρ.2 ?_
    have h := h1 n (i, r, e) (x, L.recOf i r e) (h2 n i r e x hi hg hx) _ hρ.1
    rw [show (Fm.at n).ext (i, r, e) = L.encodeIndex i r from he n i r e] at h
    exact h
  rw [hempty]
  exact le_of_eq (pr_empty _)

/-- **Hypothesis by name**: the part of the abort set that may hang on the private input does not
hang on the proof-of-work test bits. -/
def HidZero : Prop :=
  ∀ n w x ρ, RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ (Fm.at n).Hid w x ↔
    ρ ∈ (Fm.at n).Hid w x

/-- **Hypothesis by name**: its measure at tied inputs. -/
def HidSmall (Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) (z : ℝ≥0∞) : Prop :=
  ∀ n w x, Tied n w x → prRho ((Fm.at n).Hid w x) ≤ z

/-- **The clause B of `StopsSmall`.** -/
theorem stopsB_of_small {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {ok : I → Prop}
    {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {z : ℝ≥0∞} (hz : HidSmall Fm Tied z)
    (h2 : ValidTied Tied ok Gs Ryes) (h0 : HidZero Fm W) :
    ∀ n i r e x, ok i → Gs e → Ryes i x →
      pr (unif (Rho L.onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈
          (sessionAt (proversOf hT hL Fm) n).Hid (i, r, e) (x, L.recOf i r e)} ≤ z := by
  intro n i r e x hi hg hx
  have hs : {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈
      (sessionAt (proversOf hT hL Fm) n).Hid (i, r, e) (x, L.recOf i r e)} =
      (Fm.at n).Hid (i, r, e) (x, L.recOf i r e) :=
    Set.ext fun ρ => h0 n (i, r, e) (x, L.recOf i r e) ρ
  rw [hs]
  exact hz n (i, r, e) (x, L.recOf i r e) (h2 n i r e x hi hg hx)

/-- **The statement's own structure `ExtEnc`**, the key file's and the link's clauses being premises
in the statement's own words. -/
theorem extEnc_of (h : ExtIsEnc Fm) (eT : ∀ i r e, hT.ext (i, r, e) = L.encodeIndex i r)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')) :
    ExtEnc (proversOf hT hL Fm) :=
  ⟨eT, eL, extB_of hT hL Fm h⟩

/-- **The statement's own structure `Sims.Good`**, the session's clause at error 0 (no result by
itself: this file's Limits); the other two clauses from a value of the structure at any other
family. -/
theorem good_of_exact {Sm : Sims L} {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop}
    {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞}
    {Fm' : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    (g : Sm.Good (proversOf hT hL Fm') W ok Gs Ryes zT zL zO) (h1 : OneExact Fm Sm.B Tied)
    (h2 : ValidTied Tied ok Gs Ryes) (he : ExtIsEnc Fm) :
    Sm.Good (proversOf hT hL Fm) W ok Gs Ryes zT zL 0 :=
  ⟨g.T, g.Lk, goodB_of_exact hT hL Fm W h1 h2 he⟩

/-- **The statement's own structure `StopsSmall`**, the session's clause at z; the other two clauses
from a value of the structure at any other family. -/
theorem stops_of_small {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {ok : I → Prop}
    {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {pT pL pO z : ℝ≥0∞}
    {Fm' : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    (s : StopsSmall (proversOf hT hL Fm') W ok Gs Ryes pT pL pO) (hz : HidSmall Fm Tied z)
    (h2 : ValidTied Tied ok Gs Ryes) (h0 : HidZero Fm W) :
    StopsSmall (proversOf hT hL Fm) W ok Gs Ryes pT pL z :=
  ⟨s.T, s.Lk, stopsB_of_small hT hL Fm W hz h2 h0⟩

/-- **The clause B of `RunVals`, without its two fences** (the range of indices; "outside the abort
set"): so it gives that clause behind two binders. In general letters: pv reads the run values off
the plain parts, rv off the coins. The hypothesis is a law on the strategy's plain parts at EVERY
verifier randomness, at the family. -/
theorem runValsB_of {RV : Type} (pv : Plains L.onlineBatch.loc.shape → RV) (rv : Fm.Coin → RV)
    (h : ∀ n w x κ ρ, pv ((Fm.strat n w x κ).run ρ).1.plains = rv κ) :
    ∀ i r e n x κ ρ,
      pv (((proversOf hT hL Fm).B.strat (i, r, e, n) (x, L.recOf i r e) κ).run ρ).1.plains = rv κ :=
  fun i r e n x κ ρ => h n (i, r, e) (x, L.recOf i r e) κ ρ

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.sessionAt_proversOf
#print axioms AtPublicFiles.Bridge.ValidTied.mono
#print axioms AtPublicFiles.Bridge.extB_of
#print axioms AtPublicFiles.Bridge.goodB_of_exact
#print axioms AtPublicFiles.Bridge.stopsB_of_small
#print axioms AtPublicFiles.Bridge.runValsB_of
#print axioms AtPublicFiles.Bridge.extEnc_of
#print axioms AtPublicFiles.Bridge.good_of_exact
#print axioms AtPublicFiles.Bridge.stops_of_small
