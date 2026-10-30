-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/OfHonest.lean: THE ACCEPT LAWS AS THE PROVER OF A WHOLE REQUEST SPENDS THEM
(AccAt, SetsSmall: Johnson/Prover/All/End.lean, Law.lean), FROM THREE HONEST RECORDS THAT ARE
ARGUMENTS, AND THREE FAMILIES OF FALLS. The records are values of the library's type of an honest
prover (Honest, Iop/InteractiveOracleProof.lean) for the three protocols of an object with records. The strategies
are the records' strategies; a set B is the record's withheld set together with the fall at the
record's coin; the seeds that are set aside (Z) are letters.

THE RECORDS ARE NOT THE OBJECT's OWN FIELDS honestOfflineProver, honestLinkProver, honestOnlineBatchProver: an object may hold silent place-holders
there, and it is not to be changed. The session's record is handed the copy's number with its
private input.

WHAT A FALL IS. A test of the verifier's own, with code, run on the plain messages that are sent and
the challenges; and Fall w x κ, a set of lists of challenges, is its pull-back along the honest
play: it reads the private input and the instance beside the coin. It reads no oracle's answer
beyond the challenges. AT A FALL NO ACCEPTANCE IS OWED, and its measure is paid at each fixed
private input, instance and coin. WHAT A STRATEGY SENDS AT OR BEHIND A FALL IS NOT ASKED HERE, but
for the clause num (the copy's number in the session's plain parts), which is asked at every list of
challenges: the strategies are arguments. Here the three families (Falls) are letters: that a given
one is such a pull-back is not asked; the empty family (Falls.none) is one.

WHY. A verifier's test may fail on a coin: for nearly every list of challenges some coin fails it,
while at each fixed coin the lists that fail are few. Acceptance at every coin outside a set OF
SMALL MEASURE that reads no coin cannot hold then. So acceptance is owed at every private input,
instance and coin, at every list outside the withheld set and outside the fall there; and the
measure is asked at each fixed private input, instance and coin.

WHAT IS ASKED OF THE RECORDS AND THE FALLS (HonFit) IS THE CONDITIONAL FORM: the verifier accepts
outside the withheld set and the fall WHERE ALL TESTS OF WORK ARE PASSED, at every transcript that
is the honest run but for nonces, at seeds that are not set aside; withheld set and fall together do
not hang on the test bits (for a fall that is a pull-back this wants that the test reads no test bit
AND that the honest play's plain messages do not hang on them: a clause on the strategy that is
stated nowhere here); their measure, and that of the seeds set aside, is bounded. NOT asked:
acceptance at every ρ outside the withheld set (Honest.Acc, Iop/InteractiveOracleProof.lean; CompleteR,
Hiop/RecInterface.lean). NOT asked: that the decoder gives every index back (WiredR.dec_enc).

Like definitions, over the wire records of Iop/BatchWire.lean and the object's own fields, without
falls: GrFit.wh, GrFit.acc (Compile/Batch/SpecFit.lean).

Main names.
  ThreeProvers, Falls, Falls.none   the three records; the three families of falls; the empty ones.
  ThreeProvers.strats, ThreeProvers.bads   the strategies; the sets, at the three coins.
  HonFit, HonFit.mono   the clauses; they pass to every smaller set of true instances.
  accAt_of_honest, small_of_honest   THE STATEMENTS.

Limits. HonFit is a premise: its one member that is shown is idle (Johnson/Prover/At/IdleAt.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.End

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- Three honest records for the three protocols of an object with records: arguments. The private
inputs: (index, randomness, seed); the link's: both tables'; the session's: with the copy's
number. -/
structure ThreeProvers (L : HolographicProtocol I X) where
  T : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)
  Lk : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))
  B : Honest L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed × ℕ)

variable {L : HolographicProtocol I X} (Hs : ThreeProvers L) {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- **Three families of falls**: private input → instance → coin → a set of lists of challenges. -/
structure Falls where
  T : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → Hs.T.Coin → Set (Rho L.offline.shape)
  Lk : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → Hs.Lk.Coin → Set (Rho L.link.shape)
  B : I × L.EncodingRandomness × L.OutOfDomainSeed × ℕ → X × L.Rec → Hs.B.Coin → Set (Rho L.onlineBatch.loc.shape)

/-- No fall. -/
def Falls.none : Falls Hs := ⟨fun _ _ _ => ∅, fun _ _ _ => ∅, fun _ _ _ => ∅⟩

/-- The records' strategies; κ: their three coins. -/
def ThreeProvers.strats : Strats L (Hs.T.Coin × Hs.Lk.Coin × Hs.B.Coin) where
  T := fun i r e κ => Hs.T.strat (i, r, e) (L.recOf i r e) κ.1
  Lk := fun i a b κ => Hs.Lk.strat (i, a, b) (L.recOf i a.1 a.2, L.recOf i b.1 b.2) κ.2.1
  B := fun i r e x n κ => Hs.B.strat (i, r, e, n) (x, L.recOf i r e) κ.2.2

variable (F : Falls Hs)

/-- The sets, at the three coins κ: the seeds that are set aside at each table; each withheld set
with the fall at the record's coin. -/
def ThreeProvers.bads (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (i : I) (r₁ r₂ : L.EncodingRandomness) (x : X) (n : ℕ)
    (κ : Hs.T.Coin × Hs.Lk.Coin × Hs.B.Coin) : Bads L where
  Z₁ := Z i r₁
  Z₂ := Z i r₂
  T := fun e => Hs.T.withheld (i, r₁, e) (L.recOf i r₁ e) ∪ F.T (i, r₁, e) (L.recOf i r₁ e) κ.1
  Lk := fun e e' =>
    Hs.Lk.withheld (i, (r₁, e), (r₂, e')) (L.recOf i r₁ e, L.recOf i r₂ e') ∪
      F.Lk (i, (r₁, e), (r₂, e')) (L.recOf i r₁ e, L.recOf i r₂ e') κ.2.1
  B := fun e =>
    Hs.B.withheld (i, r₂, e, n) (x, L.recOf i r₂ e) ∪ F.B (i, r₂, e, n) (x, L.recOf i r₂ e) κ.2.2

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- **What is asked of the three records and the falls: the conditional form.** Yes: the true
instances. Z: the seeds that are set aside. -/
structure HonFit (Yes : I → X → Prop) (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (ζ pT pL pO : ℝ≥0∞) : Prop where
  /-- the external strings are the encoded index -/
  extT : ∀ i r e, Hs.T.ext (i, r, e) = L.encodeIndex i r
  extL : ∀ i r e r' e', Hs.Lk.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')
  extB : ∀ i r e n, Hs.B.ext (i, r, e, n) = L.encodeIndex i r
  /-- withheld set and fall together do not hang on the test bits -/
  whT : ∀ w x c ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ Hs.T.withheld w x ∪ F.T w x c →
    ρ ∈ Hs.T.withheld w x ∪ F.T w x c
  whL : ∀ w x c ρ, RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ Hs.Lk.withheld w x ∪ F.Lk w x c →
    ρ ∈ Hs.Lk.withheld w x ∪ F.Lk w x c
  whB : ∀ w x c ρ,
    RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ Hs.B.withheld w x ∪ F.B w x c →
      ρ ∈ Hs.B.withheld w x ∪ F.B w x c
  /-- acceptance outside the withheld set and the fall at the coin, where all tests are passed,
  whatever the nonces, at seeds that are not set aside -/
  accT : ∀ i x r e c, Yes i x → e ∉ Z i r →
    AccLaw (batTC L aT) (wTC W) (L.recOf i r e) (Hs.T.ext (i, r, e))
      (Hs.T.strat (i, r, e) (L.recOf i r e) c)
      (Hs.T.withheld (i, r, e) (L.recOf i r e) ∪ F.T (i, r, e) (L.recOf i r e) c)
  accL : ∀ i x r e r' e' c, Yes i x → e ∉ Z i r → e' ∉ Z i r' → AccLaw (batLC L aL) (wLC W)
    (L.recOf i r e, L.recOf i r' e') (Hs.Lk.ext (i, (r, e), (r', e')))
    (Hs.Lk.strat (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c)
    (Hs.Lk.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      F.Lk (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c)
  accB : ∀ i x r e n c, Yes i x → e ∉ Z i r →
    AccLaw L.onlineBatch (wBC W) (x, L.recOf i r e) (Hs.B.ext (i, r, e, n))
      (Hs.B.strat (i, r, e, n) (x, L.recOf i r e) c)
      (Hs.B.withheld (i, r, e, n) (x, L.recOf i r e) ∪ F.B (i, r, e, n) (x, L.recOf i r e) c)
  /-- the measures: of the seeds that are set aside, under the wire's map from uniform digests; of
  withheld set and fall together, AT EACH FIXED COIN -/
  prZ : ∀ i x r, Yes i x → pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Z i r} ≤ ζ
  prT : ∀ i x r e c, Yes i x →
    prRho (Hs.T.withheld (i, r, e) (L.recOf i r e) ∪ F.T (i, r, e) (L.recOf i r e) c) ≤ pT
  prL : ∀ i x r e r' e' c, Yes i x →
    prRho (Hs.Lk.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      F.Lk (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c) ≤ pL
  prB : ∀ i x r e n c, Yes i x →
    prRho (Hs.B.withheld (i, r, e, n) (x, L.recOf i r e) ∪
      F.B (i, r, e, n) (x, L.recOf i r e) c) ≤ pO
  /-- the session's plain parts hold the copy's number THAT ITS RECORD WAS HANDED -/
  num : ∀ i x r e n c (τ : Tr L.onlineBatch.loc.shape), Yes i x →
    Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh
      ((Hs.B.strat (i, r, e, n) (x, L.recOf i r e) c).run τ.rho).1 τ → S.num n τ.plains = true

variable {Hs F W S}

/-- What is shown at a larger set of true instances serves at every smaller one. -/
theorem HonFit.mono {Yes Yes' : I → X → Prop} {Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (h : HonFit Hs F W S Yes Z ζ pT pL pO) (hY : ∀ i x, Yes' i x → Yes i x) :
    HonFit Hs F W S Yes' Z ζ pT pL pO where
  extT := h.extT
  extL := h.extL
  extB := h.extB
  whT := h.whT
  whL := h.whL
  whB := h.whB
  accT := fun i x r e c y => h.accT i x r e c (hY i x y)
  accL := fun i x r e r' e' c y => h.accL i x r e r' e' c (hY i x y)
  accB := fun i x r e n c y => h.accB i x r e n c (hY i x y)
  prZ := fun i x r y => h.prZ i x r (hY i x y)
  prT := fun i x r e c y => h.prT i x r e c (hY i x y)
  prL := fun i x r e r' e' c y => h.prL i x r e r' e' c (hY i x y)
  prB := fun i x r e n c y => h.prB i x r e n c (hY i x y)
  num := fun i x r e n c τ y => h.num i x r e n c τ (hY i x y)

/-- **The accept laws, at the three records and the falls at the draw's coins.** -/
theorem accAt_of_honest {Yes : I → X → Prop} {Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (h : HonFit Hs F W S Yes Z ζ pT pL pO) (i : I) (r₁ : L.EncodingRandomness) (x : X)
    (d : Draw lam L Bd aT aL (Hs.T.Coin × Hs.Lk.Coin × Hs.B.Coin)) (hY : Yes i x) :
    AccAt W S Hs.strats i r₁ x d (Hs.bads F Z i r₁ d.r x d.n d.κ) where
  T := fun e₁ h1 => by
    have a := h.accT i x r₁ e₁ d.κ.1 hY h1
    rw [h.extT] at a
    exact a
  Lk := fun e₁ e₂ h1 h2 => by
    have a := h.accL i x r₁ e₁ d.r e₂ d.κ.2.1 hY h1 h2
    rw [h.extL] at a
    exact a
  B := fun e₂ h2 => by
    have a := h.accB i x d.r e₂ d.n d.κ.2.2 hY h2
    rw [h.extB] at a
    exact a
  num := fun e₂ τ hp => h.num i x d.r e₂ d.n d.κ.2.2 τ hY hp

/-- **The sets' measures, at each fixed triple of coins.** -/
theorem small_of_honest {Yes : I → X → Prop} {Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (h : HonFit Hs F W S Yes Z ζ pT pL pO) (i : I) (r₁ r₂ : L.EncodingRandomness) (x : X) (n : ℕ)
    (κ : Hs.T.Coin × Hs.Lk.Coin × Hs.B.Coin) (hY : Yes i x) :
    SetsSmall W S (Hs.bads F Z i r₁ r₂ x n κ) ζ ζ pT pL pO where
  z₁ := h.prZ i x r₁ hY
  z₂ := h.prZ i x r₂ hY
  T := fun e => (pr_mono _ fun ρ hρ => h.whT _ _ κ.1 ρ hρ).trans (h.prT i x r₁ e κ.1 hY)
  Lk := fun e e' =>
    (pr_mono _ fun ρ hρ => h.whL _ _ κ.2.1 ρ hρ).trans (h.prL i x r₁ e r₂ e' κ.2.1 hY)
  B := fun e => (pr_mono _ fun ρ hρ => h.whB _ _ κ.2.2 ρ hρ).trans (h.prB i x r₂ e n κ.2.2 hY)

end OnBytes.Prover
