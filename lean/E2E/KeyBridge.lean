-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyBridge.lean: FROM SENTENCES ON THE KEY FILE's HONEST PROVER TO WHAT TWO LISTS OF PREMISES ASK
OF IT, each clause in that list's own words, AT ONE VALUE. By calls. NOTHING IS CLAIMED OF ANY
PROVER: every sentence stands here as a HYPOTHESIS BY NAME, and none of them is proved here.

The two lists. `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean, OfRecs.lean) is the list of
premises of a statement on the compiled argument with the whole key published
(Johnson/WholeKey/Statement.lean). `OnBytes.Prover.HonFit` (Johnson/Prover/All/OfHonest.lean) is
what the prover of a whole request asks of three honest provers, toward a statement on acceptance.
What follows from either list is those files' matter.

The setting. L: an object with OOD samples. hT: an honest prover of the key file's protocol
`L.offline`, A FREE LETTER. Its private input is (index, committer's randomness, OOD seed). THE
INSTANCE IS THE OOD SAMPLE: there is no request and no copy's number. hL, Fm: the link's honest
prover and the family of one request's honest provers (E2E/HonestFamily.lean): free letters. The
one value is `proversOf hT hL Fm` (E2E/BridgePrivacy.lean), whose first field is hT by unfolding.
W: a wiring, A FREE LETTER THAT BEARS NO LAW HERE.
Two words. A fall: a set of verifier randomness, at a private input, an instance and a coin of the
prover's, outside which (and outside the abort set) acceptance is asked. An OOD seed that is set
aside: a member of Z i r, at which `HonFit` asks no acceptance.

Hypotheses by name. (`SimT`, `TiedT`, `FallT`: the types of a simulator, of "tied" and of a family
of falls at the key file.)
  `OneExact hT sim Tied`: at tied inputs, at EVERY verifier randomness outside the part of the abort
    set that may hang on the private input, the honest output IS the named simulator's.
  `ValidTied Tied ok Gs`: every index in the range ok, with every committer's randomness and every
    OOD seed of Gs, is tied to its own OOD sample.
  `ExtIsEnc hT`: the external string is the encoded index.
  `BadZero hT W`, `HidZero hT W`, `FallZero hT W FT`: if verifier randomness with its proof-of-work
    test bits set to 0 lies in the public part of the abort set, in the rest of it, in a fall, then
    so does the verifier randomness itself (for a fall: or it lies in the abort set). One way.
  `HidSmall hT Tied z`, `BadSmall hT zB`, `FallSmall hT FT Tied pF`: three measures; the fall's AT
    EACH FIXED COIN.
  `RunValsAt hT ok pv rv`, `RunForm hT okV rv`: read off the honest run's plain parts, outside the
    abort set, the run values are what is read off the coin; each coin's run value has the right
    form.
  `AccAtTied hT W FT Tied`: at tied inputs and every coin: the accept law (`AccLaw`) outside the
    abort set and the fall at the coin.
  `Sentences …`: all of these together, as one structure, with TWO relations: Tied, at the OOD seeds
    of Gs, for the simulator, the accept law and the fall's measure; TiedM, at ALL OOD seeds, for
    the measure of the stops that hang on the private input.
  `guardT Z FT`: the fall FT, made empty at the OOD seeds that are set aside (`guardT_eq`: elsewhere
    it is FT).

What is shown, and what each is worth.
  THE HYPOTHESIS IS THE CLAUSE (`:= h`): `extT_of` (`ExtEnc.T`, `HonFit.extT`) · `runValsT_of`
    (`RunVals.T`) · `okT_of` (`CoinsFit.okT`).
  NOTHING IS WANTED: `enumOf`, `enumOf_ok` (`CoinsFit.kT`: every finite non-empty type has an
    enumeration that lists each member once) · `decT_of` (`Decs.T`, from two functions to Bool; any
    decision would do, also the one that classical logic gives).
  WITH A STEP: **`goodT_of_exact`** (`Sims.Good.T` at error 0: the set that it measures is empty) ·
    **`stopsT_of_small`** (`StopsSmall.T` at z) · `whT_of` (`HonFit.whT`) · **`accT_of`**
    (`HonFit.accT`: Z IS SPENT) · **`prT_of`** (`HonFit.prT` at zB + z + pF, at every OOD seed).
  The lists' own structures at the one value: `extAt_of`, `runVals_of`, `good_of_exact`,
    `stops_of_small`, `decs_of`, `honFit_of`: the key file's clauses from the above; the link's and
    the session's are taken from a value of the same structure at any other key file's prover (they
    do not read it).
  `Sentences` suffices: `Sentences.good`, `Sentences.stops`, `Sentences.honFit`.
A member of all hypotheses together.
  `idleT`, **`sentences_idle`**: a prover whose public abort set is everything, with no fall, meets
    `Sentences` at z = 0, zB = 1, pF = 0. IDLE: see the limits.

Limits.
- CONDITIONAL THROUGHOUT. `OneExact` and `AccAtTied` are shown of no prover but the idle one. That
  prover never speaks, and no verifier is said to accept anything. It shows that the hypotheses do
  not contradict each other AT zB = 1: below a sum of 1 no member is shown.
- "ERROR 0" IS NO RESULT BY ITSELF: `PremW` has a seat for the measure of the stops that hang on the
  private input, and NONE for the public stops' measure, nor for the share of runs in which a
  verifier's test rejects. It is to be said only beside what is shown on acceptance OF THE SAME hT.
- AND THAT GUARDS ONLY BESIDE THE WIRING's LAWS. W is a free letter here. At a wiring one of whose
  tests no verifier randomness passes, `AccLaw` asks nothing, and a prover that sends fixed
  messages, with empty abort set and no fall, meets all hypotheses at 0, 0, 0. `PremW` asks the
  wiring's laws in a field of its own (`wires`); `HonFit` does not.
- THE REQUEST IN `accT` AND `prT` IS A GUARD ALONE ("the index has a true instance"): `accT_of` and
  `prT_of` ask that it puts the index into the range ok. Where ok or Gs holds nothing, the clauses
  ask nothing.
- THE FALL's SET HANGS ON THE PROVER's COIN. A bound on its measure at each fixed coin bounds the
  share over verifier randomness and coins together; it does not bound the set of verifier
  randomness at which SOME coin's run falls. So a statement of completeness takes the number as an
  error over verifier randomness and coins together; the fall is a second set, which reads the coin,
  beside the abort set, and is not folded into it: the form of `OnBytes.Prover.HonFit` (its accept
  laws outside the abort set and the fall at that coin; its measures at each fixed coin).
- `prT` IS ASKED AT EVERY OOD SEED, also at those that are set aside. There the guarded fall is
  empty, and the abort set's measure is still asked: so `HidSmall` is taken at a relation that
  covers all OOD seeds. No clause of `HonFit` sets a committer's randomness aside.
- WHICH RUN VALUE THE KEY FILE's PROVER HAS IS NOT SAID: RV, pv, rv, okV are letters. `PremW` has
  one type of run values and one test on their form for all three protocols. Constant pv and rv meet
  `RunValsAt`.
- Of `CoinsFit` two clauses are treated (kT, okT). The others that bear a T speak of the compiled
  run's coins, of the wires and of numbers.
- That any written prover is of the type of hT at the object in view is not said here.
- Nothing on what a view shows is claimed.

`Sentences` may be read as stating a goal, that is, what is to be proved of the key file's honest
prover. It counts as none.

-/
import E2E.BridgeAccept

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.KeyBridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open AtPublicFiles.Bridge (Family proversOf fallsOf FallB)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}

/-- The type of the key file's simulator (`Sims.T`). -/
abbrev SimT (L : HolographicProtocol I X) : Type :=
  L.Rec → (ρ : Rho L.offline.shape) → ((oneExternalString L.wordLength L.Symbol).Pos → Option (oneExternalString L.wordLength L.Symbol).Sym) →
    PMF (Option (DView L.offline))

/-- The type of "tied": a private input and an OOD sample. -/
abbrev TiedT (L : HolographicProtocol I X) : Type := I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → Prop

/-- The type of a family of falls of a key file's prover (`Falls.T`). -/
abbrev FallT (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)) : Type :=
  I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → hT.Coin → Set (Rho L.offline.shape)

/-! ## 1. The hypotheses, by name -/

section
variable (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))

/-- **Hypothesis by name**: at tied inputs, at every verifier randomness outside `Hid`, the honest
output is the named simulator's. -/
def OneExact (sim : SimT L) (Tied : TiedT L) : Prop :=
  ∀ w x, Tied w x → ∀ ρ, ρ ∉ hT.Hid w x →
    hT.output w x ρ = sim x ρ (L.offline.extAns x ρ (hT.ext w))

/-- **Hypothesis by name**: every index in range is tied to its own OOD sample, at every committer's
randomness and every OOD seed of Gs. -/
def ValidTied (Tied : TiedT L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) : Prop :=
  ∀ i r e, ok i → Gs e → Tied (i, r, e) (L.recOf i r e)

/-- **Hypothesis by name**: the external string is the encoded index. -/
def ExtIsEnc : Prop := ∀ i r e, hT.ext (i, r, e) = L.encodeIndex i r

/-- **Hypothesis by name**: the measure of `Hid` at tied inputs. -/
def HidSmall (Tied : TiedT L) (z : ℝ≥0∞) : Prop := ∀ w x, Tied w x → prRho (hT.Hid w x) ≤ z

/-- **Hypothesis by name**: the public stops' measure. -/
def BadSmall (zB : ℝ≥0∞) : Prop := prRho hT.Bad ≤ zB

/-- **Hypothesis by name**: a fall's measure at tied inputs, at each fixed coin. -/
def FallSmall (FT : FallT hT) (Tied : TiedT L) (pF : ℝ≥0∞) : Prop :=
  ∀ w x c, Tied w x → prRho (FT w x c) ≤ pF

/-- **Hypothesis by name**: read off the honest run's plain parts, at every verifier randomness
outside the abort set, the run values are what is read off the coin. It is the clause T of
`RunVals`, in general letters. -/
def RunValsAt (ok : I → Prop) {RV : Type} (pv : Plains L.offline.shape → RV) (rv : hT.Coin → RV) :
    Prop :=
  ∀ i r e κ ρ, ok i → ρ ∉ hT.withheld (i, r, e) (L.recOf i r e) →
    pv ((hT.strat (i, r, e) (L.recOf i r e) κ).run ρ).1.plains = rv κ

/-- **Hypothesis by name**: each coin's run value has the right form. -/
def RunForm {RV : Type} (okV : RV → Prop) (rv : hT.Coin → RV) : Prop := ∀ κ, okV (rv κ)

/-- A fall, made empty at the OOD seeds that are set aside. The guard reads the private input and no
verifier randomness. -/
def guardT (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (FT : FallT hT) : FallT hT :=
  fun w x c => {ρ | w.2.2 ∉ Z w.1 w.2.1 ∧ ρ ∈ FT w x c}

variable {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- **Hypothesis by name**: the public part of the abort set does not hang on the proof-of-work test
bits, one way. -/
def BadZero : Prop := ∀ ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ hT.Bad → ρ ∈ hT.Bad

/-- **Hypothesis by name**: the like of `Hid`. -/
def HidZero : Prop :=
  ∀ w x ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ hT.Hid w x → ρ ∈ hT.Hid w x

/-- **Hypothesis by name**: the like of a fall, up to the abort set. -/
def FallZero (FT : FallT hT) : Prop :=
  ∀ w x c ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ FT w x c →
    ρ ∈ hT.withheld w x ∪ FT w x c

/-- **Hypothesis by name**: the accept law at tied inputs, at every coin. -/
def AccAtTied (FT : FallT hT) (Tied : TiedT L) : Prop :=
  ∀ w x c, Tied w x →
    AccLaw (batTC L aT) (wTC W) x (hT.ext w) (hT.strat w x c) (hT.withheld w x ∪ FT w x c)

/-- **All hypotheses together.** Tied: at the OOD seeds of Gs. TiedM: at all OOD seeds. A member:
`sentences_idle`. -/
structure Sentences (sim : SimT L) (Tied TiedM : TiedT L) (FT : FallT hT) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) {RV : Type} (pv : Plains L.offline.shape → RV) (rv : hT.Coin → RV)
    (okV : RV → Prop) (z zB pF : ℝ≥0∞) : Prop where
  exact : OneExact hT sim Tied
  tied : ValidTied Tied ok Gs
  tiedAll : ValidTied TiedM ok fun _ => True
  ext : ExtIsEnc hT
  badZero : BadZero hT W
  hidZero : HidZero hT W
  fallZero : FallZero hT W FT
  hidSmall : HidSmall hT TiedM z
  badSmall : BadSmall hT zB
  fallSmall : FallSmall hT FT Tied pF
  runVals : RunValsAt hT ok pv rv
  runForm : RunForm hT okV rv
  acc : AccAtTied hT W FT Tied

end

/-! ## 2. The clauses of `PremW` on the key file's prover -/

section
variable (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed))

/-- The clause T of `ExtEnc`, and `HonFit.extT`. The hypothesis is the clause. -/
theorem extT_of (h : ExtIsEnc hT) : ∀ i r e, (proversOf hT hL Fm).T.ext (i, r, e) = L.encodeIndex i r := h

/-- The clause T of `RunVals`, in general letters. The hypothesis is the clause. -/
theorem runValsT_of {ok : I → Prop} {RV : Type} {pv : Plains L.offline.shape → RV}
    {rv : hT.Coin → RV} (h : RunValsAt hT ok pv rv) :
    ∀ i r e κ ρ, ok i → ρ ∉ (proversOf hT hL Fm).T.withheld (i, r, e) (L.recOf i r e) →
      pv (((proversOf hT hL Fm).T.strat (i, r, e) (L.recOf i r e) κ).run ρ).1.plains = rv κ := h

/-- **The list's own structure `RunVals`**, at any value a of its letters: the key file's clause
from `RunValsAt` at a's own key file's prover and its functions pvT, rvT; the other two are premises
in the list's own words. -/
theorem runVals_of {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (a : AtRecs lam L Bd aT aL) (ok : I → Prop) (h : RunValsAt a.Hs.T ok a.pvT a.rvT)
    (hLk : ∀ i u u' κ ρ, ok i →
      ρ ∉ a.Hs.Lk.withheld (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) →
      a.pvL ((a.Hs.Lk.strat (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) κ).run ρ).1.plains =
        a.rvL κ)
    (hB : ∀ i r e n x κ ρ, ok i → ρ ∉ a.Hs.B.withheld (i, r, e, n) (x, L.recOf i r e) →
      a.pvB ((a.Hs.B.strat (i, r, e, n) (x, L.recOf i r e) κ).run ρ).1.plains = a.rvB κ) :
    RunVals a ok :=
  ⟨h, hLk, hB⟩

/-- The clause `okT` of `CoinsFit`, in general letters. The hypothesis is the clause. -/
theorem okT_of {RV : Type} {okV : RV → Prop} {rv : hT.Coin → RV} (h : RunForm hT okV rv) :
    ∀ κ : (proversOf hT hL Fm).T.Coin, okV (rv κ) := h

variable {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- **The clause T of `Sims.Good` at error 0**: the set is empty. No law on the wires and no
blindness is spent: `OneExact` speaks at every verifier randomness, so at those with the test bits
0. NO RESULT BY ITSELF: `OneExact` is a hypothesis, and the public stops' measure has no seat in
that clause (the head's limits). -/
theorem goodT_of_exact {sim : SimT L} {Tied : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop}
    (h1 : OneExact hT sim Tied) (h2 : ValidTied Tied ok Gs) (he : ExtIsEnc hT) :
    ∀ i r e, ok i → Gs e →
      pr (unif (Rho L.offline.shape))
        {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∉
            (proversOf hT hL Fm).T.Hid (i, r, e) (L.recOf i r e) ∧
          (proversOf hT hL Fm).T.output (i, r, e) (L.recOf i r e)
            (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ) ≠
          sim (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ)
            (L.offline.extAns (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ)
              (L.encodeIndex i r))} ≤ 0 := by
  intro i r e hi hg
  refine le_of_eq (pr_eq_zero_of_forall_not_mem _ fun ρ _ hρ => hρ.2 ?_)
  have h := h1 (i, r, e) (L.recOf i r e) (h2 i r e hi hg) _ hρ.1
  rw [he i r e] at h
  exact h

/-- **The clause T of `StopsSmall`**: by `HidZero` the set that it measures lies in the set that
`HidSmall` measures. -/
theorem stopsT_of_small {Tied : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {z : ℝ≥0∞}
    (hz : HidSmall hT Tied z) (h2 : ValidTied Tied ok Gs) (h0 : HidZero hT W) :
    ∀ i r e, ok i → Gs e →
      pr (unif (Rho L.offline.shape))
        {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈
          (proversOf hT hL Fm).T.Hid (i, r, e) (L.recOf i r e)} ≤ z :=
  fun i r e hi hg =>
    (pr_mono _ fun ρ hρ => h0 (i, r, e) (L.recOf i r e) ρ hρ).trans
      (hz (i, r, e) (L.recOf i r e) (h2 i r e hi hg))

/-- The clause T of `Decs`, from two functions to Bool: whether given verifier randomness lies in
the public part of the abort set, and in the rest. -/
def decT_of (bad : Rho L.offline.shape → Bool)
    (hid : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → Rho L.offline.shape → Bool)
    (hb : ∀ ρ, ρ ∈ hT.Bad ↔ bad ρ = true) (hh : ∀ w x ρ, ρ ∈ hT.Hid w x ↔ hid w x ρ = true) :
    ∀ w x ρ, Decidable (ρ ∈ (proversOf hT hL Fm).T.withheld w x) := fun w x ρ =>
  decidable_of_iff (bad ρ = true ∨ hid w x ρ = true) (or_congr (hb ρ).symm (hh w x ρ).symm)

/-! ### The list's own structures at the one value -/

/-- `ExtEnc`: the link's and the session's clauses are premises in the list's own words. -/
theorem extAt_of (h : ExtIsEnc hT)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r'))
    (eB : ∀ i r e n, (proversOf hT hL Fm).B.ext (i, r, e, n) = L.encodeIndex i r) :
    ExtEnc (proversOf hT hL Fm) :=
  ⟨h, eL, eB⟩

/-- `Sims.Good`, with the key file's number 0. NO RESULT BY ITSELF: as at `goodT_of_exact`. -/
theorem good_of_exact {Sm : Sims L} {Tied : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop}
    {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞} {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    (g : Sm.Good (proversOf hT' hL Fm) W ok Gs Ryes zT zL zO) (h1 : OneExact hT Sm.T Tied)
    (h2 : ValidTied Tied ok Gs) (he : ExtIsEnc hT) :
    Sm.Good (proversOf hT hL Fm) W ok Gs Ryes 0 zL zO :=
  ⟨goodT_of_exact hT hL Fm W h1 h2 he, g.Lk, g.B⟩

/-- `StopsSmall`, with the key file's number z. -/
theorem stops_of_small {Tied : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop}
    {Ryes : I → X → Prop} {pT pL pO z : ℝ≥0∞} {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    (s : StopsSmall (proversOf hT' hL Fm) W ok Gs Ryes pT pL pO) (hz : HidSmall hT Tied z)
    (h2 : ValidTied Tied ok Gs) (h0 : HidZero hT W) :
    StopsSmall (proversOf hT hL Fm) W ok Gs Ryes z pL pO :=
  ⟨stopsT_of_small hT hL Fm W hz h2 h0, s.Lk, s.B⟩

/-- `Decs`. -/
def decs_of {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)} (d : Decs (proversOf hT' hL Fm))
    (dT : ∀ w x ρ, Decidable (ρ ∈ (proversOf hT hL Fm).T.withheld w x)) :
    Decs (proversOf hT hL Fm) :=
  ⟨dT, d.Lk, d.B⟩

end

/-- An enumeration of a finite non-empty type. -/
def enumOf (β : Type) [Fintype β] [Nonempty β] : Enum β :=
  ⟨Fintype.card β - 1,
    ((finCongr (Nat.sub_add_cancel (Fintype.card_pos (α := β)))).trans (Fintype.equivFin β).symm)⟩

/-- **It lists each member once**: the clause `kT` of `CoinsFit` can be met at every honest prover,
at `enumOf hT.Coin`. -/
theorem enumOf_ok (β : Type) [Fintype β] [Nonempty β] : (enumOf β).OK :=
  ((finCongr (Nat.sub_add_cancel (Fintype.card_pos (α := β)))).trans
    (Fintype.equivFin β).symm).bijective

/-! ## 3. The clauses of `HonFit` on the key file's prover -/

section
variable (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)) (FT : FallT hT)
  (FL : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → hL.Coin → Set (Rho L.link.shape))
  (FB : FallB Fm) (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- At an OOD seed that is not set aside the guarded fall is the fall. -/
theorem guardT_eq {i : I} {r : L.EncodingRandomness} {e : L.OutOfDomainSeed} (he : e ∉ Z i r) (x : L.Rec) (c : hT.Coin) :
    guardT hT Z FT (i, r, e) x c = FT (i, r, e) x c :=
  Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- The clause `whT`, at the guarded fall. -/
theorem whT_of (hb : BadZero hT W) (hh : HidZero hT W) (hf : FallZero hT W FT) :
    ∀ w x c ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈
        (proversOf hT hL Fm).T.withheld w x ∪ (fallsOf hT hL Fm (guardT hT Z FT) FL FB).T w x c →
      ρ ∈ (proversOf hT hL Fm).T.withheld w x ∪
        (fallsOf hT hL Fm (guardT hT Z FT) FL FB).T w x c := by
  rintro w x c ρ ((h | h) | ⟨hz, h⟩)
  · exact Or.inl (Or.inl (hb ρ h))
  · exact Or.inl (Or.inr (hh w x ρ h))
  · exact (hf w x c ρ h).elim Or.inl fun h' => Or.inr ⟨hz, h'⟩

/-- **The clause `accT`, at the guarded fall. Z is spent**: hg says that an OOD seed which is not
set aside lies in Gs. The request x is a guard alone: hy says that an index with a true instance is
in range. -/
theorem accT_of {Tied : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Yes : I → X → Prop}
    (h : AccAtTied hT W FT Tied) (h2 : ValidTied Tied ok Gs) (hy : ∀ i x, Yes i x → ok i)
    (hg : ∀ i r e, e ∉ Z i r → Gs e) :
    ∀ i x r e c, Yes i x → e ∉ Z i r →
      AccLaw (batTC L aT) (wTC W) (L.recOf i r e) ((proversOf hT hL Fm).T.ext (i, r, e))
        ((proversOf hT hL Fm).T.strat (i, r, e) (L.recOf i r e) c)
        ((proversOf hT hL Fm).T.withheld (i, r, e) (L.recOf i r e) ∪
          (fallsOf hT hL Fm (guardT hT Z FT) FL FB).T (i, r, e) (L.recOf i r e) c) := by
  intro i x r e c hx he
  show AccLaw (batTC L aT) (wTC W) (L.recOf i r e) (hT.ext (i, r, e))
    (hT.strat (i, r, e) (L.recOf i r e) c)
    (hT.withheld (i, r, e) (L.recOf i r e) ∪ guardT hT Z FT (i, r, e) (L.recOf i r e) c)
  rw [guardT_eq hT FT Z he]
  exact h (i, r, e) (L.recOf i r e) c (h2 i r e (hy i x hx) (hg i r e he))

/-- **The clause `prT`, at the guarded fall**, at the sum of the three measures, at every OOD seed:
at one that is set aside the guarded fall is empty; the abort set's measure is asked there too. -/
theorem prT_of {Tied TiedM : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Yes : I → X → Prop}
    {zB z pF : ℝ≥0∞} (hb : BadSmall hT zB) (hz : HidSmall hT TiedM z)
    (hf : FallSmall hT FT Tied pF) (h2 : ValidTied Tied ok Gs)
    (h2m : ValidTied TiedM ok fun _ => True) (hy : ∀ i x, Yes i x → ok i)
    (hg : ∀ i r e, e ∉ Z i r → Gs e) :
    ∀ i x r e c, Yes i x →
      prRho ((proversOf hT hL Fm).T.withheld (i, r, e) (L.recOf i r e) ∪
        (fallsOf hT hL Fm (guardT hT Z FT) FL FB).T (i, r, e) (L.recOf i r e) c) ≤
          zB + z + pF := by
  intro i x r e c hx
  refine (pr_union_le _ _ _).trans (add_le_add ((pr_union_le _ _ _).trans (add_le_add hb ?_)) ?_)
  · exact hz (i, r, e) (L.recOf i r e) (h2m i r e (hy i x hx) trivial)
  · show prRho (guardT hT Z FT (i, r, e) (L.recOf i r e) c) ≤ pF
    by_cases he : e ∈ Z i r
    · exact (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h.1 he)).trans (zero_le _)
    · rw [guardT_eq hT FT Z he]
      exact hf (i, r, e) (L.recOf i r e) c (h2 i r e (hy i x hx) (hg i r e he))

/-- **`HonFit` at the one value, at the guarded fall**: its four clauses on the key file's prover
from the sentences; the other ten from a value of the same structure at any other key file's prover
and falls. -/
theorem honFit_of (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) {Tied TiedM : TiedT L} {ok : I → Prop}
    {Gs : L.OutOfDomainSeed → Prop} {Yes : I → X → Prop} {ζ pT' pL pO zB z pF : ℝ≥0∞}
    {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)} {FT' : FallT hT'}
    (g : HonFit (proversOf hT' hL Fm) (fallsOf hT' hL Fm FT' FL FB) W S Yes Z ζ pT' pL pO)
    (he : ExtIsEnc hT) (hbz : BadZero hT W) (hhz : HidZero hT W) (hfz : FallZero hT W FT)
    (ha : AccAtTied hT W FT Tied) (h2 : ValidTied Tied ok Gs)
    (h2m : ValidTied TiedM ok fun _ => True) (hy : ∀ i x, Yes i x → ok i)
    (hg : ∀ i r e, e ∉ Z i r → Gs e) (hb : BadSmall hT zB) (hz : HidSmall hT TiedM z)
    (hf : FallSmall hT FT Tied pF) :
    HonFit (proversOf hT hL Fm) (fallsOf hT hL Fm (guardT hT Z FT) FL FB) W S Yes Z ζ (zB + z + pF)
      pL pO where
  extT := he
  extL := g.extL
  extB := g.extB
  whT := whT_of hT hL Fm FT FL FB Z W hbz hhz hfz
  whL := g.whL
  whB := g.whB
  accT := accT_of hT hL Fm FT FL FB Z W ha h2 hy hg
  accL := g.accL
  accB := g.accB
  prZ := g.prZ
  prT := prT_of hT hL Fm FT FL FB Z hb hz hf h2 h2m hy hg
  prL := g.prL
  prB := g.prB
  num := g.num

/-! ### `Sentences` suffices -/

variable {hT FT W}
variable {Tied TiedM : TiedT L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {RV : Type}
  {pv : Plains L.offline.shape → RV} {rv : hT.Coin → RV} {okV : RV → Prop} {z zB pF : ℝ≥0∞}

/-- `Sims.Good` from `Sentences` at the list's own simulator. NO RESULT BY ITSELF. -/
theorem Sentences.good {Sm : Sims L}
    (h : Sentences hT W Sm.T Tied TiedM FT ok Gs pv rv okV z zB pF) {Ryes : I → X → Prop}
    {zT zL zO : ℝ≥0∞} {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    (g : Sm.Good (proversOf hT' hL Fm) W ok Gs Ryes zT zL zO) :
    Sm.Good (proversOf hT hL Fm) W ok Gs Ryes 0 zL zO :=
  good_of_exact hT hL Fm W g h.exact h.tied h.ext

/-- `StopsSmall` from `Sentences`. -/
theorem Sentences.stops {sim : SimT L}
    (h : Sentences hT W sim Tied TiedM FT ok Gs pv rv okV z zB pF) {Ryes : I → X → Prop}
    {pT pL pO : ℝ≥0∞} {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    (s : StopsSmall (proversOf hT' hL Fm) W ok Gs Ryes pT pL pO) :
    StopsSmall (proversOf hT hL Fm) W ok Gs Ryes z pL pO :=
  stops_of_small hT hL Fm W s h.hidSmall (fun i r e hi _ => h.tiedAll i r e hi trivial) h.hidZero

/-- `HonFit` from `Sentences`, at the guarded fall. -/
theorem Sentences.honFit {sim : SimT L}
    (h : Sentences hT W sim Tied TiedM FT ok Gs pv rv okV z zB pF) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    {Yes : I → X → Prop} {ζ pT' pL pO : ℝ≥0∞} {hT' : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    {FT' : FallT hT'}
    (g : HonFit (proversOf hT' hL Fm) (fallsOf hT' hL Fm FT' FL FB) W S Yes Z ζ pT' pL pO)
    (hy : ∀ i x, Yes i x → ok i) (hg : ∀ i r e, e ∉ Z i r → Gs e) :
    HonFit (proversOf hT hL Fm) (fallsOf hT hL Fm (guardT hT Z FT) FL FB) W S Yes Z ζ (zB + z + pF)
      pL pO :=
  honFit_of hT hL Fm FT FL FB Z W S g h.ext h.badZero h.hidZero h.fallZero h.acc h.tied h.tiedAll hy
    hg h.badSmall h.hidSmall h.fallSmall

end

/-! ## 4. A member of all hypotheses together -/

section
variable {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- An idle prover of the key file's protocol: fixed messages; the PUBLIC abort set is everything,
the rest of the abort set is empty. -/
def idleT (L : HolographicProtocol I X) : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed) where
  Coin := Unit
  neCoin := ⟨()⟩
  ext := fun w => L.encodeIndex w.1 w.2.1
  strat := fun _ _ _ => Strat.dflt _ ()
  Bad := Set.univ
  Hid := fun _ _ => ∅

/-- **The hypotheses can be met together, at zB = 1**: at the idle prover, the simulator that shows
nothing, no fall, everything tied, every range and set of OOD seeds, run values of the type with one
member. IDLE: its output is "none" at every verifier randomness, and the accept law asks nothing of
it. -/
theorem sentences_idle (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) :
    Sentences (idleT L) W (fun _ _ _ => PMF.pure none) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ _ => ∅) ok Gs (fun _ => ()) (fun _ => ()) (fun _ => True) 0 1 0 where
  exact := fun _ _ _ _ _ => if_pos (Or.inl (Set.mem_univ _))
  tied := fun _ _ _ _ _ => trivial
  tiedAll := fun _ _ _ _ _ => trivial
  ext := fun _ _ _ => rfl
  badZero := fun _ _ => Set.mem_univ _
  hidZero := fun _ _ _ h => h
  fallZero := fun _ _ _ _ h => Or.inr h
  hidSmall := fun _ _ _ => le_of_eq (pr_empty _)
  badSmall := pr_le_one _ _
  fallSmall := fun _ _ _ _ => le_of_eq (pr_empty _)
  runVals := fun _ _ _ _ _ _ _ => rfl
  runForm := fun _ => trivial
  acc := fun _ _ _ _ _ _ _ h => absurd (Or.inl (Or.inl (Set.mem_univ _))) h

end

end AtPublicFiles.KeyBridge

#print axioms AtPublicFiles.KeyBridge.extT_of
#print axioms AtPublicFiles.KeyBridge.runValsT_of
#print axioms AtPublicFiles.KeyBridge.runVals_of
#print axioms AtPublicFiles.KeyBridge.okT_of
#print axioms AtPublicFiles.KeyBridge.goodT_of_exact
#print axioms AtPublicFiles.KeyBridge.stopsT_of_small
#print axioms AtPublicFiles.KeyBridge.extAt_of
#print axioms AtPublicFiles.KeyBridge.good_of_exact
#print axioms AtPublicFiles.KeyBridge.stops_of_small
#print axioms AtPublicFiles.KeyBridge.enumOf_ok
#print axioms AtPublicFiles.KeyBridge.guardT_eq
#print axioms AtPublicFiles.KeyBridge.whT_of
#print axioms AtPublicFiles.KeyBridge.accT_of
#print axioms AtPublicFiles.KeyBridge.prT_of
#print axioms AtPublicFiles.KeyBridge.honFit_of
#print axioms AtPublicFiles.KeyBridge.Sentences.good
#print axioms AtPublicFiles.KeyBridge.Sentences.stops
#print axioms AtPublicFiles.KeyBridge.Sentences.honFit
#print axioms AtPublicFiles.KeyBridge.sentences_idle
