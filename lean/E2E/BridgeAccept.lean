-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgeAccept.lean: what the prover of a whole request asks of three honest provers and three
families of falls (`OnBytes.Prover.HonFit`, Johnson/Prover/All/OfHonest.lean): its five clauses on
the SESSION's prover (`extB`, `whB`, `accB`, `prB`, `num`), and the structure itself, AT THE SAME
VALUE `proversOf hT hL Fm` of which E2E/BridgePrivacy.lean speaks: with proof of work in the rounds,
nothing carried up from protocols without.

WHAT KIND OF FILE THIS IS. The hypotheses below are cut after the clauses that they serve: `whB_of`,
`accB_of` and `numB_of` restate a clause at the family; `prB_of` is a bound for a union. So this
file by itself tests no fit with any written prover. What it adds: the number goes in front; the OOD
seeds that are set aside are SPENT; a term of `HonFit` is built. The fall's set of a written honest
side, and that it does not hang on the test bits, are not this file's. THE ACCEPT LAW ITSELF
(`AccAtTied`) IS SHOWN OF NO PROVER HERE.

  `guardFall Z FB`: a family of falls that is EMPTY at the OOD seeds that are set aside. No
    acceptance is owed there, and the clause on the measure is asked there too: so a fall that is
    laid there costs measure for nothing.
  `fallsOf FT FL FB`: three families of falls at `proversOf hT hL Fm`.
Hypotheses by name.
  `ValidTiedZ TiedA Yes Z`: every true instance is tied, at every committer's randomness and number,
    AT THE OOD SEEDS THAT ARE NOT SET ASIDE. (Z reads index and committer's randomness, as in
    `HonFit`.)
  `AccAtTied Fm FB W TiedA`: at such inputs and every coin: the accept law of one request's protocol
    (`AccLaw`), outside the abort set and the fall at the coin.
  `WithheldZero Fm W`, `FallZero FB W`: neither the abort set nor a fall hangs on the test bits.
  `BadSmall Fm zB`; `HidSmall Fm TiedM z` with `ValidTied TiedM all all Yes`: AT ALL OOD SEEDS, the
    set-aside ones too: that part of the abort set is the prover's own and no fall can be emptied in
    its stead.
  `FallSmall FB TiedA pF`: AT EACH FIXED COIN, at the inputs of TiedA: so at the seeds that are not
    set aside alone IF TiedA SHUTS THE OTHERS OUT (`ValidTiedZ` lets it).
What is shown.
  `whB_of`, **`accB_of`**, **`prB_of`** (at zB + z + pF), `numB_of`, with `extB_of`
    (E2E/BridgePrivacy.lean).
  `NineFit`: the nine clauses of `HonFit` that do not read the session's prover, in its own words,
    as a structure; `NineFit.of_honFit`: from a value of `HonFit` at any other family.
  **`honFit_of`**: `HonFit (proversOf hT hL Fm) (fallsOf … (guardFall Z FB)) W S Yes Z ζ pT pL (zB +
    z + pF)`, at ANY letters S of the OOD seed, from `NineFit` and the hypotheses above.

Limits.
- CONDITIONAL THROUGHOUT. No member is shown here.
- The committer's randomness has no place of its own in `HonFit`: Z sets aside OOD seeds, given
  index and randomness. If at some randomness every seed is bad, the measure of the seeds set aside
  pays.
- A bound on the share of rejected runs that is a mean over the prover's coins does not give
  `FallSmall`: that is asked at each fixed coin.
- THE FORM: a fall hangs on the prover's coins: it is a second set, which reads the coin, for
  completeness alone, and is not folded into the abort set. `HonFit` asks acceptance at every coin
  outside the abort set and the fall AT THAT COIN, and the measure at each fixed coin; a mean over
  the coins of these bounds then bounds the error over verifier randomness and coins JOINTLY, which
  is how the goals measure. It does not bound the set of verifier randomness at which SOME coin
  falls.
- "True instances" (Yes) has to shut out by itself what is out of range.


-/
import E2E.BridgePrivacy

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}
  (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed))

/-- A family of falls of the session's prover, by the copy's number. -/
abbrev FallB (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)) : Type :=
  ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Fm.Coin → Set (Rho L.onlineBatch.loc.shape)

/-- The family that is empty at the OOD seeds that are set aside. -/
def guardFall {Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)} (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed)
    (FB : FallB Fm) : FallB Fm :=
  fun n w x c => {ρ | w.2.2 ∉ Z w.1 w.2.1 ∧ ρ ∈ FB n w x c}

/-- Three families of falls at `proversOf hT hL Fm`. -/
def fallsOf (FT : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → hT.Coin → Set (Rho L.offline.shape))
    (FL : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → hL.Coin →
      Set (Rho L.link.shape)) (FB : FallB Fm) : Falls (proversOf hT hL Fm) :=
  ⟨FT, FL, fun w x c => FB w.2.2.2 (w.1, w.2.1, w.2.2.1) x c⟩

variable (FB : FallB Fm) {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- **Hypothesis by name**: every true instance is tied at the OOD seeds that are not set aside. -/
def ValidTiedZ (Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) (Yes : I → X → Prop)
    (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) : Prop :=
  ∀ n i r e x, Yes i x → e ∉ Z i r → Tied n (i, r, e) (x, L.recOf i r e)

/-- From `ValidTied` at all OOD seeds, whatever is set aside. IT THROWS THE PREMISE "not set aside"
AWAY: at a relation that is had so, every hypothesis on acceptance is asked at the seeds set aside
too. -/
theorem ValidTied.toZ {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {Yes : I → X → Prop}
    (h : ValidTied Tied (fun _ => True) (fun _ => True) Yes) (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) :
    ValidTiedZ Tied Yes Z := fun n i r e x hx _ => h n i r e x trivial trivial hx

/-- **Hypothesis by name**: the accept law at tied inputs, at every coin. -/
def AccAtTied (Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) : Prop :=
  ∀ n w x c, Tied n w x →
    AccLaw L.onlineBatch (wBC W) x ((Fm.at n).ext w) ((Fm.at n).strat w x c)
      ((Fm.at n).withheld w x ∪ FB n w x c)

/-- **Hypotheses by name**: neither the abort set nor a fall hangs on the test bits. -/
def WithheldZero : Prop :=
  ∀ n w x ρ, RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ (Fm.at n).withheld w x →
    ρ ∈ (Fm.at n).withheld w x

def FallZero : Prop :=
  ∀ n w x c ρ, RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈ FB n w x c → ρ ∈ FB n w x c

/-- **Hypotheses by name**: the public stops' measure; a fall's, at each fixed coin. -/
def BadSmall (zB : ℝ≥0∞) : Prop := prRho Fm.Bad ≤ zB

def FallSmall (Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) (pF : ℝ≥0∞) : Prop :=
  ∀ n w x c, Tied n w x → prRho (FB n w x c) ≤ pF

variable (FT : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → hT.Coin → Set (Rho L.offline.shape))
  (FL : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → hL.Coin → Set (Rho L.link.shape))
  (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed)

/-- **The clause `whB`.** -/
theorem whB_of (h : WithheldZero Fm W) (hf : FallZero Fm FB W) :
    ∀ w x c ρ, RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈
        (proversOf hT hL Fm).B.withheld w x ∪ (fallsOf hT hL Fm FT FL (guardFall Z FB)).B w x c →
      ρ ∈ (proversOf hT hL Fm).B.withheld w x ∪ (fallsOf hT hL Fm FT FL (guardFall Z FB)).B w x c :=
  fun w x c ρ hρ => hρ.elim (fun a => Or.inl (h w.2.2.2 (w.1, w.2.1, w.2.2.1) x ρ a))
    fun a => Or.inr ⟨a.1, hf w.2.2.2 (w.1, w.2.1, w.2.2.1) x c ρ a.2⟩

/-- **The clause `accB`**: the premise "the OOD seed is not set aside" is spent. -/
theorem accB_of {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {Yes : I → X → Prop}
    (h : AccAtTied Fm FB W Tied) (h2 : ValidTiedZ Tied Yes Z) :
    ∀ i x r e n c, Yes i x → e ∉ Z i r →
      AccLaw L.onlineBatch (wBC W) (x, L.recOf i r e) ((proversOf hT hL Fm).B.ext (i, r, e, n))
        ((proversOf hT hL Fm).B.strat (i, r, e, n) (x, L.recOf i r e) c)
        ((proversOf hT hL Fm).B.withheld (i, r, e, n) (x, L.recOf i r e) ∪
          (fallsOf hT hL Fm FT FL (guardFall Z FB)).B (i, r, e, n) (x, L.recOf i r e) c) := by
  intro i x r e n c hx he
  have hs : (fallsOf hT hL Fm FT FL (guardFall Z FB)).B (i, r, e, n) (x, L.recOf i r e) c =
      FB n (i, r, e) (x, L.recOf i r e) c :=
    Set.ext fun ρ => ⟨fun a => a.2, fun a => ⟨he, a⟩⟩
  rw [hs]
  exact h n (i, r, e) (x, L.recOf i r e) c (h2 n i r e x hx he)

open Classical in
/-- **The clause `prB`**, at the sum of the three measures: at every OOD seed. -/
theorem prB_of {TiedA TiedM : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {Yes : I → X → Prop}
    {zB z pF : ℝ≥0∞} (hb : BadSmall Fm zB) (hz : HidSmall Fm TiedM z)
    (hM : ValidTied TiedM (fun _ => True) (fun _ => True) Yes) (hf : FallSmall Fm FB TiedA pF)
    (hA : ValidTiedZ TiedA Yes Z) :
    ∀ i x r e n c, Yes i x →
      prRho ((proversOf hT hL Fm).B.withheld (i, r, e, n) (x, L.recOf i r e) ∪
        (fallsOf hT hL Fm FT FL (guardFall Z FB)).B (i, r, e, n) (x, L.recOf i r e) c) ≤
          zB + z + pF := by
  intro i x r e n c hx
  refine (pr_union_le _ _ _).trans (add_le_add ((pr_union_le _ _ _).trans (add_le_add hb ?_)) ?_)
  · exact hz n (i, r, e) (x, L.recOf i r e) (hM n i r e x trivial trivial hx)
  · by_cases he : e ∈ Z i r
    · have hs : (fallsOf hT hL Fm FT FL (guardFall Z FB)).B (i, r, e, n) (x, L.recOf i r e) c = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun _ a => a.1 he
      rw [hs, pr_empty]
      exact zero_le _
    · exact (pr_mono _ fun _ a => a.2).trans
        (hf n (i, r, e) (x, L.recOf i r e) c (hA n i r e x hx he))

/-- **The clause `num`**, from the same at the family. -/
theorem numB_of (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) {Yes : I → X → Prop}
    (h : ∀ n w x c (τ : Tr L.onlineBatch.loc.shape),
      Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ((Fm.strat n w x c).run τ.rho).1 τ →
        S.num n τ.plains = true) :
    ∀ i x r e n c (τ : Tr L.onlineBatch.loc.shape), Yes i x →
      Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh
        (((proversOf hT hL Fm).B.strat (i, r, e, n) (x, L.recOf i r e) c).run τ.rho).1 τ →
      S.num n τ.plains = true :=
  fun i x r e n c τ _ hp => h n (i, r, e) (x, L.recOf i r e) c τ hp

/-- **The nine clauses of `HonFit` that do not read the session's prover**, in that structure's own
words: on the key file's prover, on the link's, and on the measure of the OOD seeds that are set
aside. -/
structure NineFit (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (Yes : I → X → Prop) (ζ pT pL : ℝ≥0∞) : Prop where
  extT : ∀ i r e, hT.ext (i, r, e) = L.encodeIndex i r
  extL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')
  whT : ∀ w x c ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ hT.withheld w x ∪ FT w x c →
    ρ ∈ hT.withheld w x ∪ FT w x c
  whL : ∀ w x c ρ, RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ hL.withheld w x ∪ FL w x c →
    ρ ∈ hL.withheld w x ∪ FL w x c
  accT : ∀ i x r e c, Yes i x → e ∉ Z i r →
    AccLaw (batTC L aT) (wTC W) (L.recOf i r e) (hT.ext (i, r, e))
      (hT.strat (i, r, e) (L.recOf i r e) c)
      (hT.withheld (i, r, e) (L.recOf i r e) ∪ FT (i, r, e) (L.recOf i r e) c)
  accL : ∀ i x r e r' e' c, Yes i x → e ∉ Z i r → e' ∉ Z i r' → AccLaw (batLC L aL) (wLC W)
    (L.recOf i r e, L.recOf i r' e') (hL.ext (i, (r, e), (r', e')))
    (hL.strat (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c)
    (hL.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      FL (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c)
  prZ : ∀ i x r, Yes i x → pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Z i r} ≤ ζ
  prT : ∀ i x r e c, Yes i x →
    prRho (hT.withheld (i, r, e) (L.recOf i r e) ∪ FT (i, r, e) (L.recOf i r e) c) ≤ pT
  prL : ∀ i x r e r' e' c, Yes i x →
    prRho (hL.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      FL (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c) ≤ pL

/-- They are had from a value of `HonFit` at any family and falls of the session's prover. -/
theorem NineFit.of_honFit (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) {Yes : I → X → Prop}
    {ζ pT pL pO : ℝ≥0∞} {Fm' : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)} {FB' : FallB Fm'}
    (g : HonFit (proversOf hT hL Fm') (fallsOf hT hL Fm' FT FL FB') W S Yes Z ζ pT pL pO) :
    NineFit hT hL W FT FL Z S Yes ζ pT pL :=
  ⟨g.extT, g.extL, g.whT, g.whL, g.accT, g.accL, g.prZ, g.prT, g.prL⟩

/-- **The structure itself**, from the nine and the hypotheses on the session's prover. -/
theorem honFit_of (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    {TiedA TiedM : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {Yes : I → X → Prop}
    {ζ pT pL zB z pF : ℝ≥0∞} (g : NineFit hT hL W FT FL Z S Yes ζ pT pL)
    (he : ExtIsEnc Fm) (hw : WithheldZero Fm W) (hfz : FallZero Fm FB W)
    (ha : AccAtTied Fm FB W TiedA) (hA : ValidTiedZ TiedA Yes Z) (hb : BadSmall Fm zB)
    (hz : HidSmall Fm TiedM z) (hM : ValidTied TiedM (fun _ => True) (fun _ => True) Yes)
    (hf : FallSmall Fm FB TiedA pF)
    (hn : ∀ n w x c (τ : Tr L.onlineBatch.loc.shape),
      Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ((Fm.strat n w x c).run τ.rho).1 τ →
        S.num n τ.plains = true) :
    HonFit (proversOf hT hL Fm) (fallsOf hT hL Fm FT FL (guardFall Z FB)) W S Yes Z ζ pT pL
      (zB + z + pF) where
  extT := g.extT
  extL := g.extL
  extB := extB_of hT hL Fm he
  whT := g.whT
  whL := g.whL
  whB := whB_of hT hL Fm FB W FT FL Z hw hfz
  accT := g.accT
  accL := g.accL
  accB := accB_of hT hL Fm FB W FT FL Z ha hA
  prZ := g.prZ
  prT := g.prT
  prL := g.prL
  prB := prB_of hT hL Fm FB FT FL Z hb hz hM hf hA
  num := numB_of hT hL Fm W S hn

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.ValidTied.toZ
#print axioms AtPublicFiles.Bridge.whB_of
#print axioms AtPublicFiles.Bridge.accB_of
#print axioms AtPublicFiles.Bridge.prB_of
#print axioms AtPublicFiles.Bridge.numB_of
#print axioms AtPublicFiles.Bridge.NineFit.of_honFit
#print axioms AtPublicFiles.Bridge.honFit_of
