-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Bundle.lean: COMPLETENESS, INDEX BINDING, INDEX PRIVACY AND THE HONEST SIDE's WORK
AT ONE TERM: the scheme with the whole key published (argW, Johnson/WholeKey/Defs.lean) at ONE value
of the three interactive protocols' honest sides.

General theorems with their proofs. This file states no goal of the release.

Why. Index privacy alone is cheap: honest sides that send fixed messages meet its premises on
provers with error 0 (silent_good, Johnson/WholeKey/Foes.lean). It says something of a protocol only
beside completeness OF THE SAME HONEST SIDES. HERE COMPLETENESS IS CONCLUDED, from premises on the
same value a.Hs, and the letters of its error are bounded by these premises.

  bundle_argW   under
      * the tie of the range to the relation: every index with a true instance is in the range ok;
      * PremW (Johnson/WholeKey/Premises.lean), the premises of index privacy;
      * the premises of the library's theorem on index binding at the whole key;
      * the premises of completeness at honest sides (complete_of_honFit,
        Johnson/WholeKey/CompleteOfRecs.lean): HonFit AT a.Hs (acceptance outside each honest side's
        withheld set and fall; the measures of these sets at most pT, pL, pO; of the seeds that are
        set aside at most ζc), LawFit, WiresFit, SideFit;
    FIVE CLAUSES AT argW … a.side:
      (1) completeness at alphaAll W caps ζc ζc pT pL pO;
      (2) index binding, extractor named, at soundnessBoundOverTypedOracles W εs;
      (3) index privacy on ok, simulator named, at zetaW;
      (4) the committer asks at most commitN typed queries on every path;
      (5) the prover asks at most proveN.
  stopsSmall_of_honFit   THE STOPS' NUMBERS NEED NO PREMISE OF THEIR OWN WHERE COMPLETENESS STANDS:
    the measure of the stops that may hang on the private input, at verifier messages with the test
    bits 0, is at most the measure of withheld set and fall together: StopsSmall at pT, pL, pO, on
    every range whose indices have a true instance.

WHAT GUARDS, AND WHAT DOES NOT. The tie of the range shuts out an empty range, unless the relation
is empty. That the honest sides are one value shuts out two provers. STILL NO GUARD BY ITSELF: THE
BITE IS IN THE BARS THAT A QUOTE NAMES: the numbers of alphaAll, of zetaW at named (t, n), and of
soundnessBoundOverTypedOracles AT THE NUMBER OF QUERIES OF CLAUSES (4) AND (5). Three provers that still meet the theorem:
  * honest sides whose withheld set is everything meet HonFit whole at pT := pL := pO := 1 (its
    accept laws are asked outside the withheld set alone): clause (1) then holds at an error of 1 or
    more;
  * a prover that tells a one-bit index meets the premises of index privacy at an error that is
    below 1 (typed at a toy: FoeScheme.guess_member, Johnson/WholeKey/FoeZeta.lean): FOR zetaW
    ζ + ζ < 1 IS WHERE IT BEGINS TO SPEAK, and that is necessary, not enough: what shuts out a
    prover that tells in every proof that holds a string is ζ + ζ + α < 1, α the error of
    completeness (argued, not typed: the head of Johnson/WholeKey/Half.lean);
  * "BELOW 1" IS NO BAR FOR COMPLETENESS EITHER (argued, not typed): at a toy silent
    honest sides are accepted by luck with positive probability, so their true error is below 1, and
    they are private. THE NUMBERS TELL, NOT "< 1": the error of completeness must be WELL below 1.
Two numbers stand at a toy: 1/16, and ζ + ζ at most about 0.50 at one query and three requests
(joined_pad2, Johnson/WholeKey/Member2Bundle.lean; zeta_pad2_le, Johnson/WholeKey/Main.lean). Of
soundnessBoundOverTypedOracles there is a number at that toy (eps_pad2, Johnson/WholeKey/Member2Bundle.lean), beside a clause
on binding that is idle there.

Limits. All of Johnson/WholeKey/Statement.lean's. Completeness is `Gen.HasCompletenessError`, for
batches of at most one request: one commitment, one request, both fixed before the oracles are
drawn; nothing on bad keys or on a second request (Johnson/WholeKey/Complete.lean's head). The
accept laws are PREMISES: no real strategy is written. Typed queries, not calls of one hash
function.
ITS ELEVEN PREMISES HOLD TOGETHER AT A TOY ALONE (bundle_pad2, Johnson/WholeKey/Member2Bundle.lean):
six with a case, INDEX BINDING's FIVE IDLY: the toy's index decoder answers one fixed index, so
NOTHING ON BINDING FOLLOWS from that member: its clause on binding would hold there of any
verifier. THE GUARD's BITE IS MEANT, NOT STATED: there is no theorem that silent honest sides fail
completeness.
HonFit's clauses on the session (num, accB, prB) are asked at EVERY number n of a copy; whether a
written strategy meets them so is not known.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Main
import Johnson.WholeKey.Small
import Johnson.WholeKey.CompleteOfRecs
import Johnson.WholeKey.WorkOf

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The stops' numbers, from the premises of completeness.** -/
theorem stopsSmall_of_honFit {Hs : ThreeProvers L} {F : Falls Hs} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {Yes : I → X → Prop} {Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed}
    {ζc pT pL pO : ℝ≥0∞} (hf : HonFit Hs F W S Yes Z ζc pT pL pO) (ok : I → Prop)
    (hok : ∀ i, ok i → ∃ x, Yes i x) (Gs : L.OutOfDomainSeed → Prop) :
    StopsSmall Hs W ok Gs Yes pT pL pO where
  T := fun i r e hi _ => by
    obtain ⟨x, hx⟩ := hok i hi
    refine le_trans (pr_mono _ fun ρ hρ => ?_)
      (hf.prT i x r e (Classical.arbitrary Hs.T.Coin) hx)
    exact hf.whT _ _ _ ρ (Or.inl (Or.inr hρ))
  Lk := fun i r e r' e' hi _ _ => by
    obtain ⟨x, hx⟩ := hok i hi
    refine le_trans (pr_mono _ fun ρ hρ => ?_)
      (hf.prL i x r e r' e' (Classical.arbitrary Hs.Lk.Coin) hx)
    exact hf.whL _ _ _ ρ (Or.inl (Or.inr hρ))
  B := fun n i r e x _ _ hx => by
    refine le_trans (pr_mono _ fun ρ hρ => ?_)
      (hf.prB i x r e n (Classical.arbitrary Hs.B.Coin) hx)
    exact hf.whB _ _ _ ρ (Or.inl (Or.inr hρ))

/-- **THE FIVE CLAUSES AT ONE TERM.** -/
theorem bundle_argW {Wn : Type} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params)
    (a : AtRecs lam L Bd aT aL) (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop)
    (c : CoinNums Bd) (u : NumsW) (i₀ : I) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (F : Falls a.Hs)
    (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (ζc pT pL pO : ℝ≥0∞)
    (_tie : ∀ i, (∃ x w, Ryes i x w) → ok i)
    (hP : PremW W S cA p a Sm ok Gs (fun i x => ∃ w, Ryes i x w) c u)
    (hS : L.SoundAtR Rno wit eR εT εL εB) (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hbB : Err.Below εB εs)
    (hf : HonFit a.Hs F W S (fun i x => ∃ w, Ryes i x w) Z ζc pT pL pO)
    (hL : LawFit W S a.capT a.capL a.capB) (hW : WiresFit W cA) (hF : SideFit W p a.side) :
    ZKCP.Gen.HasCompletenessError
        (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
        (argW W S cA r₀ p a.side) 1 (alphaAll W a.capT a.capL a.capB ζc ζc pT pL pO) ∧
      ZKCP.Gen.HasIndexBindingWith
        (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
        (argW W S cA r₀ p a.side) (extractorC0 W) (soundnessBoundOverTypedOracles W εs) ∧
      ZKCP.Gen.PrivacyOn
        (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
        (argW W S cA r₀ p a.side) 1 (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit)
        (zetaW W S p a c u) ok ∧
      (∀ i, (commitW W S cA a.side i).QueryBound (commitN W a.side)) ∧
      ∀ isk b, (proveW W cA r₀ a.side isk b).QueryBound (proveN W a.side) :=
  ⟨fun i b hb => complete_of_honFit a.Hs F W S cA r₀ p a.side a.dc rfl hf hL hW hF i b hb,
    argW_binding W S cA r₀ p a.side Ryes Rno wit eR εT εL εB εs sub hS hSd hbT hbL hbB
      hP.isLocal.1 hP.isLocal.2.1 hP.isLocal.2.2 hP.coherent.1 hP.coherent.2.1 hP.coherent.2.2
      hP.wires,
    wholeKeyPrivacy I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs (fun i x => ∃ w, Ryes i x w) c u
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub) i₀
      (fun _ _ _ hy => hy) hP,
    fun i => work_commitW hP i, fun isk b => work_proveW hP r₀ isk b⟩

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.stopsSmall_of_honFit
#print axioms OnBytes.WholeKey.bundle_argW
