-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/PremAt.lean: the premises of index privacy at every value d of a set Dok of the
public reading's values, as one premise (PremAll). If it holds, with one bound for all these d, the
scheme with the whole key published has index privacy on the range ok (ZKCP.Gen.PrivacyOn), for
every relation inside Ryes whose public parameter is the one value of Unit, at each d of Dok; ok and
Ryes are parameters of PremAll. If Dok is all d, so has, under the four premises on the public
reading, the scheme that first reads d off the hash function (wholeRead,
Johnson/PublicAt/Whole.lean). Conditional.
Terms and the limits that go with any quote: Spec.lean.

What this file has. The family T, the honest sides and the simulators are variables.
  SidesAt T   what may depend on d besides T's own parts: a (the honest side), Sm (the simulators of
      the three interactive protocols protocol.offline, protocol.link and protocol.onlineBatch.loc), Gs (the public set of seeds), c
      and u (numbers), i₀ (the simulator's fixed index). F.side d and F.sim d are the honest side
      and the simulator simWholeKey at d.
  PremAll F ok Ryes Dok   PremW (Johnson/WholeKey/Premises.lean) at every d of Dok. The range ok of
      indices and the relation Ryes do not depend on d.
  ZetaLe F Dok ζ   the explicit error zetaW at every d of Dok is at most ζ: one bound for all d.
  privacy_typedAt   If Rl.yes implies Ryes, and PremAll and ZetaLe hold: at each d of Dok, PrivacyOn
      of typedAt T F.side d over the typed oracles, with the simulator F.sim d, at ζ, on the range
      ok. By wholeKeyPrivacy (Johnson/WholeKey/Main.lean).
  privacy_read   If moreover Dok is all d and the four premises on the public reading hold:
      PrivacyOn of wholeRead T F.side over one hash function, at ζ, on ok.
  privacy_read_on   The same for any Dok, at ζ + β, if β bounds the probability that the reading's
      value is outside Dok and the simulators at the d outside Dok give consistent answers
      (ConsistentOn, ZKCP/PublicRead/Spec.lean). That is a PREMISE, here (hS) and in
      privacy_wholeRead_on (Johnson/PublicAt/Whole.lean): no statement of this library concludes
      ConsistentOn, and nothing calls privacy_read_on: it is no unconditional result.

Limits. PremAll is required at every d of Dok, whether or not a hash function gives that d. No
member of PremAll is built here; one, with two placeholder provers, which send fixed messages, is
premAll_laid (LaidAll.lean). privacy_read and privacy_read_on are about wholeRead, whose key has no
told part and no commitment ID. They are not about a shell, and the way to the shells does not use
them: it uses privacy_typedAt only. All limits of Johnson/WholeKey/Statement.lean and
ZKCP/PublicRead/Spec.lean hold. A bound says nothing until ζ + ζ < 1 (Johnson/WholeKey/Half.lean).
At an empty range ok or a range with one index, and in privacy_read_on at β ≥ 1, they say nothing.

Notes: why at every d. wholeKeyPrivacy is for parameters that are fixed before the oracles are
sampled. A verifier that first reads d off the hash function and then runs at parameters made from d
needs it at every d, with one bound (Johnson/PublicAt/Whole.lean requires that). The seeds' wire,
the code of answers and the coding depend on d (LayoutsByPublicReading, Johnson/Top/InnerCompiledVerifierByPublicReading.lean). The
honest side may too: the enumerations of salts and coins, the public starts of leaf salts, the
strategies.
-/
import Johnson.WholeKey.Main
import Johnson.PublicAt.Whole

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- ZKCP.Gen.PrivacyOn at a bound ζ holds at every bound ζ' that is at least ζ at all arguments. -/
theorem privacyOn_mono {S : OSpec} {I X W PP IVK ISK Pf : Type} {R : ZKCP.Gen.RelPair I X W PP}
    {A : ZKCP.Gen.Arg S I X W IVK ISK Pf} {B : ℕ} {Sim : ZKCP.Gen.Simulator S PP IVK X Pf}
    {ζ ζ' : ℕ → ℕ → ℝ≥0∞} {ok : I → Prop} (h : ZKCP.Gen.PrivacyOn R A B Sim ζ ok)
    (hζ : ∀ t n, ζ t n ≤ ζ' t n) : ZKCP.Gen.PrivacyOn R A B Sim ζ' ok :=
  fun i hi Z hZ t Vt N hb => ⟨(h i hi Z hZ t Vt N hb).1.trans (hζ t N), (h i hi Z hZ t Vt N hb).2⟩

variable {R : InnerCompilerInput}

/-- The parameters of the honest side and of the simulator, as functions of the public reading's
value d. -/
structure SidesAt (T : LayoutsByPublicReading R) where
  /-- the honest side's parameters -/
  a : T.D → AtRecs 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits
  /-- the simulators of the three interactive protocols -/
  Sm : T.D → Sims R.protocol
  /-- the public set of seeds -/
  Gs : T.D → R.protocol.OutOfDomainSeed → Prop
  /-- the numbers of the premises on coins -/
  c : T.D → CoinNums R.LeafBody
  /-- the numbers of the premises -/
  u : T.D → NumsW
  /-- the simulator's fixed index -/
  i₀ : T.D → R.Index

variable {T : LayoutsByPublicReading R} (F : SidesAt T)

/-- The honest side of the scheme at d. -/
def SidesAt.side (d : T.D) : HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits := (F.a d).side

/-- The simulator simWholeKey at d, over the typed oracles. -/
def SidesAt.sim (d : T.D) : ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) Unit
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol) :=
  simWholeKey R.queryLayout (T.Sd d) (T.cA d) R.fixedSample (F.a d).side (F.Sm d) (F.i₀ d) (F.u d).s1 (F.Gs d) Unit

/-- The premises of index privacy, PremW, at every d of Dok. The range ok and the relation Ryes do
not depend on d. -/
def PremAll (ok : R.Index → Prop) (Ryes : R.Index → R.Instance → Prop) (Dok : T.D → Prop) : Prop :=
  ∀ d, Dok d →
    PremW R.queryLayout (T.Sd d) (T.cA d) R.compilerParameters (F.a d) (F.Sm d) ok (F.Gs d) Ryes (F.c d) (F.u d)

/-- One bound for all d of Dok: the explicit error zetaW at d is at most ζ. -/
def ZetaLe (Dok : T.D → Prop) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ d, Dok d → ∀ t n, zetaW R.queryLayout (T.Sd d) R.compilerParameters (F.a d) (F.c d) (F.u d) t n ≤ ζ t n

variable {F} {ok : R.Index → Prop} {Ryes : R.Index → R.Instance → Prop} {Dok : T.D → Prop}
  {ζ : ℕ → ℕ → ℝ≥0∞} (Rl : ZKCP.Gen.RelPair R.Index R.Instance Unit Unit)

/-- If Rl.yes implies Ryes (hR), and PremAll and ZetaLe hold, then at each d of Dok the scheme with
the whole key published at the input at d (typedAt) has ZKCP.Gen.PrivacyOn over the typed oracles,
with the simulator F.sim d, at ζ, on the range ok. -/
theorem privacy_typedAt (hR : ∀ i x w, Rl.yes i x w → Ryes i x) (hP : PremAll F ok Ryes Dok)
    (hζ : ZetaLe F Dok ζ) (d : T.D) (hd : Dok d) :
    ZKCP.Gen.PrivacyOn Rl (typedAt T F.side d) 1 (F.sim d) ζ ok :=
  privacyOn_mono
    (wholeKeyPrivacy R.Index R.Instance 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters (F.a d) (F.Sm d)
      ok (F.Gs d) Ryes (F.c d) (F.u d) Rl (F.i₀ d) hR (hP d hd))
    (hζ d hd)

/-- If Rl.yes implies Ryes, PremAll and ZetaLe hold at every d, and the four premises on the public
reading hold, the scheme that first reads d off the hash function (wholeRead) has ZKCP.Gen.PrivacyOn
at ζ on the range ok. wholeRead is not a shell. -/
theorem privacy_read (hR : ∀ i x w, Rl.yes i x w → Ryes i x)
    (hP : PremAll F ok Ryes fun _ => True) (hζ : ZetaLe F (fun _ => True) ζ)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s) :
    ZKCP.Gen.PrivacyOn Rl (wholeRead T F.side) 1
      (glueSim T.Pub fun d => simOne (T.m d) (F.sim d)) ζ ok :=
  privacy_wholeRead F.side Rl F.sim 1 ζ ok noCoin asks once spare
    fun d => privacy_typedAt Rl hR hP hζ d trivial

/-- privacy_read with PremAll and ZetaLe required only at the d of Dok: at the bound ζ + β, if β
bounds the probability that the reading's value is outside Dok (hβ) and the simulators at the d
outside Dok give consistent answers (hS). -/
theorem privacy_read_on (hR : ∀ i x w, Rl.yes i x w → Ryes i x) (hP : PremAll F ok Ryes Dok)
    (hζ : ZetaLe F Dok ζ) (β : ℝ≥0∞) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hS : ∀ d, ¬ Dok d → ConsistentOn Rl 1 (simOne (T.m d) (F.sim d)) ok)
    (hβ : Rom.Pr T.Pub (fun _ => {d | ¬ Dok d}) ≤ β) :
    ZKCP.Gen.PrivacyOn Rl (wholeRead T F.side) 1
      (glueSim T.Pub fun d => simOne (T.m d) (F.sim d)) (fun t N => ζ t N + β) ok :=
  privacy_wholeRead_on F.side Rl F.sim 1 ζ β ok Dok noCoin asks once spare
    (fun d hd => privacy_typedAt Rl hR hP hζ d hd) hS hβ

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.privacy_typedAt
#print axioms OnBytes.FrontRoad.privacy_read
#print axioms OnBytes.FrontRoad.privacy_read_on
