-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileBase.lean: the five well-formedness conditions of the base that
concern the link's compilation data alone, and a proof that they hold at homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome).
  home_linkInBase   at homeR b Z, for all b and Z, the five conditions hold, with no premise. It is
      one call of wiresFit_home (Johnson/Prover/At/HomeAt.lean), which proves all of the base's
      well-formedness conditions.
  LinkInBase W   the five conditions, verbatim as the base's well-formedness conditions W.OKG
      (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) have them:
      Lk         the well-formedness conditions of the link's compilation data
      depthExt   the second part of extDepth: the link's input oracles lie as deep as a table
      depthL     a table's depth is at most the link's greatest depth
      extL       a position of the first input oracle lies in tree 0, one of the second in tree 1,
                 each at its own index
      prjL_emb   what is written into a leaf body of the link is read back
  linkInBase_of_okg   they are parts of the base's well-formedness conditions, for all compilation
      data: by projections.
  linkInBase_of_premW   so PremW gives them.

The count. Besides the eighteen clauses on the link that PremW (Johnson/WholeKey/Premises.lean)
has, counted by inspection (LinkCompile, CompileSpec.lean; LinkFields and LinkBeside,
Johnson/LinkSim/Spec.lean), PremW's field wires holds the base's well-formedness conditions
(wires.base : W.OKG), sixteen fields. Four of them, and one of the three parts of a fifth, name the
link's compilation data alone: these are the five. Four are new in content. Lk follows from okgL,
one of the eighteen, by inspection and not by a theorem: three of its four parts read only the
shape, the round annotations and the compilation data, and the fourth is asked at the carrier's link
protocol, which reads nothing (the carrier, typedOracleCarrier in Johnson/TypedOracleCompiler/RecCompile/Carrier.lean, holds
only the protocol's public types).

How it fits. Under Johnson/LinkSim/ home_linkInBase and linkInBase_of_premW are called by no file;
they complete the count of what PremW says of the link alone.

Limits. That these five are all that the base's well-formedness conditions say of the link's
compilation data alone is by inspection of that structure's text, not proved. Its other eleven
fields, and the other two parts of extDepth, name the first table's sub-protocol, the sessions, or
what all three sub-protocols share (the tables' depth, the number of slots, a symbol of an encoded
index that is read back from a leaf body).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileHome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

section General
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The parts of the base's well-formedness conditions that name the link's compilation data
alone.** -/
structure LinkInBase (W : QueryLayout lam L) : Prop where
  Lk : W.Lk.OKG
  depthExt : W.Lk.ext.depth = W.depth
  depthL : W.depth ≤ W.Lk.maxDepth
  extL : (∀ p, W.Lk.ext.which (.inl p) = 0 ∧ W.Lk.ext.leaf (.inl p) = p.val) ∧
         (∀ p, W.Lk.ext.which (.inr p) = 1 ∧ W.Lk.ext.leaf (.inr p) = p.val)
  prjL_emb : ∀ p a, W.prjL p (W.embL p a) = some a

/-- They are parts of the base's well-formedness conditions. -/
theorem linkInBase_of_okg {W : QueryLayout lam L} (h : W.OKG) : LinkInBase W :=
  ⟨h.Lk, h.extDepth.2.1, h.depthL, h.extL, h.prjL_emb⟩

end General

section
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **PremW gives them.** -/
theorem linkInBase_of_premW {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params} {a : AtRecs lam L Bd aT aL} {Sm : Sims L}
    {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {c : CoinNums Bd} {N : NumsW}
    (hP : PremW W Sd cA p a Sm ok Gs Ryes c N) : LinkInBase W :=
  linkInBase_of_okg hP.wires.base

end

/-- **They hold at homeR b Z**, with no premise. -/
theorem home_linkInBase (b : PublicFiles → ℕ) (Z : PublicFiles) : LinkInBase (homeR b Z).queryLayout :=
  linkInBase_of_okg (wiresFit_home b Z ((homeT b Z).Pub.det fun _ _ _ => false)).oka.base

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.linkInBase_of_premW
#print axioms OnBytes.LinkSim.AtHome.home_linkInBase
