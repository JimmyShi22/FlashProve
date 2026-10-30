-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileSpec.lean: the clauses of PremW on the link's compilation data,
round annotations and randomness, and the statement that they hold at homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome). Definitions and one statement, proved in
Johnson/LinkSim/AtHome/CompileHome.lean.
  LinkCompile W p a c   eleven clauses, verbatim as PremW has them: freeL, okgL, fmtL, cohL, backL,
      kL, okL, lenL, coL, roundsL and winL. They concern the positions the verifier reads, the
      well-formedness of the link's compilation data and round annotations, the reading back of
      nonces, and the lengths, windows, enumerations and distribution of the link's randomness; each
      field's docstring says what it asks.
  linkCompile_of_premW   PremW gives them, by projections.
  LaidLink W p a c v₀   what the substitution sets, and what it asks, of the parameters a and c.
      Set, the link's own components: kL is the enumeration picked by choice, at a's own type of
      coins; the run value is the constant v₀; every public prefix has p.sMT - c.ℓ bits; coL is
      coinsPre (Johnson/WholeKey/CoinLaws.lean) at the window and numbers of a, p, c and W, its
      random bits running through an enumeration that lists each value once. Asked, of components
      that the link shares with the first table's sub-protocol and the sessions: v₀ is well formed;
      c.ℓ ≤ p.sMT; 42 ≤ a.nR; 1 ≤ a.nK; 2 ^ 24 ≤ a.nJ. (The link has 42 rounds, one tree per round
      component and trees of at most 2 ^ 24 leaves: home_roundsL and home_winL,
      Johnson/LinkSim/AtHome/CompileHome.lean.) Johnson/LinkSim/AtHome/CompileLaid.lean proves that
      LaidLink can be met with the explicit honest prover in place. Free: the bound on attempts
      a.capL, the honest provers, and all else.
  Spec.linkCompileHome   at homeR b Z, for all a, c and v₀: LaidLink implies LinkCompile. It does
      not ask which honest prover the link has: none of the eleven clauses reads the honest
      prover except through its type of coins.

How it fits. PremW (Johnson/WholeKey/Premises.lean) names the link in many clauses. Four concern its
honest prover and simulator (LinkFields, Johnson/LinkSim/Spec.lean; at homeR b Z:
Johnson/LinkSim/AtHome/SpecHome.lean), and three its protocol (LinkBeside,
Johnson/LinkSim/Spec.lean). The rest that name the link alone are here. What these definitions serve
is link_all_met (Johnson/LinkSim/AtHome/CompileFiller.lean): that the eighteen clauses on the link
hold together at one structure of parameters. LaidLink also stands in the statement of sideFit_coL
(Johnson/LinkSim/AtHome/CompileSide.lean). premW_withLaid (Johnson/LinkSim/AtHome/CompileFit.lean)
does not use them: it copies these eleven clauses from its premise. They would be wanted by a proof
of PremW at homeR b Z that does not assume it; no file under Johnson/LinkSim/ gives one.

Limits.
  Named and left, because they bind the link to the first table's sub-protocol and to the sessions:
      the two query budgets (at the link's counts 62 and 62: qT + (M + 1) · 62 ≤ b and
      62 + s1 · qon ≤ b), the premise that the joint distribution of a table's OOD answer and its
      symbols at any b positions is the same for all indices (hidE, Hiop/Seeded/Game.lean), the
      base's well-formedness conditions and the encoding of the OOD answers among the parts of the
      clause wires, the tables' salts, and the seeds' plain parts. Five parts of the base's
      well-formedness conditions name the link's compilation data alone (LinkInBase,
      Johnson/LinkSim/AtHome/CompileBase.lean, where they are proved).
  Whether the substituted values are those of the programs' byte format is not said: a constant
      run value and a public prefix of fixed length are a choice made here.
  Nothing on completeness: the lengths of what a hashed run is given (SideFit,
      Johnson/WholeKey/Complete.lean) are not among the eleven.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.SpecHome
import Johnson.WholeKey.Member

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

section General
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **What PremW asks of the link's compilation data, round annotations and randomness.** -/
structure LinkCompile (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params)
    (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) : Prop where
  /-- the positions read do not depend on nonces -/
  freeL : ReadsFree (batLC L aL) (wLC W).sh
  /-- the well-formedness conditions of the link's compilation data -/
  okgL : (wLC W).OKG
  /-- every round has a format -/
  fmtL : aL.Fmt
  /-- the round annotations fit together -/
  cohL : aL.Coherent
  /-- the numbers that a proof-of-work search may try are read back -/
  backL : NoncesBack L.link.shape aL (wLC W).sh a.capL 0
  /-- the enumeration of the prover's coins lists each once -/
  kL : a.kL.OK
  /-- the run values that the prover's coins give are well formed -/
  okL : ∀ κ, a.okV (a.rvL κ)
  /-- a leaf's salt has the length that the verifier's strict format asks -/
  lenL : ∀ v i b s, a.okV v → i < a.nR → s.length = p.sFS →
    (a.startL v i b s).length + c.ℓ = p.sMT
  /-- the distribution of the randomness of a hashed run -/
  coL : RunLaw a.coL a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL
  /-- the window holds all rounds -/
  roundsL : L.link.shape.length ≤ a.nR
  /-- the window holds all trees -/
  winL : WithinWin a.nK a.nJ L.link.shape aL (wLC W).sh

/-- PremW gives them, by projections. -/
theorem linkCompile_of_premW {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params}
    {a : AtRecs lam L Bd aT aL} {Sm : Sims L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop}
    {Ryes : I → X → Prop} {c : CoinNums Bd} {N : NumsW}
    (hP : PremW W Sd cA p a Sm ok Gs Ryes c N) : LinkCompile W p a c :=
  ⟨hP.freeL, hP.wires.Lk, hP.fmt.2.1, hP.coherent.2.1, hP.backL, hP.coins.kL, hP.coins.okL,
    hP.coins.lenL, hP.coins.coL, hP.coins.rounds.2.1, hP.coins.winL⟩

/-- **What the substitution sets, and what it asks, of the parameters.** -/
structure LaidLink (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params)
    (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (v₀ : a.RV) : Prop where
  /-- set: the enumeration of the coins, picked by choice -/
  kL : a.kL = Member.pick a.Hs.Lk.Coin
  /-- set: one constant run value -/
  rvL : ∀ κ, a.rvL κ = v₀
  /-- set: every public prefix has p.sMT - c.ℓ bits -/
  startL : ∀ v i b s, (a.startL v i b s).length = p.sMT - c.ℓ
  /-- set: the randomness of a hashed run -/
  coL : ∃ E : Enum (RunBits lam a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqL), E.OK ∧
    a.coL = coinsPre a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL a.fill E
  /-- asked: the constant is well formed -/
  okV : a.okV v₀
  /-- asked: the random bits fit into a leaf's salt -/
  free : c.ℓ ≤ p.sMT
  /-- asked: the window -/
  nR : 42 ≤ a.nR
  nK : 1 ≤ a.nK
  nJ : 2 ^ 24 ≤ a.nJ

end General

/-- Statement only; proved as linkCompileHome in Johnson/LinkSim/AtHome/CompileHome.lean. At
homeR b Z, LaidLink implies LinkCompile, for all a, c and v₀. -/
def Spec.linkCompileHome : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles)
    (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (c : CoinNums (homeR b Z).LeafBody) (v₀ : a.RV),
    LaidLink (homeR b Z).queryLayout (homeR b Z).compilerParameters a c v₀ → LinkCompile (homeR b Z).queryLayout (homeR b Z).compilerParameters a c

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.linkCompile_of_premW
