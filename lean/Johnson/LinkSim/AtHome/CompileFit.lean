-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileFit.lean: if the premises of index privacy (PremW) hold at homeR b Z,
they still hold after the link's honest prover and simulator are replaced by the explicit ones,
and its six other components by substituted values (CompileLaid.lean), with the link's two error
terms 0.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
premW_withLaid: if parameters satisfy the premises of index privacy (PremW) at homeR b Z, they still
do after the link's honest prover is replaced by explicitLinkProver b Z, its simulator by homeSim Z, and its
six other components by substituted values (withLaidLink, below). It asks for a run value v₀ of the
right form and a list E of each value once; both always exist (premW_withLaid_some). The link's two
error terms become 0, and the error of index privacy does not grow (zetaW_withLaid_le,
AtHome/FitZeta.lean). It holds for all public files Z.

  Spec.premW_withLaid   the statement, proved as premW_withLaid. It holds for all b and all public
      files Z, with no condition that Z be in scope. It quantifies over the OOD phase's compilation
      data Sd, the encoding cA of the OOD answers, the structure of parameters a₀ (any three honest
      provers, any bounds on proof-of-work attempts, any number of copies), the three simulators Sm,
      the set ok of indices, the set Gs of OOD seeds, the set Ryes of (index, instance) pairs that
      count as true, and the numbers c and N. It has three premises: PremW at a₀, Sm, c and N; the
      run value v₀ is well formed (a₀.okV v₀); and the enumeration E lists each value of a hashed
      run's random bits exactly once (E.OK). Its conclusion is PremW at withLaidLink b Z a₀ c v₀ E,
      fitSims Sm and fitNums N, with Sd, cA, ok, Gs, Ryes and c unchanged. The compilation data queryLayout
      and the salt lengths compilerParameters are those of homeR b Z.
  withLaidLink b Z a₀ c v₀ E (Johnson/LinkSim/AtHome/CompileLaid.lean)   the substitution: a₀ with
      seven components replaced, all the link's own (the table: Johnson/LinkSim/Swap.lean), with H
      := explicitLinkProver b Z and kL := an enumeration picked by choice. Every other component of a₀ is
      kept.
  fitSims Sm, fitNums N   the simulators Sm with the link's := homeSim Z; the numbers N with the
      link's error and the measure of its aborts := 0.
  premW_withLaid_some   so: if PremW is satisfiable at homeR b Z at all, it is satisfied by
      parameters whose link's honest prover is explicitLinkProver b Z and whose link's simulator is homeSim Z,
      with the link's two error terms both 0. v₀ and E need not be given. A run value of a₀'s own
      link serves, and there is always an E. This form does not say that the new parameters keep
      a₀'s number of copies and bounds on attempts; for the error after the substitution use
      premW_withLaid (see Johnson/LinkSim/AtHome/FitZeta.lean).
  withLaidLink_side (CompileLaid.lean), withLaidLink_rest, withLaidLink_rest_too   checks, by
      definition, that the new link prover is explicitLinkProver b Z and that every other component is a₀'s,
      the link's own bound on proof-of-work attempts (capL) among them.
  premW_withLaid_needs_okV   the premise on v₀ cannot be dropped: if v₀ is not well formed, PremW is
      false at the parameters after the substitution, whatever the other parameters.

How it is proved. The link's four clauses at the new parameters come from one call of
linkFieldsHome (Johnson/LinkSim/AtHome/Home.lean), through linkFields_withLaid (CompileLaid.lean);
of these four only the clause on the simulator has content (see
Johnson/LinkSim/AtHome/SpecHome.lean). Four parts of the clause coins are proved again:
kL from the picked enumeration (pick_ok), okL from the premise on v₀, coL from the premise on E, and
lenL from the substitution with PremW's clause len₀. Every other clause of PremW is copied from the
premise, because it mentions none of the seven replaced components.

How it fits. A lemma on the way to index privacy (Johnson/WholeKey/Statement.lean). No file under
Johnson/LinkSim/ applies the statement of index privacy to the parameters after the substitution.
E2E/LinkLaidPrivacy.lean does (premW_laid, linkLaidWithBound), for public files in scope, with
placeholder provers for the other two sub-protocols. Under Johnson/LinkSim/, FitZeta.lean states the
error after the substitution, and SwapHome.lean derives this statement from the general one in
Johnson/LinkSim/Swap.lean.

Limits.
  The lemma is an implication. Where PremW does not hold it says nothing, and by itself it gives no
      instance of PremW. Its conclusion holds the link's condition on the simulator at error 0
      (good, zL = 0), so where its premise holds it is a statement on distributions. Its conclusion
      has two parts: the link's four conditions, which hold outright (linkFields_withLaid,
      CompileLaid.lean), and the rest of PremW, which is copied from the premise, but for four parts
      of the clause coins (see "How it is proved"), and is only as good as it.
  Without this lemma, instances of PremW are proved, for public files in scope, only with three
      placeholder provers that send fixed messages. The instance that fiveLeft_silent
      (E2E/FiveLeftSilent.lean), noProverSide_built (E2E/PremisesAtFiles.lean) and premW_of_five
      (E2E/PrivacyAtDescription.lean) give is vacuous. Every bound on proof-of-work attempts is 0,
      so each search has one attempt. The link alone has six rounds with 32 proof-of-work bits each
      (fr_work, OnBytes/Slice/FullRecRounds.lean, checked by evaluation in Lean's kernel). So the
      honest party almost never outputs a proof (argued on paper, not proved): this is the fourth
      way of being vacuous below.
  E2E/FiveLeftSilentCaps.lean has the same three placeholder provers with any bounds on attempts; at
      2 ^ 40 attempts their proofs are produced (E2E/StringsInGame.lean, E2E/SessionsInGame.lean),
      so that instance is not vacuous in the fourth way.
  fiveLeft_silent's instance is proved for at most 710,324 copies and at most 688,127 sessions per
      copy (the two query budgets: noProverSide_atFiles, E2E/PremisesAtFiles.lean), with no more
      random bits than a leaf's salt has (ℓ ≤ compilerParameters.sMT). For public files out of scope no instance is
      proved.
  No instance of PremW with three explicit provers is proved in this library. Applied to an
      instance with three placeholder provers, this lemma gives one with the explicit link prover
      and two placeholder provers.
  Only PremW carries over. After the substitution the parameters have another link prover, so they
      define another scheme: another committer and prover, with the same verifier. Completeness,
      binding or work (the honest party's number of oracle queries) that is proved for a₀ does not
      carry over; and index privacy says something only together with completeness of the same
      honest provers.
  PremW can hold vacuously, in four ways: the set ok of indices is empty; the set Gs of seeds is
      empty; an error term is 1 or more; or the bounds on proof-of-work attempts are so small that
      the honest party almost never outputs a proof. The conclusion keeps the premise's ok, Gs,
      bounds on attempts and every number but zL and hL. So it is vacuous in the first, second and
      fourth way exactly when the premise is.
  Nothing is proved again for the first table's sub-protocol or for the sessions. Their clauses, the
      counts of reads and the two query budgets are copied from the premise unchanged (see
      Johnson/LinkSim/AtHome/Home.lean on the three sub-protocols).
  The lemma is stated at the compilation data queryLayout and the salt lengths compilerParameters of homeR b Z, which PremW
      names; nothing is said at other compilation data or other numbers (Johnson/LinkSim/Swap.lean
      states the same step for all of them; on the one fixed digest at which homeR b Z is taken, see
      Home.lean's limits; on the substituted values and the programs, see CompileSpec.lean's
      limits).

Notes.
  Towards completeness at the new parameters two facts are proved, and the rest is not. sideFit_coL
      (Johnson/LinkSim/AtHome/CompileSide.lean) proves that the randomness given to a hashed run of
      the link has the lengths that completeness asks. It is stated under LaidLink
      (Johnson/LinkSim/AtHome/CompileSpec.lean), which includes three conditions on the window
      (42 ≤ nR, 1 ≤ nK, 2 ^ 24 ≤ nJ; the window: see the terms in Johnson/LinkSim/Spec.lean) that
      this lemma does not have, and under two premises more. homeSide_accepted
      (Johnson/LinkSim/AtHome/HomeAccepted.lean) proves that the link's verifier accepts
      explicitLinkProver b Z at every verifier message that passes the proof-of-work checks, for public files
      in scope and a live description (protocolDataWellFormed) only. For public files out of scope this lemma still
      holds, but no completeness at all is proved there.
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
open Johnson.Prover.Link (Kc)
open OnBytes.LinkSim (LinkFields)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- The simulators with the link's := the explicit one. -/
def fitSims {b : PublicFiles → ℕ} {Z : PublicFiles} (Sm : Sims (homeR b Z).protocol) : Sims (homeR b Z).protocol :=
  { Sm with Lk := homeSim Z }

/-- The numbers with the link's two error terms, zL and hL, := 0; all others unchanged. -/
def fitNums (N : NumsW) : NumsW := { N with zL := 0, hL := 0 }

/-- Statement only; proved as premW_withLaid below. If PremW holds at homeR b Z, v₀ is well formed
and E lists each value once, then PremW holds with the explicit link prover and simulator in place
and the link's two error terms 0. -/
def Spec.premW_withLaid : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles)
    (Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (cA : (homeR b Z).protocol.OutOfDomainAnswer → List (Dig 256))
    (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (Sm : Sims (homeR b Z).protocol) (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) (c : CoinNums (homeR b Z).LeafBody) (N : NumsW)
    (v₀ : a₀.RV)
    (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL)),
    PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a₀ Sm ok Gs Ryes c N → a₀.okV v₀ → E.OK →
    PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) (fitSims Sm) ok Gs Ryes c
      (fitNums N)

/-- Proves Spec.premW_withLaid: the link's four clauses come from linkFieldsHome, four parts of the
clause coins from the substitution and the premises on v₀ and E, and every other clause of PremW
from the premise. -/
theorem premW_withLaid : Spec.premW_withLaid := by
  intro b Z Sd cA a₀ Sm ok Gs Ryes c N v₀ E hP hv hE
  have LF := linkFields_withLaid b Z a₀ c v₀ E ok Gs
  have hf : c.ℓ ≤ (homeR b Z).compilerParameters.sMT := hP.coins.len₀ ▸ Nat.le_add_left _ _
  exact
    { ext := ⟨hP.ext.T, LF.ext, hP.ext.B⟩
      runVals := ⟨hP.runVals.T, LF.runVals, hP.runVals.B⟩
      reads := hP.reads
      budget₀ := hP.budget₀
      budget₁ := hP.budget₁
      good := ⟨hP.good.T, LF.good, hP.good.B⟩
      stops := ⟨hP.stops.T, LF.stops, hP.stops.B⟩
      seeds := hP.seeds
      freeT := hP.freeT
      freeL := hP.freeL
      freeB := hP.freeB
      wires := hP.wires
      fmt := hP.fmt
      backT := hP.backT
      backL := hP.backL
      backB := hP.backB
      plain := hP.plain
      coherent := hP.coherent
      isLocal := hP.isLocal
      coins :=
        { ri := hP.coins.ri
          kT := hP.coins.kT
          kL := Member.pick_ok _
          kB := hP.coins.kB
          sl := hP.coins.sl
          len₀ := hP.coins.len₀
          okT := hP.coins.okT
          okL := fun _ => hv
          okB := hP.coins.okB
          lenT := hP.coins.lenT
          lenL := fun _ _ _ _ _ _ _ =>
            (congrArg (· + c.ℓ) List.length_replicate).trans (Nat.sub_add_cancel hf)
          lenB := hP.coins.lenB
          coT := hP.coins.coT
          coL := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ E hE
          coB := hP.coins.coB
          rounds := hP.coins.rounds
          winT := hP.coins.winT
          winL := hP.coins.winL
          winB := hP.coins.winB } }

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **If PremW is satisfiable at homeR b Z at all, it is satisfiable with the explicit link prover
and the explicit simulator, with the link's two error terms both 0.** -/
theorem premW_withLaid_some
    {Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits}
    {cA : (homeR b Z).protocol.OutOfDomainAnswer → List (Dig 256)}
    {a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits}
    {Sm : Sims (homeR b Z).protocol} {ok : (homeR b Z).Index → Prop} {Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop}
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop} {c : CoinNums (homeR b Z).LeafBody} {N : NumsW}
    (hP : PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a₀ Sm ok Gs Ryes c N) :
    ∃ a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits,
      a.Hs.Lk = explicitLinkProver b Z ∧
      PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a (fitSims Sm) ok Gs Ryes c (fitNums N) := by
  obtain ⟨E, hE⟩ := runBits_listed 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr
    (homeR b Z).queryLayout.depthReqL
  obtain ⟨κ⟩ := (inferInstance : Nonempty a₀.Hs.Lk.Coin)
  exact ⟨withLaidLink b Z a₀ c (a₀.rvL κ) E, rfl,
    premW_withLaid b Z Sd cA a₀ Sm ok Gs Ryes c N (a₀.rvL κ) E hP (hP.coins.okL κ) hE⟩

/-! ## Checks of the substitution -/

section
variable (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  (c : CoinNums (homeR b Z).LeafBody) (v₀ : a₀.RV)
  (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL))

/-- **Twenty-one of the 29 components that are not replaced are a₀'s**, by definition. The link's
own bound on proof-of-work attempts is among them: it is kept. The other eight are in
withLaidLink_rest_too. -/
theorem withLaidLink_rest :
    (withLaidLink b Z a₀ c v₀ E).Hs.T = a₀.Hs.T ∧ (withLaidLink b Z a₀ c v₀ E).Hs.B = a₀.Hs.B ∧
    (withLaidLink b Z a₀ c v₀ E).capT = a₀.capT ∧ (withLaidLink b Z a₀ c v₀ E).capL = a₀.capL ∧
    (withLaidLink b Z a₀ c v₀ E).capB = a₀.capB ∧ (withLaidLink b Z a₀ c v₀ E).M = a₀.M ∧
    (withLaidLink b Z a₀ c v₀ E).nR = a₀.nR ∧ (withLaidLink b Z a₀ c v₀ E).nK = a₀.nK ∧
    (withLaidLink b Z a₀ c v₀ E).nJ = a₀.nJ ∧ (withLaidLink b Z a₀ c v₀ E).ri = a₀.ri ∧
    (withLaidLink b Z a₀ c v₀ E).sl = a₀.sl ∧ (withLaidLink b Z a₀ c v₀ E).kT = a₀.kT ∧
    (withLaidLink b Z a₀ c v₀ E).kB = a₀.kB ∧ (withLaidLink b Z a₀ c v₀ E).coT = a₀.coT ∧
    (withLaidLink b Z a₀ c v₀ E).coB = a₀.coB ∧ (withLaidLink b Z a₀ c v₀ E).rvT = a₀.rvT ∧
    (withLaidLink b Z a₀ c v₀ E).rvB = a₀.rvB ∧ (withLaidLink b Z a₀ c v₀ E).pvT = a₀.pvT ∧
    (withLaidLink b Z a₀ c v₀ E).pvB = a₀.pvB ∧
    (withLaidLink b Z a₀ c v₀ E).startT = a₀.startT ∧
    (withLaidLink b Z a₀ c v₀ E).startB = a₀.startB :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- **The other eight**: the leaf padding, the copies' numbers, the type of run values and its
well-formedness test, the tails of the runs' salts, the fixed public string that stands for salt
bits outside the window nR, nK, nJ, and the decisions for the first table's sub-protocol and for the
sessions. With withLaidLink_rest: every component that is not replaced is a₀'s. Seven are replaced,
all the link's own: its honest prover and decision, rvL, pvL, startL, kL, coL. -/
theorem withLaidLink_rest_too :
    (withLaidLink b Z a₀ c v₀ E).b₀ = a₀.b₀ ∧ (withLaidLink b Z a₀ c v₀ E).nm = a₀.nm ∧
    (withLaidLink b Z a₀ c v₀ E).RV = a₀.RV ∧ (withLaidLink b Z a₀ c v₀ E).okV = a₀.okV ∧
    (withLaidLink b Z a₀ c v₀ E).rtail = a₀.rtail ∧ (withLaidLink b Z a₀ c v₀ E).fill = a₀.fill ∧
    (withLaidLink b Z a₀ c v₀ E).dc.T = a₀.dc.T ∧ (withLaidLink b Z a₀ c v₀ E).dc.B = a₀.dc.B :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The premise on v₀ cannot be dropped**: if v₀ is not well formed, PremW is false at the
parameters after the substitution, whatever the other parameters. -/
theorem premW_withLaid_needs_okV (hv : ¬ a₀.okV v₀)
    (Sd : OutOfDomainSampleQueryLayout 256 (homeR b Z).queryLayout.K (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (cA : (homeR b Z).protocol.OutOfDomainAnswer → List (Dig 256)) (Sm : Sims (homeR b Z).protocol)
    (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) (c' : CoinNums (homeR b Z).LeafBody) (N : NumsW) :
    ¬ PremW (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) Sm ok Gs Ryes c' N :=
  fun hP => by
    obtain ⟨κ⟩ := (inferInstance : Nonempty (withLaidLink b Z a₀ c v₀ E).Hs.Lk.Coin)
    exact hv (hP.coins.okL κ)

end

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.premW_withLaid
#print axioms OnBytes.LinkSim.AtHome.premW_withLaid_some
#print axioms OnBytes.LinkSim.AtHome.withLaidLink_rest
#print axioms OnBytes.LinkSim.AtHome.withLaidLink_rest_too
#print axioms OnBytes.LinkSim.AtHome.premW_withLaid_needs_okV
