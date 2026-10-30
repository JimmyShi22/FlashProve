-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/Swap.lean: in general form, if the premises of index privacy hold, they still hold
after the link's prover and simulator are replaced by any pair that meets the link's four clauses
with both error terms 0.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  Spec.premW_layLink   the statement, proved as premW_layLink. It holds for all protocol structures
      L, all compilation data, all salt lengths p, all structures of parameters a₀, all simulators
      Sm, every set ok of indices, every set Gs of OOD seeds, every set Ryes of (index, instance)
      pairs that count as true, and all numbers c and N. Take any honest prover H of the link, any
      enumeration kL of its coins, any simulator S of the link, any run value v₀ and any enumeration
      E of a hashed run's random bits. There are five premises: (1) PremW holds at a₀, Sm, c and N;
      (2) LinkFields (Johnson/LinkSim/Spec.lean), the link's four clauses, holds for
      layLink W p a₀ c H kL v₀ E and S, with both error terms 0; (3) kL lists each coin of H exactly
      once; (4) v₀ is well formed; (5) E lists each value exactly once. Then PremW holds at
      layLink W p a₀ c H kL v₀ E, laySims Sm S and layNums N. The compilation data, the OOD phase's
      compilation data, the encoding of the OOD answers, p, ok, Gs, Ryes and c are the same on both
      sides.
  layLink W p a₀ c H kL v₀ E   the substitution: a₀ with the link's seven components replaced;
      every other component is kept. AtRecs has 32 fields; with the three honest provers and the
      three decisions counted one by one, 36 components, of which these seven are replaced:
        Hs.Lk      the link's honest prover, by H;
        dc.Lk      its Decidable instance for the abort set, by Classical.dec;
        rvL, pvL   the run value read off the coin and off what is sent in the clear, both by v₀;
        startL     the public prefix of each leaf salt, by p.sMT - ℓ zeros;
        kL         the enumeration of H's coins, by kL;
        coL        the randomness of the link's hashed run, built from E (coinsPre,
                   Johnson/WholeKey/CoinLaws.lean) within a₀'s window (see the terms in
                   Johnson/LinkSim/Spec.lean); outside it the fixed public string a₀.fill stands in.
  laySims Sm S, layNums N   the simulators Sm with the link's := S; the numbers N with the link's
      error and the measure of its aborts := 0.
  layLink_side, layLink_rest, layLink_rest_too   checks, by definition, that the new link prover is
      H and that every other component is a₀'s, the link's own bound on proof-of-work attempts
      (capL) among them.
  premW_layLink_needs_okV   the premise on v₀ cannot be dropped: if v₀ is not well formed, PremW is
      false at the parameters after the substitution, whatever the other parameters.

How it is proved. The link's parts of ext, runVals, good and stops come from premise (2); runVals
holds in any case, since both readings of the run value are the constant v₀. Of the clause coins, kL
is premise (3), okL is premise (4), coL follows from premise (5), and lenL follows from the
substitution with PremW's clause len₀. Every other clause of PremW is copied from premise (1),
because it mentions none of the seven replaced components.

How it fits. A lemma on the premises of the conditional theorem on index privacy
(Spec.wholeKeyPrivacy, Johnson/WholeKey/Statement.lean). Johnson/LinkSim/AtHome/CompileFit.lean's
lemma is proved directly; this file is the reusable form, for any pair that meets the link's four
clauses; Johnson/LinkSim/AtHome/SwapHome.lean proves that the general statement implies
CompileFit.lean's, by taking Spec.premW_layLink as a hypothesis and deriving that lemma's statement
from it. Under Johnson/LinkSim/ no file calls the theorem premW_layLink. The definitions layLink and
layNums are used: Johnson/LinkSim/SwapZeta.lean states the error after the substitution with them.

Limits.
  The lemma is an implication with two substantial premises: PremW before the substitution, and the
      link's four clauses for H and S with both error terms 0. Where either fails it says nothing.
      It proves nothing new about any distribution. What such an implication does and does not give
      is in Johnson/LinkSim/AtHome/CompileFit.lean's Limits.
  The lemma holds for every prover H and simulator S. Under Johnson/LinkSim/, though, its second
      premise is proved for one prover and one parameter set only: explicitLinkProver b Z and homeSim Z at
      homeR b Z (linkFieldsHome, Johnson/LinkSim/AtHome/Home.lean). There its conclusion is what
      Johnson/LinkSim/AtHome/CompileFit.lean proves by a separate proof.
  Two limits of Johnson/LinkSim/AtHome/CompileFit.lean apply here unchanged and are stated there:
      PremW can hold vacuously, in four ways; and only PremW carries over to the parameters after
      the substitution, not completeness, binding or bounds on the honest party's work; and index
      privacy says something only together with completeness of the same honest provers.
  Nothing is proved again for the first table's sub-protocol or for the sessions: their clauses are
      copied from premise (1). (On the substituted values and the programs, see
      Johnson/LinkSim/AtHome/CompileSpec.lean's limits.)

Notes.
  The premise on kL cannot be dropped: after the substitution, PremW's clause on the enumeration of
      the link's coins is kL.OK itself (by the definition of layLink, not stated as a theorem).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Spec

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LinkSim
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The substitution: a₀ with the link's seven components replaced**: the honest prover by H and
its Decidable instance for the abort set by Classical.dec; both readings of the run value by v₀; the
salt prefixes by zeros; the coins' enumeration by kL; the hashed run's randomness by one built from
E. -/
def layLink (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params) (a₀ : AtRecs lam L Bd aT aL)
    (c : CoinNums Bd) (H : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
    (kL : Enum H.Coin) (v₀ : a₀.RV)
    (E : Enum (RunBits lam a₀.nR a₀.nK a₀.nJ p.sFS c.ℓ c.ℓr W.depthReqL)) :
    AtRecs lam L Bd aT aL where
  Hs := ⟨a₀.Hs.T, H, a₀.Hs.B⟩
  dc := ⟨a₀.dc.T, fun _ _ _ => Classical.dec _, a₀.dc.B⟩
  b₀ := a₀.b₀
  capT := a₀.capT
  capL := a₀.capL
  capB := a₀.capB
  M := a₀.M
  nm := a₀.nm
  RV := a₀.RV
  okV := a₀.okV
  rvT := a₀.rvT
  rvL := fun _ => v₀
  rvB := a₀.rvB
  startT := a₀.startT
  startL := fun _ _ _ _ => List.replicate (p.sMT - c.ℓ) false
  startB := a₀.startB
  pvT := a₀.pvT
  pvL := fun _ => v₀
  pvB := a₀.pvB
  rtail := a₀.rtail
  nR := a₀.nR
  nK := a₀.nK
  nJ := a₀.nJ
  fill := a₀.fill
  ri := a₀.ri
  sl := a₀.sl
  kT := a₀.kT
  kL := kL
  kB := a₀.kB
  coT := a₀.coT
  coL := coinsPre a₀.nR a₀.nK a₀.nJ p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL a₀.fill E
  coB := a₀.coB

/-- The simulators with the link's := S. -/
def laySims (Sm : Sims L) (S : SimOf L.link) : Sims L := { Sm with Lk := S }

/-- The numbers with the link's two error terms, zL and hL, := 0; all others unchanged. -/
def layNums (N : NumsW) : NumsW := { N with zL := 0, hL := 0 }

/-- Statement only; proved as premW_layLink below. If PremW holds, and the link's four clauses hold
for H and S with both error terms 0, then PremW holds after the link's prover and simulator are
replaced by H and S, given three side premises on kL, v₀ and E. -/
def Spec.premW_layLink : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params) (a₀ : AtRecs lam L Bd aT aL) (Sm : Sims L)
    (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd) (N : NumsW)
    (H : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))) (kL : Enum H.Coin)
    (S : SimOf L.link) (v₀ : a₀.RV)
    (E : Enum (RunBits lam a₀.nR a₀.nK a₀.nJ p.sFS c.ℓ c.ℓr W.depthReqL)),
    PremW W Sd cA p a₀ Sm ok Gs Ryes c N →
    LinkFields (layLink W p a₀ c H kL v₀ E) S W ok Gs 0 0 → kL.OK → a₀.okV v₀ → E.OK →
    PremW W Sd cA p (layLink W p a₀ c H kL v₀ E) (laySims Sm S) ok Gs Ryes c (layNums N)

/-- Proves Spec.premW_layLink: the link's four clauses come from the premise LinkFields, four parts
of the clause coins from the substitution and premises (3) to (5), and every other clause of PremW
from the premise PremW. -/
theorem premW_layLink : Spec.premW_layLink := by
  intro I X lam L Bd aT aL W Sd cA p a₀ Sm ok Gs Ryes c N H kL S v₀ E hP LF hk hv hE
  have hf : c.ℓ ≤ p.sMT := hP.coins.len₀ ▸ Nat.le_add_left _ _
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
          kL := hk
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

/-! ## Checks of the substitution -/

section
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params) (a₀ : AtRecs lam L Bd aT aL)
  (c : CoinNums Bd) (H : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  (kL : Enum H.Coin) (v₀ : a₀.RV)
  (E : Enum (RunBits lam a₀.nR a₀.nK a₀.nJ p.sFS c.ℓ c.ℓr W.depthReqL))

/-- The new link's honest prover is H. -/
theorem layLink_side : (layLink W p a₀ c H kL v₀ E).Hs.Lk = H := rfl

/-- **Twenty-one of the 29 components that are not replaced are a₀'s**, by definition. The link's
own bound on proof-of-work attempts is among them: it is kept. -/
theorem layLink_rest :
    (layLink W p a₀ c H kL v₀ E).Hs.T = a₀.Hs.T ∧ (layLink W p a₀ c H kL v₀ E).Hs.B = a₀.Hs.B ∧
    (layLink W p a₀ c H kL v₀ E).capT = a₀.capT ∧ (layLink W p a₀ c H kL v₀ E).capL = a₀.capL ∧
    (layLink W p a₀ c H kL v₀ E).capB = a₀.capB ∧ (layLink W p a₀ c H kL v₀ E).M = a₀.M ∧
    (layLink W p a₀ c H kL v₀ E).nR = a₀.nR ∧ (layLink W p a₀ c H kL v₀ E).nK = a₀.nK ∧
    (layLink W p a₀ c H kL v₀ E).nJ = a₀.nJ ∧ (layLink W p a₀ c H kL v₀ E).ri = a₀.ri ∧
    (layLink W p a₀ c H kL v₀ E).sl = a₀.sl ∧ (layLink W p a₀ c H kL v₀ E).kT = a₀.kT ∧
    (layLink W p a₀ c H kL v₀ E).kB = a₀.kB ∧ (layLink W p a₀ c H kL v₀ E).coT = a₀.coT ∧
    (layLink W p a₀ c H kL v₀ E).coB = a₀.coB ∧ (layLink W p a₀ c H kL v₀ E).rvT = a₀.rvT ∧
    (layLink W p a₀ c H kL v₀ E).rvB = a₀.rvB ∧ (layLink W p a₀ c H kL v₀ E).pvT = a₀.pvT ∧
    (layLink W p a₀ c H kL v₀ E).pvB = a₀.pvB ∧
    (layLink W p a₀ c H kL v₀ E).startT = a₀.startT ∧
    (layLink W p a₀ c H kL v₀ E).startB = a₀.startB :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- **The other eight.** Seven components are replaced, all the link's own: its honest prover and
decision, rvL, pvL, startL, kL, coL. -/
theorem layLink_rest_too :
    (layLink W p a₀ c H kL v₀ E).b₀ = a₀.b₀ ∧ (layLink W p a₀ c H kL v₀ E).nm = a₀.nm ∧
    (layLink W p a₀ c H kL v₀ E).RV = a₀.RV ∧ (layLink W p a₀ c H kL v₀ E).okV = a₀.okV ∧
    (layLink W p a₀ c H kL v₀ E).rtail = a₀.rtail ∧ (layLink W p a₀ c H kL v₀ E).fill = a₀.fill ∧
    (layLink W p a₀ c H kL v₀ E).dc.T = a₀.dc.T ∧ (layLink W p a₀ c H kL v₀ E).dc.B = a₀.dc.B :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The premise on v₀ cannot be dropped**: if v₀ is not well formed, PremW is false after the
substitution, whatever the other parameters. -/
theorem premW_layLink_needs_okV (hv : ¬ a₀.okV v₀) (Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop)
    (Ryes : I → X → Prop) (c' : CoinNums Bd) (N : NumsW) :
    ¬ PremW W Sd cA p (layLink W p a₀ c H kL v₀ E) Sm ok Gs Ryes c' N := fun hP => by
  obtain ⟨κ⟩ := (inferInstance : Nonempty (layLink W p a₀ c H kL v₀ E).Hs.Lk.Coin)
  exact hv (hP.coins.okL κ)

end

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.premW_layLink
#print axioms OnBytes.LinkSim.layLink_rest
#print axioms OnBytes.LinkSim.layLink_rest_too
#print axioms OnBytes.LinkSim.premW_layLink_needs_okV
