-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamFree.lean: what the link's honest prover satisfies by its form alone, for
all parameters.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

Under Johnson/LinkSim/ no file calls the four statements of this file.

What this file proves. The link's honest prover in general form is linkRec C ds a xs dec ext next
(Johnson/Prover/Link/LinkFrame.lean). Its type of coins, its input oracles (ext) and its
next-message function (next) are variables. Both parts of its abort set are empty by definition.
Four statements follow from this form alone, for all parameters:
  Spec.linkStops, linkStops        for any map z of the verifier messages, the set of verifier
               messages ρ with z ρ in Hid, the part of the abort set that may depend on the private
               input, has probability 0 under uniform ρ.
  Spec.linkNotHid, linkNotHid      no verifier message lies in that part, nor in the whole abort
               set.
  Spec.linkExt, linkExt            the prover's input oracles are the variable ext.
  Spec.linkRunVals, linkRunVals    suppose the run value read off the plain parts is one fixed
               value, and the run value of every coin is that value. Then the two agree at every
               run.

How it fits. The premises of index privacy ask four things of the link's honest prover, besides a
simulator: StopsSmall, ExtEnc, RunVals, and "outside the abort set" in Sims.Good
(Johnson/WholeKey/Premises.lean). This file proves what of these follows from the prover's form.
What the premises ask of its coins' enumeration and of the compilation data is LinkCompile
(Johnson/LinkSim/AtHome/CompileSpec.lean). The explicit prover explicitLinkProver b Z has this form: it is
defined by linkSide (Johnson/LinkSim/AtText/SpecExact.lean), which is linkRec at linkNext, and
homeSide_is (Johnson/LinkSim/AtHome/SpecHome.lean) writes it out.

Limits.
- linkRunVals covers only the trivial case: it says nothing of run values that depend on a coin.
- That ext is the pair of encoded indices is the choice of whoever substitutes it; homeExt
  (Johnson/LinkSim/AtHome/SpecHome.lean) substitutes it so.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkFrame

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open Prob
open OnBytes.Flat (linkProtocolOfRoundData)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO SgX)
open TypedOracleCompiler.Run.PQ (RD)

/-- Statement only; proved as linkStops below. Under any map z of the verifier messages, the set of
ρ with z ρ in the honest prover's Hid has probability 0. -/
def Spec.linkStops : Prop :=
  ∀ (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (X : Type) (dec : X → View → Bool)
    (Wt Kc : Type) [Fintype Kc] [Nonempty Kc] (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str)
    (next : Wt → X → Kc → ℕ → List Fmt.Drawn → MsgV) (w : Wt) (x : X)
    (z : Rho (linkProtocolOfRoundData C ds a xs dec).shape → Rho (linkProtocolOfRoundData C ds a xs dec).shape),
    pr (unif (Rho (linkProtocolOfRoundData C ds a xs dec).shape))
      {ρ | z ρ ∈ (linkRec C ds a xs dec ext next).Hid w x} = 0

theorem linkStops : Spec.linkStops := by
  intro C ds a xs X dec Wt Kc _ _ ext next w x z
  have e : {ρ | z ρ ∈ (linkRec C ds a xs dec ext next).Hid w x} =
      (∅ : Set (Rho (linkProtocolOfRoundData C ds a xs dec).shape)) := rfl
  rw [e]
  exact Prob.pr_empty _

/-- Statement only; proved as linkNotHid below. No verifier message lies in Hid or in the whole
abort set. -/
def Spec.linkNotHid : Prop :=
  ∀ (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (X : Type) (dec : X → View → Bool)
    (Wt Kc : Type) [Fintype Kc] [Nonempty Kc] (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str)
    (next : Wt → X → Kc → ℕ → List Fmt.Drawn → MsgV) (w : Wt) (x : X)
    (ρ : Rho (linkProtocolOfRoundData C ds a xs dec).shape),
    ρ ∉ (linkRec C ds a xs dec ext next).Hid w x ∧
      ρ ∉ (linkRec C ds a xs dec ext next).withheld w x

theorem linkNotHid : Spec.linkNotHid := by
  intro C ds a xs X dec Wt Kc _ _ ext next w x ρ
  refine ⟨fun h => h, fun h => ?_⟩
  rw [linkRec_withheld] at h
  exact h

/-- Statement only; proved as linkExt below. The prover's input oracles are ext. -/
def Spec.linkExt : Prop :=
  ∀ (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (X : Type) (dec : X → View → Bool)
    (Wt Kc : Type) [Fintype Kc] [Nonempty Kc] (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str)
    (next : Wt → X → Kc → ℕ → List Fmt.Drawn → MsgV) (w : Wt),
    (linkRec C ds a xs dec ext next).ext w = ext w

theorem linkExt : Spec.linkExt := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- Statement only; proved as linkRunVals below. If both run values are one fixed value, they agree
at every run. -/
def Spec.linkRunVals : Prop :=
  ∀ (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (X : Type) (dec : X → View → Bool)
    (Wt Kc : Type) [Fintype Kc] [Nonempty Kc] (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str)
    (next : Wt → X → Kc → ℕ → List Fmt.Drawn → MsgV) (RV : Type) (v : RV)
    (pv : Plains (linkProtocolOfRoundData C ds a xs dec).shape → RV) (rv : Kc → RV),
    (∀ π, pv π = v) → (∀ κ, rv κ = v) →
    ∀ w x κ ρ, pv (((linkRec C ds a xs dec ext next).strat w x κ).run ρ).1.plains = rv κ

theorem linkRunVals : Spec.linkRunVals :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hr _ _ κ _ => (hp _).trans (hr κ).symm

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.linkStops
#print axioms OnBytes.LinkSim.Seam.linkNotHid
#print axioms OnBytes.LinkSim.Seam.linkExt
#print axioms OnBytes.LinkSim.Seam.linkRunVals
