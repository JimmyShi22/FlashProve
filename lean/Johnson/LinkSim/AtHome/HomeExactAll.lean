-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/HomeExactAll.lean: the folder's main theorem, written out as one equation.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves. homeExactAt: at the library's full-size parameter set (dsFull), for every b,
all public files Z, every private input w of the link prover and every verifier message ρ, two
distributions are equal. The private input w is an index and, for each of the two tables, its
encoding randomness and its seed. The first distribution is the output of the explicit honest link
prover explicitLinkProver b Z at w, at the instance homeInst b Z w and at ρ. The second is the output of the
explicit simulator homeSim Z. No verifier message is excepted, and there is no premise and no error
term.
As the definition has it (Honest.HVZK, Iop/InteractiveOracleProof.lean), the simulator is given the instance, the
verifier's messages and the symbols of the input oracles at the queried positions. Here the instance
is the two tables' out-of-domain (OOD) samples, and the input oracles are the two encodings of the
index, queried at no more than 62 positions each (home_beside, HomeTies.lean). So what the prover
discloses to an honest verifier adds nothing to what these samples and symbols already disclose.

Z enters the link protocol HomeQ Z (defined in Johnson/LinkSim/AtHome/TwoViews.lean) only through
its verifier's decision, which the disclosed view does not contain (by inspection of these
definitions, not proved). That is why "for all public files Z" and "at one parameter set" do not
clash. homeExt b Z w, in homeExactAt, is (explicitLinkProver b Z).ext w, in homeExactAll, by definition. The
file is named for homeExactAll.

homeExactAll says the same with the instance x as a variable, under the premise that w and x are
valid (validLk, Johnson/LinkSim/Spec.lean, with both of its side conditions trivially true). By
valid_iff_homeInst, that premise holds exactly when x is homeInst b Z w.

How it fits. homeExact (Johnson/LinkSim/AtHome/Home.lean) is stated through ExactOff
(Johnson/LinkSim/Spec.lean), which excepts the verifier messages in the private part of the prover's
abort set (Hid). For explicitLinkProver b Z the whole abort set is empty (home_withheld,
Johnson/LinkSim/AtHome/TwoViews.lean). homeExactAll is homeExact's equation without that exception,
proved from homeExact and home_withheld. homeExactAt follows from it through homeExactAll_iff_at.

Names (namespace OnBytes.LinkSim.AtHome).
  homeInst             the honest instance of a private input: its two out-of-domain (OOD) samples.
  valid_iff_homeInst   w and x are valid exactly when x is homeInst b Z w.
  Spec.homeExactAt     the equation at the honest instance (statement only).
  Spec.homeExactAll    the equation at every valid pair (statement only).
  homeExactAll_iff_at  the two statements are equivalent.
  homeExactAll, homeExactAt   the two statements, proved.

Limits. The main theorem is not a statement that the index is hidden; that limit, and those on the
verifier, on hashing, on the three provers and on programs, are told once, in Home.lean's head. All
limits of homeExact apply; they are listed in Johnson/LinkSim/AtHome/Home.lean. This file adds none.

Sources. A statement here is covered by the note on sources in the head of Spec.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.Home
import Johnson.LinkSim.AtHome.TwoViews

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes.LinkSim (validLk)
open _root_.Iop (Rho InteractiveOracleProof Honest)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- The honest instance of a private input: the out-of-domain (OOD) samples of the first table and
of the copy. -/
def homeInst (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) : RecFull × RecFull :=
  ((homeR b Z).protocol.recOf w.1 w.2.1.1 w.2.1.2, (homeR b Z).protocol.recOf w.1 w.2.2.1 w.2.2.2)

/-- With both side conditions trivially true, a private input and an instance are valid exactly if
the instance is the honest one. -/
theorem valid_iff_homeInst (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (x : RecFull × RecFull) :
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x ↔ x = homeInst b Z w :=
  ⟨fun h => h.2.2.2, fun h => ⟨trivial, trivial, trivial, h⟩⟩

/-- Statement only; proved as homeExactAt below. At the honest instance and every verifier message,
the honest link prover's output and the simulator's output, given that instance, ρ and the input
oracles' symbols at the queried positions, are the same distribution. -/
def Spec.homeExactAt : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (ρ : Rho (HomeQ Z).shape),
    (explicitLinkProver b Z).output w (homeInst b Z w) ρ =
      homeSim Z (homeInst b Z w) ρ ((HomeQ Z).extAns (homeInst b Z w) ρ (homeExt b Z w))

/-- Statement only; proved as homeExactAll below. The same at every valid private input and
instance. -/
def Spec.homeExactAll : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (x : RecFull × RecFull),
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x →
    ∀ ρ : Rho (HomeQ Z).shape,
      (explicitLinkProver b Z).output w x ρ =
        homeSim Z x ρ ((HomeQ Z).extAns x ρ ((explicitLinkProver b Z).ext w))

/-- The two statements are equivalent. -/
theorem homeExactAll_iff_at : Spec.homeExactAll ↔ Spec.homeExactAt :=
  ⟨fun h b Z w ρ => h b Z w _ ((valid_iff_homeInst b Z w _).2 rfl) ρ,
    fun h b Z w x hv ρ => by
      rw [(valid_iff_homeInst b Z w x).1 hv]
      exact h b Z w ρ⟩

/-- **The same at every valid pair**: homeExact's equation at every verifier message, since the
abort set is empty (home_withheld). -/
theorem homeExactAll : Spec.homeExactAll :=
  fun b Z w x hv ρ =>
    homeExact b Z (fun _ => True) (fun _ => True) w x hv ρ (Set.notMem_empty ρ) fun h =>
      Set.eq_empty_iff_forall_notMem.1 (home_withheld b Z w x) ρ (Set.mem_union_right _ h)

/-- **The main theorem**: at the honest instance and every verifier message, the honest link
prover's output equals the simulator's output, given that instance, ρ and the input oracles' symbols
at the queried positions. -/
theorem homeExactAt : Spec.homeExactAt := homeExactAll_iff_at.1 homeExactAll

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.valid_iff_homeInst
#print axioms OnBytes.LinkSim.AtHome.homeExactAll_iff_at
#print axioms OnBytes.LinkSim.AtHome.homeExactAll
#print axioms OnBytes.LinkSim.AtHome.homeExactAt
