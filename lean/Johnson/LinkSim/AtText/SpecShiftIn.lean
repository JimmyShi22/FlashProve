-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SpecShiftIn.lean: the statement on the two algorithms that the proof chain
uses, in the form that carries over to a finite type of coins. Definitions and two statements.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

No proof here: bodyShiftOr is proved in Induct.lean, linkShiftIn in LinkShift.lean.

The statement (Spec.linkShiftIn). For all data X and all challenges D, under the public premises on
sizes (Sizes, Johnson/LinkSim/AtText/SpecShift.lean) and one premise on the honest run: what the
prover's algorithm (linkAll) and the simulator's algorithm (simAll) disclose (shownOf,
SpecShift.lean) agrees up to a shift of the coin variables that can be undone, at the coin variables
that are in the places (InPlaces, Johnson/LinkSim/AtText/Places.lean), and what is added is in the
places too (UpToShiftOn, Johnson/LinkSim/UpToOn.lean).

How it differs from Spec.linkShift (SpecShift.lean), whose place on the proof chain it takes.
  Its conclusion says more in one way: what is added is in the places. Without that, the step down
      to a finite type of coins cannot be made (comap_needs_fence, Johnson/LinkSim/UpToIn.lean).
      Nor can it be added afterwards, since in Spec.linkShift the shift is under "there exists".
  Its conclusion says less in one way: it speaks only of coin variables in the places. The step
      down uses no more (UpToShiftOn.comap).
  Its premise on the honest run asks less, twice: only at coin variables in the places, and only
      where the element that the base case's first round samples is not 0. Where it is 0, the
      verifier's last equation does not read the claim's target, and the two first elements agree
      without the premise.
  So, as stated in Lean, neither statement follows from the other.

The other names (namespace OnBytes.LinkSim.AtText).
  LamZero D e        the element that the base case's first round sampled is 0 (the base case is
                     the last stage's two rounds).
  Spec.bodyShiftOr   Spec.bodyShift (Johnson/LinkSim/AtText/SpecStage.lean) with that weaker
                     premise.

How it fits. LinkShift.lean proves Spec.linkShiftIn; SeamClaim.lean proves its premise on the honest
run at the full-size parameters (fr_claimPremise), and SeamAtFull3.lean its premises on sizes
(fr_sizes). Spec.linkShiftIn is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).

Limits.
- Its conclusion is not to be read as holding "at all challenges". D runs over all families of
  challenges, also ones that no verifier message of the protocol gives. Where the sampled factor of
  a seed (of the link proof's own OOD samples) is 0, the prover's algorithm takes 1 in its place
  (unitOf); nothing here says that the verifier's state does the same. There the premise on the
  honest run may fail, and the statement is then vacuous, not false. Whoever proves that premise at
  the protocol's challenges needs "a sampled factor is not 0". SeamFactors.lean proves that the
  factor is not 0 at the full-size rounds that sample a seed, for challenges as hash blocks over the
  field GF (ckP .two). SeamClaim.lean proves the premise at the full-size parameters, for data that
  satisfy Meant, through the honest prover's invariant.
- It covers an honest verifier and one link (the verifier: Johnson/LinkSim/AtHome/Home.lean's
  limits; one link: SpecExact.lean's limits).
- The coins are variables on all natural numbers; no finite type of coins and no distribution is
  here.
- At the full-size parameters, one position more at a stage makes the premises on sizes fail and the
  statement vacuous (see Notes). A tree opened twice is not modelled here (sched, SeamGroups.lean).

Notes. The premises on sizes hold at the full-size parameters with nothing to spare: at every stage,
for both codes, as many positions are sampled as a row's tail is long (fr_cnts and fr_tails,
Johnson/LinkSim/AtText/SeamAtFull3.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Places
import Johnson.LinkSim.UpToOn

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open Johnson.Prover.Link

/-- The element that the base case's first round sampled is 0. -/
def LamZero (D : ℕ → Fmt.Drawn) (e : BEnd) : Prop := toE ((D e.o).elems.headD (0, 0, 0)) = 0

/-- Statement only; proved as bodyShiftOr in Induct.lean. **Along the stages**, with the premise on
the claim asked only where that element is not 0. -/
def Spec.bodyShiftOr : Prop :=
  ∀ (p : P12) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (Kr Ks : BCoins) (Pr Ps d : PS) (colr cols : ℕ → List UInt64),
    FitsBody D rest cur o → AtStage p D rest j cur l o t Kr Ks Pr Ps d colr cols →
    (LamZero D (bodyEnd p Kr D rest j cur l o t Pr colr) ∨
      ClaimTrue p (bodyEnd p Kr D rest j cur l o t Pr colr)) →
    (bodyAll p Kr rest j cur l o t Pr colr D).gs = (bodyAll p Ks rest j cur l o t Ps cols D).gs ∧
      (bodyAll p Kr rest j cur l o t Pr colr D).rs =
        (bodyAll p Ks rest j cur l o t Ps cols D).rs.set
          ((bodyEnd p Ks D rest j cur l o t Ps cols).o - o)
          ⟨[.e (tauStar p (bodyEnd p Ks D rest j cur l o t Ps cols) D)],
            D (bodyEnd p Ks D rest j cur l o t Ps cols).o⟩

/-- Statement only; proved as linkShiftIn in LinkShift.lean. **The two algorithms disclose the same
up to a shift of the coins that can be undone, at coins that are 0 outside the places, with a shift
that is 0 outside them too**, under Sizes and the weaker premise on the honest run. -/
def Spec.linkShiftIn : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (D : ℕ → Fmt.Drawn),
    Sizes P S t D →
    (∀ C, InPlaces P S C → ∀ e, linkEnd P S t X C D = some e →
      LamZero D e ∨ ClaimTrue (p12Of P) e) →
    UpToShiftOn addC (InPlaces P S) (InPlaces P S) (fun C => shownOf (linkAll P S t X C D))
      (fun C => shownOf (simAll P S t X C D))

end OnBytes.LinkSim.AtText
