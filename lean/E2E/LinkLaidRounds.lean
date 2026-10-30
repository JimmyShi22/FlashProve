-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LinkLaidRounds.lean: with the explicit link prover substituted, the rounds that a produced link
proof's hashed transcript gives to the link's decision are that prover's own rounds, item for item,
at the samples that the oracle functions gave.

Summary. E2E/StringsPlain.lean proves that a produced proof has the plain parts of a transcript that
is the prover's own run, up to what `put` writes. In the link's wiring `put` writes a nonce, a
component of its own beside a round's items. The decision's view (`Run.PQ.View`: what the link's
decision is given) does not hold the nonce: this is the library's `shown_SL`
(Johnson/Prover/Link/LinkFrame.lean), whose docstring says: "So the decision's view (viewX) holds no
nonce." The proof does hold it: π.plains has the nonces, and whoever is given the proof reads them.
So for the items an equation can be proved. It holds for all oracle functions and all coins. No
probability occurs.

Main results.
  `laid_rounds`: `LinkRoundsAt` holds for `laidAt`, for every b and every Z, with no premise.
  `LinkRoundsAt b Z a lay` states, at `homeR b Z`: for every index, all oracle functions, all the
    committer's coins and every copy whose link proof π in the key is produced, there is a τ with:
    the compiled link prover, at the scheme's own terms, returns (π, τ) under g (a run under g has
    one value, so it is the τ of AtFullSide/E2E/LinkLaidHashedAccepted.lean) · π.plains = τ.plains ·
    the verifier's chain on π's own fields yields τ.rho · the rounds read off τ are the field rs of
    `linkAll frP frS 97` at `homeIn` of the index, both tables' randomness, OOD seeds and OOD
    samples, at the copy's coin and at τ's samples.
  `laid_rounds_at`: the equation of rounds for an arbitrary τ: for `laidAt`, any index, randomness,
    OOD seeds and coin, from `PlainAt` of π and τ for the strategy that the scheme plays for a link.
    No other premise.
  `rounds_of_plain`: the same for an arbitrary link protocol (kit C, rounds' data ds, a, xs, dec),
    its wiring `wqW` at any K and chal, and any function `next` that gives the messages: if
    `PlainAt` holds of π and τ for the strategy `stratOf C ds next`, then `rvSL C ds` of τ after the
    trivial first round is `rvOf ds 0 [] next` at the samples of τ's verifier messages. By
    `shown_SL` and `rv_run`.

Terms: E2E/HidingTerms.lean.

Limits.
- The result is for a produced link proof. How often one is produced is proved in
  E2E/LinkLaidPrivacy.lean, for public files in scope alone: out of scope nothing proves that a link
  proof is ever produced, and this statement may be vacuous there. No theorem here joins the two.
- It concerns the rounds' items and samples (`rvSL`): not the oracle messages and not the opened
  columns. Nothing is stated about the nonces' values: they are removed on both sides.
- `rvSL` reads only a transcript's plain parts and verifier messages (`rvSL_of_plains`,
  Johnson/LinkSim/AtHome/TwoViews.lean).
- One of three sub-protocols: the provers for the first table's proof and for the sessions are
  placeholders, which send each round's fixed message. One input: `homeR b Z`. That `VerifierAndGoals.verify`
  is ever called at this input is not proved.
- One step of the compiled verifier, its chain: not that it accepts the proof. The model:
  E2E/HidingTerms.lean.
- It builds on files of Johnson/LinkSim/.
- Nothing on completeness as such, on soundness or on what is hidden.

Definitions and helper lemmas.
  `rounds_home`, `home_strat`: `rounds_of_plain` at the link's protocol and wiring of `homeR b Z`,
    for an arbitrary function that gives the messages; the explicit link prover's strategy is
    `stratOf` of `linkNext frP frS 97` at `homeIn` and `coinsFull`. `laid_rounds` follows from
    these, `link_hashed` (E2E/StringsPlain.lean; its `WiresFit` holds at that input by `fits_home`)
    and `rs_full` (Johnson/Prover/Link/LinkJoinA.lean).


-/
import E2E.LinkLaidPrivacy
import E2E.StringsPlain
import Johnson.LinkSim.AtHome.TwoViews

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.LinkLaid
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.Shown
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData homeR)
open OnBytes.Flat OnBytes.Slice
open Johnson.Prover.Link
open Johnson.RunOne.StrictW (wqW)
open _root_.Desc.K15 (frP)
open _root_.Run (ckP)
open PV.EntryFive (dsF xsF)
open _root_.Run.PQ (CK XO View)
open TypedOracleCompiler.Run.PQ (RD SOf uL drawnSL rvSL wiresSL)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-! ## 1. For an arbitrary link protocol -/

theorem rounds_of_plain (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) {X : Type}
    (dec : X → View → Bool) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (next : ℕ → List Fmt.Drawn → MsgV) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up)
    (cap : ℕ → ℕ) (τ : Tr (_root_.Run.Twin.up (SOf C ds)))
    (hp : PlainAt (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) (stratOf C ds next) cap π
      τ) :
    rvSL C ds τ.2.2 = rvOf ds 0 [] next (drawnSL C ds (Tr.rho τ.2.2)) := by
  have hP := hp.puts
  obtain ⟨m0, c0, τ⟩ := τ
  have hP2 : Puts _ _ (wiresSL C K chal ds) ((stratSL C ds 0 [] next).run (Tr.rho τ)).1 τ :=
    hP.2.2.2
  obtain ⟨e1, -, -⟩ := shown_SL C K chal ds _ τ hP2
  exact e1.trans (rv_run C next ds 0 [] _)

/-! ## 2. With the explicit link prover substituted -/

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- The first, at the link's protocol and wiring of that input, for an arbitrary function that gives
the messages. -/
theorem rounds_home (nx : ℕ → List Fmt.Drawn → MsgV) (cap : ℕ → ℕ)
    (π : OneProtocolProof 256 (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits)) (τ : Tr (HomeQ Z).shape)
    (hp : PlainAt (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits) (wLC (homeR b Z).queryLayout)
      (stratOf (ckP .two) dsF nx) cap π τ) :
    rvSL (ckP .two) dsF τ.2.2 = rvOf dsF 0 [] nx (drawnSL (ckP .two) dsF (Tr.rho τ.2.2)) :=
  rounds_of_plain (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
    (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (_root_.Run.chalP .two _) nx π cap τ
    hp

/-- The explicit link prover's strategy, in the form `stratOf`. -/
theorem home_strat (w : HomeWt b Z) (x : RecFull × RecFull) (κ : Kc) :
    (explicitLinkProver b Z).strat w x κ =
      stratOf (ckP .two) dsF (linkNext frP frS 97 (homeIn b Z w x) (coinsFull κ)) := rfl

/-- The statement that `laid_rounds` proves: see the header. -/
def LinkRoundsAt
    (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (lay : a.side.KL → LCoins) : Prop :=
  ∀ (g : Fam (typedOracleFamily 256 (homeR b Z).queryLayout.K
      (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits))) (i : (homeR b Z).Index)
    (c : DrawC 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits a.side.KT a.side.KL)
    (j : ℕ) (e : DrawCopy 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits a.side.KL),
    c.copies[j]? = some e →
    ∀ l : Dig 256 × (homeR b Z).protocol.Rec × Option (OneProtocolProof 256 (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits)),
      ((commitAt (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode a.side i c).det g).1.links[j]? =
        some l →
      ∀ π : OneProtocolProof 256 (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits), l.2.2 = some π →
        ∃ τ : Tr (HomeQ Z).shape,
          (proveLA (homeR b Z).queryLayout (homeR b Z).answerCode
            (fun k => if k = 0 then (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).tree
              else (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).tree)
            (a.side.dressL (a.side.rvL e.κ) e.co) a.side.capL
            (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).tree.root
            (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).tree.root
            ((homeR b Z).protocol.recOf i c.r (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).seed)
            ((homeR b Z).protocol.recOf i e.r (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).seed)
            ((homeR b Z).protocol.encodeIndex i c.r, (homeR b Z).protocol.encodeIndex i e.r)
            (a.side.st.Lk i (c.r, (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).seed)
              (e.r, (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).seed) e.κ)).det g =
            .ok (π, τ) ∧
          π.plains = τ.plains ∧
          (∃ Rt ph, TypedOracleCompiler.Run.chainF g _root_.Compile.Tag.link
            (cmsLA (homeR b Z).answerCode
              (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).tree.root
              (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).tree.root
              ((homeR b Z).protocol.recOf i c.r
                (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).seed).2
              ((homeR b Z).protocol.recOf i e.r
                (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).seed).2) none π.salt π.rtreq
            (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits).loc.shape (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits).ann
            (wLC (homeR b Z).queryLayout).sh id 0 .first π.roots π.plains = some (Tr.rho τ, Rt, ph)) ∧
          rvSL (ckP .two) dsF τ.2.2 =
            (linkAll frP frS 97
              (homeIn b Z
                (i, (c.r, (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).seed),
                  (e.r, (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).seed))
                ((homeR b Z).protocol.recOf i c.r
                    (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i c.r c.s).seed,
                  (homeR b Z).protocol.recOf i e.r
                    (tabG (homeR b Z).queryLayout (homeR b Z).seedQueries a.side g i e.r e.s).seed))
              (lay e.κ) (drawsOf (drawnSL (ckP .two) dsF (Tr.rho τ.2.2)))).rs

set_option maxHeartbeats 1600000 in
/-- **The equation of rounds, for an arbitrary transcript.** -/
theorem laid_rounds_at (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (i : (homeR b Z).Index)
    (u v : (homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed) (κ : Kc)
    (π : OneProtocolProof 256 (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits)) (τ : Tr (HomeQ Z).shape)
    (hp : PlainAt (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits) (wLC (homeR b Z).queryLayout)
      ((laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.st.Lk i u v κ)
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.capL π τ) :
    rvSL (ckP .two) dsF τ.2.2 =
      (linkAll frP frS 97
        (homeIn b Z (i, u, v) ((homeR b Z).protocol.recOf i u.1 u.2, (homeR b Z).protocol.recOf i v.1 v.2))
        (coinsFull κ) (drawsOf (drawnSL (ckP .two) dsF (Tr.rho τ.2.2)))).rs := by
  rw [laid_plays, home_strat] at hp
  exact (rounds_home b Z _ _ π τ hp).trans (rs_full 97 _ _ _)

set_option maxHeartbeats 1600000 in
/-- **For every b and every Z.** -/
theorem laid_rounds (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) :
    LinkRoundsAt b Z (laidAt b Z b₀ M ℓ ℓr capT capL capB E) coinsFull := by
  intro g i c j e hj l hl π hπ
  obtain ⟨τ, hτ, hp, -, hh⟩ := link_hashed (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side g (fits_home b Z).2 i c j e hj l hl π hπ
  exact ⟨τ, hτ, hp.1, hh, laid_rounds_at b Z b₀ M ℓ ℓr capT capL capB E i _ _ e.κ π τ hp⟩

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.rounds_of_plain
#print axioms AtPublicFiles.LinkLaid.rounds_home
#print axioms AtPublicFiles.LinkLaid.home_strat
#print axioms AtPublicFiles.LinkLaid.laid_rounds_at
#print axioms AtPublicFiles.LinkLaid.laid_rounds
