-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/TwoViews.lean: the honest output as a distribution of disclosed views
(output_home), the empty abort set (home_withheld), and a weak check that the disclosed view changes
when 1 is added to one cell of the index, at one verifier message (two_views).
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has. It supplies two things to the main theorem (homeExactAt,
Johnson/LinkSim/AtHome/HomeExactAll.lean): HomeQ Z, the link's protocol, which stands in that
theorem's statement; and home_withheld, which its proof uses. output_home says what the left side of
that theorem's equation is: at every verifier message ρ, (explicitLinkProver b Z).output w x ρ is the
distribution, over a uniform coin c, of the disclosed view homeView b Z w x c ρ, never none.
home_withheld: the explicit link prover's abort set is empty, by definition; this is the lemma
behind "the prover never aborts".

two_views, the weaker of the two checks (TwoPlains.lean has the stronger): the disclosed views
homeView at (w, x) and at (bumpWt b Z w, x') differ at the verifier message zeroAtHome Z c₀. This
holds for every private input w, all instances x and x', every coin c (the same on both sides) and
every c₀. bumpWt b Z w adds 1 at the cell (0, 0) of the index and keeps all randomness and seeds
(TwoIndices.lean).

Why. TwoIndices.lean speaks of the prover's algorithm (linkAll). Here the same is said of the
library's own notions: the strategy of explicitLinkProver b Z (Johnson/LinkSim/AtHome/SpecHome.lean), its run
against a verifier message as the protocol defines it, and the disclosed view of that run
(InteractiveOracleProof.dview, Iop/InteractiveOracleProof.lean), whose distribution over the coins is Honest.output.

How it fits. In this folder, TwoPlains.lean uses zeroAtHome, rs_of_plains, homeView and
home_withheld. HomeExactAll.lean states the main theorem with HomeQ and proves it with
home_withheld. HomeHVZK.lean and HomeDigest.lean use HomeQ too.

Names (namespace OnBytes.LinkSim.AtHome).
  rvSL_of_plains   the rounds of the format's view (Fmt.View, Fmt/View.lean; not the disclosed
                   view), as read off a transcript (rvSL, OnBytes/TypedOracleCompiler/Run/PlanQS.lean; "rounds" as
                   in Johnson/LinkSim/AtText/Defs.lean) depend on its plain parts and its verifier
                   messages alone. For all parameters.
  rs_of_plains     at the full-size parameters, for any two data and coins and one verifier message:
                   if the runs of the strategies at the two have the same plain parts, the
                   algorithm's outputs at the two have the same rounds.
  HomeQ Z          the link's protocol at homeR b Z (linkProtocolOfRoundData, OnBytes/Flat/LinkSib.lean).
  homeView         the disclosed view of the run of (explicitLinkProver b Z).strat w x c against ρ.
  zeroAtHome Z c₀  the verifier message (c₀, zeroRho dsFull). c₀ is the value of the trivial first
                   round, in which nothing is sent and whose verifier message nothing reads; it has
                   only one possible value (CK.front, Run/PlanQTypes.lean). In every later round,
                   all of the verifier's hash blocks and proof-of-work bits are 0
                   (Johnson/LinkSim/AtText/ZeroDraws.lean).
  two_views, home_withheld, output_home   above.
  two_views_valid  the form with two valid private inputs, weaker than two_views in every binder but
                   the coin's. There are two valid private inputs with their instances, the same
                   randomness and seeds and different indices. There is also a verifier message
                   outside both abort sets at which, at every coin, the two disclosed views differ.
                   Its two conditions on the abort sets hold trivially: these sets are empty
                   (home_withheld). The instances may differ.

Proof uses: the disclosed view holds the plain parts; rv_run (Johnson/Prover/Link/LinkFrame.lean);
rs_full (Johnson/Prover/Link/LinkJoinA.lean), which uses that each item that the algorithm writes
has the kind that its round declares; two_fronts (TwoIndices.lean).

Limits.
- By their statements, two_views and two_views_valid say that two disclosed views differ. A view
  also holds the symbols read in the encoded indices, which are no message. A prover that sends
  fixed messages, with the same input oracles, could satisfy these statements too (by inspection,
  not proved). So, as a check against "the messages are constant in the index", these two could pass
  at such a prover. What says that a message changes: two_plains
  (Johnson/LinkSim/AtHome/TwoPlains.lean), which such a prover does not satisfy (plains_fixed,
  there); and, for the algorithm, answer_home and two_fronts (TwoIndices.lean).
- The two views differ coin by coin; of the two outputs, which are distributions over the coins,
  nothing follows. Told in TwoPlains.lean's limits: that limit; one verifier message; one change of
  one cell; which plain part differs is not in the statement (by TwoIndices.lean, the first answer
  of the third round); and what "valid" means in the form with two valid inputs.
- The statements are for every matrix of the index type. That a model's weights are such a matrix is
  not stated in this folder (Spec.lean, "index").

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.TwoIndices
import Johnson.Prover.Link.LinkJoinA

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
open OnBytes.LinkSim.AtText
open Johnson.Prover.Link
open _root_.Desc.K15 (frP)
open _root_.Iop (Rho Tr Strat InteractiveOracleProof DView Honest)
open _root_.Run (ckP)
open PV.EntryFive (dsF xsF)
open _root_.Run.PQ (CK)
open TypedOracleCompiler.Run.PQ (RD SOf uL drawnSL rvSL)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-! ## For all parameters -/

/-- The rounds of the format's view (not the disclosed view), as read off a transcript, depend on
its plain parts and its verifier messages alone. -/
theorem rvSL_of_plains (C : CK) : ∀ (ds : List RD) (τ τ' : Tr (uL C ds)),
    τ.plains = τ'.plains → τ.rho = τ'.rho → rvSL C ds τ = rvSL C ds τ'
  | [], _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), hp, hr => by
    have h1 : m.2 = m'.2 := congrArg Prod.fst hp
    have h2 : τ.plains = τ'.plains := congrArg Prod.snd hp
    have h3 : c = c' := congrArg Prod.fst hr
    have h4 : τ.rho = τ'.rho := congrArg Prod.snd hr
    show _ :: rvSL C ds τ = _ :: rvSL C ds τ'
    rw [h1, h3, rvSL_of_plains C ds τ τ' h2 h4]

/-! ## At the full-size parameters -/

/-- If the runs of the strategies at two data and coins have the same plain parts, the algorithm's
outputs at the two have the same rounds. -/
theorem rs_of_plains (t : ℕ) (X X' : LIn frS) (C C' : LCoins)
    (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsFull)))
    (h : ((stratOf (ckP .two) dsFull (linkNext frP frS t X C)).run ρ).1.plains =
      ((stratOf (ckP .two) dsFull (linkNext frP frS t X' C')).run ρ).1.plains) :
    (linkAll frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ.2))).rs =
      (linkAll frP frS t X' C' (drawsOf (drawnSL (ckP .two) dsFull ρ.2))).rs := by
  obtain ⟨c₀, ρ'⟩ := ρ
  have h2 : ((stratSL (ckP .two) dsFull 0 [] (linkNext frP frS t X C)).run ρ').1.plains =
      ((stratSL (ckP .two) dsFull 0 [] (linkNext frP frS t X' C')).run ρ').1.plains :=
    congrArg Prod.snd h
  have h3 := rvSL_of_plains (ckP .two) dsFull _ _ h2
    ((Strat.rho_run _ ρ').trans (Strat.rho_run _ ρ').symm)
  rw [rv_run, rv_run, rs_full, rs_full] at h3
  exact h3

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- The link's protocol at homeR b Z. -/
abbrev HomeQ (Z : PublicFiles) :
    InteractiveOracleProof (RecFull × RecFull) (_root_.Iop.twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX) :=
  linkProtocolOfRoundData (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec

/-- **The disclosed view of the run of the explicit link prover's strategy**, at a private input, an
instance, a coin and a verifier message. -/
def homeView (w : HomeWt b Z) (x : RecFull × RecFull) (c : Kc) (ρ : Rho (HomeQ Z).shape) :
    DView (HomeQ Z) :=
  (HomeQ Z).dview x ((explicitLinkProver b Z).ext w) (((explicitLinkProver b Z).strat w x c).run ρ).1

/-- The verifier message whose hash blocks and proof-of-work bits after the trivial first round are
all 0. -/
def zeroAtHome (Z : PublicFiles) (c₀ : (_root_.Run.PQ.s0 (ckP .two)).up.Chal) : Rho (HomeQ Z).shape :=
  (c₀, zeroRho dsFull)

/-- **The disclosed views at w and at bumpWt b Z w differ**, at every coin, at the verifier message
zeroAtHome Z c₀. -/
theorem two_views (w : HomeWt b Z) (x x' : RecFull × RecFull) (c : Kc)
    (c₀ : (_root_.Run.PQ.s0 (ckP .two)).up.Chal) :
    homeView b Z w x c (zeroAtHome Z c₀) ≠ homeView b Z (bumpWt b Z w) x' c (zeroAtHome Z c₀) := by
  intro h
  have hrs := rs_of_plains 97 (homeIn b Z w x) (homeIn b Z (bumpWt b Z w) x') (coinsFull c)
    (coinsFull c) (c₀, zeroRho dsFull) (congrArg DView.plains h)
  have hrs' : (linkAll frP frS 97 (homeIn b Z w x) (coinsFull c) drawsZero).rs =
      (linkAll frP frS 97 (homeIn b Z (bumpWt b Z w) x') (coinsFull c) drawsZero).rs := hrs
  rw [linkAll_rs_at fr_cons, linkAll_rs_at fr_cons, List.append_assoc, List.append_assoc] at hrs'
  exact two_fronts b Z w x x' (coinsFull c)
    (List.append_inj hrs' ((length_lFront _ _).trans (length_lFront _ _).symm)).1

/-- The explicit link prover's abort set is empty. -/
theorem home_withheld (w : HomeWt b Z) (x : RecFull × RecFull) :
    (explicitLinkProver b Z).withheld w x = ∅ := linkRec_withheld _ _ _ _ _ _ _ w x

/-- The output is the distribution of the disclosed view over a uniform coin. -/
theorem output_home (w : HomeWt b Z) (x : RecFull × RecFull) (ρ : Rho (HomeQ Z).shape) :
    (explicitLinkProver b Z).output w x ρ =
      (Prob.unif Kc).map fun c => some (homeView b Z w x c ρ) := by
  unfold Honest.output
  rw [if_neg (Set.eq_empty_iff_forall_notMem.1 (home_withheld b Z w x) ρ)]
  rfl

/-- The form with two valid private inputs: weaker than two_views in every binder but the coin's;
its two conditions on the abort sets hold trivially. -/
theorem two_views_valid : ∃ (w w' : HomeWt b Z) (x x' : RecFull × RecFull),
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x ∧
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w' x' ∧
    w'.1 ≠ w.1 ∧ w'.2 = w.2 ∧
    ∃ ρ : Rho (HomeQ Z).shape,
      ρ ∉ (explicitLinkProver b Z).withheld w x ∧ ρ ∉ (explicitLinkProver b Z).withheld w' x' ∧
      ∀ c : Kc, homeView b Z w x c ρ ≠ homeView b Z w' x' c ρ := by
  obtain ⟨w⟩ := home_wt_nonempty b Z
  obtain ⟨c₀⟩ := (_root_.Run.PQ.s0 (ckP .two)).up.neChal
  have hv : ∀ u : HomeWt b Z, ∃ y : RecFull × RecFull,
      validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) u y :=
    fun _ => ⟨_, trivial, trivial, trivial, rfl⟩
  obtain ⟨x, hx⟩ := hv w
  obtain ⟨x', hx'⟩ := hv (bumpWt b Z w)
  exact ⟨w, bumpWt b Z w, x, x', hx, hx',
    bumpCell_ne frS frZ 402653181 numsRef fr_rowsPos w.1, rfl, zeroAtHome Z c₀,
    Set.eq_empty_iff_forall_notMem.1 (home_withheld b Z w x) _,
    Set.eq_empty_iff_forall_notMem.1 (home_withheld b Z (bumpWt b Z w) x') _,
    fun c => two_views b Z w x x' c c₀⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.home_withheld
#print axioms OnBytes.LinkSim.AtHome.output_home
#print axioms OnBytes.LinkSim.AtHome.two_views_valid
#print axioms OnBytes.LinkSim.AtHome.rvSL_of_plains
#print axioms OnBytes.LinkSim.AtHome.rs_of_plains
#print axioms OnBytes.LinkSim.AtHome.two_views
