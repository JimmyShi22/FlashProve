-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/TwoPlains.lean: the link prover's clear messages do not ignore the index:
adding 1 to one cell changes them, at one verifier message, at every coin.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves. This file guards homeExact against a vacuous reading: homeExact does not
speak of a prover whose messages ignore the index. two_plains: adding 1 to cell (0, 0) of the index
changes what the prover sends in the clear, at the verifier message whose hash blocks are all 0.
That holds for every private input, all instances and every coin. A placeholder prover that sends
fixed messages fails the same statement (silent_not_two_plains).

In detail. explicitLinkProver b Z is the explicit honest link prover at homeR b Z (Spec.lean's terms).
bumpWt b Z w adds 1 at the cell (0, 0) of the index and keeps all randomness and seeds
(TwoIndices.lean). The instances x and x' of the two runs need not be valid, and there is no
premise. The coin c is the same on both sides. The verifier message is zeroAtHome Z c₀
(TwoViews.lean).

Why the plain parts. TwoViews.lean proves that two disclosed views differ. But a disclosed view
(Spec.lean's terms) also holds the symbols that the verifier reads in the input oracles, which are
no message of the prover. So a prover whose messages depend on nothing could still have two views
that differ. This file therefore compares the plain parts: what the prover sends in the clear in
each round.

How it fits. TwoIndices.lean proves a more specific fact for the prover's algorithm (linkAll). When
1 is added to the cell (0, 0), the first answer in the clear changes by exactly 1, at the one
verifier message and at every coin (answer_home). This file carries the change over to the prover's
strategy as the protocol defines it, (explicitLinkProver b Z).strat. Nothing in this folder uses this file: it
is a check that stands beside homeExact (Johnson/LinkSim/AtHome/Home.lean).

Names (namespace OnBytes.LinkSim.AtHome).
  homePlains        the plain parts of one run of (explicitLinkProver b Z).strat w x c against the verifier
                    message ρ.
  homeView_plains   they are the first field of the disclosed view homeView (TwoViews.lean), by
                    definition.
  two_plains        the main statement, above.
  two_plains_same   its case x' = x. The instance is the same on both sides, so the change does
                    not come from the instance. Where the two inputs' OOD samples differ, that
                    instance is valid for at most one of them. Validity is not a premise here.
  two_plains_valid  the weakest of the three forms, in every binder but the coin's. There are two
                    valid private inputs with their instances, with the same randomness and seeds
                    and different indices. There is also a verifier message outside both abort
                    sets (withheld) at which, at every coin, the plain parts differ. Its two
                    conditions on the abort sets hold trivially: these sets are empty here
                    (home_withheld, TwoViews.lean). The two instances may differ.
  plains_const, plains_fixed, plains_silent   negative tests: a prover whose messages depend on
                    nothing does not satisfy this statement. Against one verifier message, the plain
                    parts of its runs are the same at all private inputs, instances and coins.
                    plains_const: in general form, for every honest prover whose strategy is the
                    same at all private inputs, instances and coins. plains_fixed: its case for the
                    library's one strategy of fixed messages (Strat.dflt, Iop/Shape.lean).
                    plains_silent: hence for the link part of the placeholder provers (silent,
                    Johnson/WholeKey/Foes.lean), for every protocol structure.
  silent_not_two_plains   the statement can fail. At homeR b Z's own protocol structure, put the
                    placeholder link prover in place of explicitLinkProver b Z. Then, at the same private
                    inputs, instances and verifier message, the statement of two_plains is false.

Proof uses: rs_of_plains (TwoViews.lean); linkAll_rs_at (Johnson/LinkSim/AtText/LinkShift.lean);
fr_cons (Johnson/Prover/Link/LinkAtFull.lean); length_lFront
(Johnson/LinkSim/AtText/TwoAnswers.lean); two_fronts (Johnson/LinkSim/AtHome/TwoIndices.lean).

Limits.
- At each coin the two values of the plain parts differ. Nothing follows about distributions over
  the coins: two families of points that differ coin by coin can have the same distribution.
- The statement rules out a strategy that does not read the private input. It does not rule out one
  that repeats what the verifier reads in the encodings anyway. That the first answer is no such
  symbol is by inspection, not proved; answer_home (TwoIndices.lean) proves only that it changes.
- Only one verifier message is covered: zeroAtHome Z c₀.
- Only one change of the index is covered: 1 added at the cell (0, 0).
- Only a change through the first table is proved, through one item of the messages. That the
  messages depend on the copy's table and on both tables' randomness is by inspection, not proved.
- No statement here has both private inputs valid at one instance.
- "Valid" in two_plains_valid is taken with the range of all indices and the set of all seeds: both
  side predicates are trivially true.
- All limits of TwoIndices.lean hold here.
- The statements are for every matrix of the index type. That a model's weights are such a matrix is
  not stated in this folder (Spec.lean, "index").

Notes.
- Which plain part differs is not in the statement. By TwoIndices.lean it is the first answer of the
  third round.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.TwoViews
import Johnson.WholeKey.Foes

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
open _root_.Iop (Rho Tr Strat InteractiveOracleProof DView Honest Plains ExtSpec)
open _root_.Run (ckP)
open PV.EntryFive (dsF xsF)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-! ## A negative test: fixed messages -/

/-- The plain parts of a prover whose strategy is the same at all private inputs, instances and
coins depend on nothing but the verifier message. -/
theorem plains_const {Y Wt : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} (H : Honest Q Wt)
    (hs : ∀ w y c w' y' c', H.strat w y c = H.strat w' y' c') (w w' : Wt) (y y' : Y)
    (c c' : H.Coin) (ρ : Rho Q.shape) :
    ((H.strat w y c).run ρ).1.plains = ((H.strat w' y' c').run ρ).1.plains := by
  rw [hs w y c w' y' c']

/-- The plain parts of a prover that sends the fixed messages depend on nothing but the verifier
message. -/
theorem plains_fixed {Y Wt : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} (H : Honest Q Wt)
    (hs : ∀ w y c, H.strat w y c = Strat.dflt Q.shape ()) (w w' : Wt) (y y' : Y) (c c' : H.Coin)
    (ρ : Rho Q.shape) :
    ((H.strat w y c).run ρ).1.plains = ((H.strat w' y' c').run ρ).1.plains := by
  rw [hs, hs]

/-- Hence the same for the link part of the placeholder provers (silent), for every protocol
structure. -/
theorem plains_silent {I X : Type} (L : _root_.Iop.HolographicProtocol I X)
    (w w' : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)) (y y' : L.Rec × L.Rec)
    (c c' : (OnBytes.WholeKey.silent L).Lk.Coin) (ρ : Rho L.link.shape) :
    (((OnBytes.WholeKey.silent L).Lk.strat w y c).run ρ).1.plains =
      (((OnBytes.WholeKey.silent L).Lk.strat w' y' c').run ρ).1.plains :=
  plains_fixed _ (fun _ _ _ => rfl) w w' y y' c c' ρ

/-! ## At homeR b Z -/

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **What the explicit link prover's strategy sends in the clear** (its plain parts), at a private
input, an instance, a coin and a verifier message. -/
def homePlains (w : HomeWt b Z) (x : RecFull × RecFull) (c : Kc) (ρ : Rho (HomeQ Z).shape) :
    Plains (HomeQ Z).shape :=
  (((explicitLinkProver b Z).strat w x c).run ρ).1.plains

/-- The plain parts are the first field of the disclosed view homeView; true by definition. -/
theorem homeView_plains (w : HomeWt b Z) (x : RecFull × RecFull) (c : Kc)
    (ρ : Rho (HomeQ Z).shape) : (homeView b Z w x c ρ).plains = homePlains b Z w x c ρ := rfl

/-- **The plain parts differ**, at every coin, when 1 is added at the cell (0, 0) of the index, at
the verifier message zeroAtHome Z c₀. -/
theorem two_plains (w : HomeWt b Z) (x x' : RecFull × RecFull) (c : Kc)
    (c₀ : (_root_.Run.PQ.s0 (ckP .two)).up.Chal) :
    homePlains b Z w x c (zeroAtHome Z c₀) ≠
      homePlains b Z (bumpWt b Z w) x' c (zeroAtHome Z c₀) := by
  intro h
  have hrs := rs_of_plains 97 (homeIn b Z w x) (homeIn b Z (bumpWt b Z w) x') (coinsFull c)
    (coinsFull c) (c₀, zeroRho dsFull) h
  have hrs' : (linkAll frP frS 97 (homeIn b Z w x) (coinsFull c) drawsZero).rs =
      (linkAll frP frS 97 (homeIn b Z (bumpWt b Z w) x') (coinsFull c) drawsZero).rs := hrs
  rw [linkAll_rs_at fr_cons, linkAll_rs_at fr_cons, List.append_assoc, List.append_assoc] at hrs'
  exact two_fronts b Z w x x' (coinsFull c)
    (List.append_inj hrs' ((length_lFront _ _).trans (length_lFront _ _).symm)).1

/-- The case of two_plains with the same instance on both sides. -/
theorem two_plains_same (w : HomeWt b Z) (x : RecFull × RecFull) (c : Kc)
    (c₀ : (_root_.Run.PQ.s0 (ckP .two)).up.Chal) :
    homePlains b Z w x c (zeroAtHome Z c₀) ≠
      homePlains b Z (bumpWt b Z w) x c (zeroAtHome Z c₀) := two_plains b Z w x x c c₀

/-- **The statement can fail**: with the placeholder link prover in place of explicitLinkProver b Z, the
statement of two_plains is false. -/
theorem silent_not_two_plains (w : HomeWt b Z) (x x' : RecFull × RecFull)
    (c₀ : (_root_.Run.PQ.s0 (ckP .two)).up.Chal) :
    ¬ ((((OnBytes.WholeKey.silent (homeR b Z).protocol).Lk.strat w x ()).run (zeroAtHome Z c₀)).1.plains ≠
      (((OnBytes.WholeKey.silent (homeR b Z).protocol).Lk.strat (bumpWt b Z w) x' ()).run
        (zeroAtHome Z c₀)).1.plains) :=
  fun h => h (plains_silent (homeR b Z).protocol w (bumpWt b Z w) x x' () () (zeroAtHome Z c₀))

/-- The form with two valid private inputs: weaker than two_plains in every binder but the coin's.
-/
theorem two_plains_valid : ∃ (w w' : HomeWt b Z) (x x' : RecFull × RecFull),
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x ∧
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w' x' ∧
    w'.1 ≠ w.1 ∧ w'.2 = w.2 ∧
    ∃ ρ : Rho (HomeQ Z).shape,
      ρ ∉ (explicitLinkProver b Z).withheld w x ∧ ρ ∉ (explicitLinkProver b Z).withheld w' x' ∧
      ∀ c : Kc, homePlains b Z w x c ρ ≠ homePlains b Z w' x' c ρ := by
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
    fun c => two_plains b Z w x x' c c₀⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.plains_const
#print axioms OnBytes.LinkSim.AtHome.plains_fixed
#print axioms OnBytes.LinkSim.AtHome.plains_silent
#print axioms OnBytes.LinkSim.AtHome.homeView_plains
#print axioms OnBytes.LinkSim.AtHome.two_plains
#print axioms OnBytes.LinkSim.AtHome.two_plains_same
#print axioms OnBytes.LinkSim.AtHome.silent_not_two_plains
#print axioms OnBytes.LinkSim.AtHome.two_plains_valid
