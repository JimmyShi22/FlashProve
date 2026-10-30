-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/TwoIndices.lean: the link prover's first answer in the clear does not
ignore the index: adding 1 to one cell changes it by exactly 1, at one verifier message, at every
coin.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves. For every private input w of the link, let bumpWt b Z w keep the randomness
of both tables and the seeds, and add 1 at the cell (0, 0) of the index. Take one verifier message:
the one whose hash blocks and proof-of-work bits are all 0 (zeroRho dsFull,
Johnson/LinkSim/AtText/ZeroDraws.lean). There, whatever the two instances are, the following hold.
The first of the two answers that the prover's algorithm sends in the clear in its third round
changes by exactly 1 (answer_home). So the two runs' fronts differ (two_fronts). And what the two
runs disclose differs (two_shown): shownOf of linkAll, the prover's side of home_upTo's statement
(Johnson/LinkSim/AtHome/RoadCloses.lean). These three hold for every value of the coins, C : LCoins,
not only for the images of the finite type Kc.

Why that verifier message. There the point at which the tables' rows are folded, and the point of
the link proof's own first OOD sample (lSeed, on the two folded rows), are both 0. At that corner
("all false") the fold takes row 0 and the sample takes entry 0, which is where the cell (0, 0) is
written. eqk_fold_home and eqk_seed_home prove that both weights there are 1; they are the two
factors that make the change exactly 1.

How it fits. TwoViews.lean and TwoPlains.lean call two_fronts and bumpWt, and carry the change over
from the algorithm to the prover's strategy as the protocol defines it. answer_home and two_indices
have no user in this folder; two_shown is used by two_indices alone.

Names (namespace OnBytes.LinkSim.AtHome).
  fr_cutPos, fr_rowsPos, fr_Tl, fr_Cl   concrete facts on public numbers.
  entryOf_first, idxJ_first, putAt_ne_pad   where the first coefficient of the message's part is
                    placed.
  homeIn_bump       the first table's rows' polynomials change in one coefficient.
  eqk_seed_home     at that verifier message, the weight that the link proof's own first OOD
                    sample's point gives to that coefficient's entry is 1.
  eqk_fold_home     at that verifier message, the weight that the fold's point gives to row 0 is 1.
  answer_home       the equation: the first answer changes by 1.
  two_fronts, two_shown   the fronts differ; what is disclosed differs.
  two_indices       the form with two valid private inputs: there are two, with their instances,
                    the same randomness and seeds, different indices, and a verifier message, such
                    that at every coin of the finite type what is disclosed differs. It is weaker
                    than two_shown in every binder. For the statement that a message changes, cite
                    answer_home or two_fronts.

Limits, the weightiest first.
- By their statements, two_shown and two_indices do not say that a message changes. They say that
  shownOf differs. Besides the rounds, shownOf holds the groups of columns, whose first are the
  stored columns at the positions read (lStored, Johnson/Prover/Link/LinkAll.lean). These are
  symbols of the two encoded indices, which are not messages of the link's prover. A prover of fixed
  messages over the same two encodings could satisfy both statements.
- Only a change through the first table is proved, through one item. That the messages depend on the
  second table's rows and on both tables' randomness is by inspection of the algorithm alone, not
  proved.
- Its statements hold coin by coin, at one verifier message and for one changed cell, and say
  nothing on distributions over the coins (see Johnson/LinkSim/AtHome/TwoPlains.lean's limits). That
  other verifier messages do the same is not said.
- It speaks of the prover's algorithm (linkAll, Johnson/Prover/Link/LinkAll.lean), at explicitLinkProver b Z's
  own data (homeIn b Z), its own coins (coinsFull, Johnson/Prover/Link/LinkCoin.lean) and the
  challenges of a verifier message: the prover's side of home_upTo's statement. The verifier message
  is the part after the trivial first round (in home_upTo: ρ.2).
- By inspection, not proved: of a cell only the first coordinate is written (cellEntry,
  Johnson/Flat/CodingCells.lean). So two indices that differ only in other coordinates give the same
  message.
- The statements are for every matrix of the index type. That a model's weights are such a matrix is
  not stated in this folder (Spec.lean, "index"). That either index lies in the range of the goals'
  relation is not said.

Notes.
- Argued on paper, not proved: over uniform coins each answer by itself has the same distribution at
  all indices; nothing here contradicts that.
- What says by statement that a message changes: answer_home (the first answer changes by exactly 1)
  and two_fronts, for the algorithm; for the strategy's plain parts, two_plains
  (Johnson/LinkSim/AtHome/TwoPlains.lean). Here two_shown and two_indices are proved through
  two_fronts.
- That the rounds of the strategy's run are this algorithm's rounds is proved in other files
  (rv_run, Johnson/Prover/Link/LinkFrame.lean; rs_full, Johnson/Prover/Link/LinkJoinA.lean).
- "Valid" is validLk (Johnson/LinkSim/Spec.lean) at the range of all indices and the set of all
  seeds.
- fr_Tl and fr_Cl are proved under a raised limit of elaboration (see Johnson/LinkSim/Spec.lean,
  "maxRecDepth").

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.HomeNotIdle
import Johnson.LinkSim.AtText.OneCell
import Johnson.LinkSim.AtText.ZeroDrawsAtFull

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
open _root_.Iop (Rho)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (uL drawnSL)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-! ## Public numbers, and an entry -/

theorem fr_cutPos : 0 < 402653181 := by decide

theorem fr_rowsPos : 0 < numsRef.rows := by decide

set_option maxRecDepth 100000 in
theorem fr_Tl : 0 < frS.P.T.l := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_Cl : frS.P.C.l ≠ 1 := by decide +kernel

theorem entryOf_first (S : Sz) (hl : 0 < S.P.T.l) :
    S.entryOf ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ = 0 := by
  unfold Sz.entryOf
  rw [if_neg (Nat.lt_irrefl _)]
  exact Nat.sub_self _

theorem idxJ_first (S : Sz) (hl : 0 < S.P.T.l) :
    S.idxJ (S.putAt ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩) = 0 := by
  show S.entryOf ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ / S.P.C.l +
    2 ^ S.P.aR * (S.entryOf ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ % S.P.C.l) = 0
  rw [entryOf_first S hl, Nat.zero_div, Nat.zero_mod, Nat.mul_zero]

theorem putAt_ne_pad (S : Sz) (hl : 0 < S.P.T.l) (hc : S.P.C.l ≠ 1) :
    S.putAt ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ ≠ S.padJ := by
  intro h
  have e : S.entryOf ⟨S.P.T.r, Nat.lt_add_of_pos_right hl⟩ % S.P.C.l = S.P.C.l - 1 :=
    congrArg Fin.val (congrArg Prod.snd (Sum.inl.inj h))
  rw [entryOf_first S hl, Nat.zero_mod] at e
  have := S.hl
  omega

/-! ## The two private inputs -/

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- The same randomness and seeds; 1 added at the index's cell (0, 0). -/
def bumpWt (w : HomeWt b Z) : HomeWt b Z := (bumpCell frS frZ 402653181 numsRef w.1, w.2)

/-- The first table's rows' polynomials change in one coefficient. -/
theorem homeIn_bump (w : HomeWt b Z) (x x' : RecFull × RecFull) :
    (homeIn b Z (bumpWt b Z w) x').M₀ = (homeIn b Z w x).M₀ +
      oneCoeff (fun _ => false) ⟨frS.P.T.r, Nat.lt_add_of_pos_right fr_Tl⟩ 1 :=
  rowPolys_bump fr_cutPos fr_rowsPos fr_Tl w.1 w.2.1.1.1 (tailWords frS w.2.1.1.2)

theorem eqk_seed_home :
    Alg.eqk (lSeed frS drawsZero).1 (fun t =>
      (frS.idxJ (frS.putAt ⟨frS.P.T.r, Nat.lt_add_of_pos_right fr_Tl⟩)).testBit t.val) = 1 := by
  rw [fr_lSeed_zero, idxJ_first frS fr_Tl]
  have e : (fun t : Fin (frS.P.aR + frS.P.aP) => (0 : ℕ).testBit t.val) = fun _ => false :=
    funext fun t => Nat.zero_testBit _
  rw [e]
  exact eqk_zero _

theorem eqk_fold_home : Alg.eqk (lGam frS drawsZero) (fun _ => false) = 1 := by
  rw [fr_lGam_zero]
  exact eqk_zero _

/-- **The equation: the first answer changes by 1.** -/
theorem answer_home (w : HomeWt b Z) (x x' : RecFull × RecFull) (C : LCoins) :
    smAt frS 97 (lSeed frS drawsZero)
        (mu0 frS 97 (lMem frS (homeIn b Z (bumpWt b Z w) x') C drawsZero)) false =
      smAt frS 97 (lSeed frS drawsZero)
        (mu0 frS 97 (lMem frS (homeIn b Z w x) C drawsZero)) false + 1 := by
  rw [answer_moves (fun _ => false) ⟨frS.P.T.r, Nat.lt_add_of_pos_right fr_Tl⟩ (Nat.le_refl _) 1
    (homeIn_bump b Z w x x'), mat_putAt _ _ (putAt_ne_pad frS fr_Tl fr_Cl), eqk_seed_home,
    eqk_fold_home, one_mul, one_mul]

/-- The two fronts differ. -/
theorem two_fronts (w : HomeWt b Z) (x x' : RecFull × RecFull) (C : LCoins) :
    lFront frS 97 (homeIn b Z w x) C drawsZero ≠
      lFront frS 97 (homeIn b Z (bumpWt b Z w) x') C drawsZero :=
  front_moves (fun _ => false) ⟨frS.P.T.r, Nat.lt_add_of_pos_right fr_Tl⟩ (Nat.le_refl _) 1
    (homeIn_bump b Z w x x') (putAt_ne_pad frS fr_Tl fr_Cl)
    (by rw [eqk_seed_home]; exact one_ne_zero) (by rw [eqk_fold_home]; exact one_ne_zero)
    one_ne_zero

/-- **What is disclosed differs**, for every family of coin values. -/
theorem two_shown (w : HomeWt b Z) (x x' : RecFull × RecFull) (C : LCoins) :
    shownOf (linkAll frP frS 97 (homeIn b Z w x) C drawsZero) ≠
      shownOf (linkAll frP frS 97 (homeIn b Z (bumpWt b Z w) x') C drawsZero) :=
  shown_moves fr_cons (two_fronts b Z w x x' C)

/-- **The form with two valid private inputs.** Weaker than two_shown in every binder. By its
statement it does not say that a message changes: for that, cite answer_home or two_fronts. -/
theorem two_indices : ∃ (w w' : HomeWt b Z) (x x' : RecFull × RecFull),
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x ∧
    validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w' x' ∧
    w'.1 ≠ w.1 ∧ w'.2 = w.2 ∧
    ∃ ρ : Rho (uL (ckP .two) dsFull), ∀ c : Kc,
      shownOf (linkAll frP frS 97 (homeIn b Z w x) (coinsFull c)
          (drawsOf (drawnSL (ckP .two) dsFull ρ))) ≠
        shownOf (linkAll frP frS 97 (homeIn b Z w' x') (coinsFull c)
          (drawsOf (drawnSL (ckP .two) dsFull ρ))) := by
  obtain ⟨w⟩ := home_wt_nonempty b Z
  exact ⟨w, bumpWt b Z w, _, _, ⟨trivial, trivial, trivial, rfl⟩, ⟨trivial, trivial, trivial, rfl⟩,
    bumpCell_ne frS frZ 402653181 numsRef fr_rowsPos w.1, rfl, zeroRho dsFull,
    fun c => two_shown b Z w _ _ (coinsFull c)⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.fr_Tl
#print axioms OnBytes.LinkSim.AtHome.fr_Cl
#print axioms OnBytes.LinkSim.AtHome.entryOf_first
#print axioms OnBytes.LinkSim.AtHome.idxJ_first
#print axioms OnBytes.LinkSim.AtHome.putAt_ne_pad
#print axioms OnBytes.LinkSim.AtHome.homeIn_bump
#print axioms OnBytes.LinkSim.AtHome.eqk_seed_home
#print axioms OnBytes.LinkSim.AtHome.eqk_fold_home
#print axioms OnBytes.LinkSim.AtHome.answer_home
#print axioms OnBytes.LinkSim.AtHome.two_fronts
#print axioms OnBytes.LinkSim.AtHome.two_shown
#print axioms OnBytes.LinkSim.AtHome.two_indices
