-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/FrontStep.lean: under the premises AtFront, the front of the link prover's
algorithm gives the same rounds at the honest run and at the run at the data 0 with shifted coins.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The front is the part of linkAll before the first stage (its rounds are
walked through in Defs.lean's head). Compare the run at the data X and coins C with the run at the
data 0 (zeroIn X) and coins C'. AtFront collects what is assumed of C and C':
  - the pads, the tails of the R rows in which each folded row is laid out, the first fold's
    coefficients and the tail of the row beside the two folded rows differ by shPad, shTN, shW0
    and shPsi (Johnson/LinkSim/AtText/ShiftDefs.lean);
  - the pad has an entry of its own in the row's message (PadRoom);
  - the first tree is opened at no more positions than its rows' tails are long.
Under AtFront:
  lFront_same    the five front rounds are the same at both runs.
  lT_same        the verifier's state after the batching is the same.
  lPS_add        the first prover state at (X, C) is the first state at (zeroIn X, C') plus d0.
  lCol_same      the first tree has equal columns at the positions at which it is opened.
Each statement is an equation between the two runs. The proofs use smAt_shift, lMem_split,
lMem_zero, firstPS_add, packedN_add, symG_tailAt and firstColW_congr.

How it fits. LinkShift.lean proves Spec.frontShift from these lemmas, with C' = C + shC (atFront_of
gives AtFront there).

The other names.
  lMem_other     the folded rows' messages at (zeroIn X, C') are their pads alone.
  lMem_diff      the folded rows' messages at (X, C) are those at (zeroIn X, C') plus dMem.
  phi_diff       the row beside the folded rows at C is the one at C' plus dPhi.

Limits.
  - These lemmas are about the front alone.
Notes.
  - Nothing here says how AtFront's premises come about: LinkShift.lean derives them from Sizes
    (atFront_of).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Step

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open Johnson.Prover.Link

/-- What is assumed of the two runs' coins in the front. -/
structure AtFront (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C C' : LCoins) (D : ℕ → Fmt.Drawn) :
    Prop where
  pad : ∀ a, C'.pad a = C.pad a + shPad S t X D a
  tN : ∀ a i, C'.tN a i = C.tN a i + shTN P S t X D a i
  W : C'.body.W (sg0 P) 0 = C.body.W (sg0 P) 0 + shW0 P S t X X C D (sg0 P)
  psi : C'.ψN = C.ψN + shPsi P S t X X C D
  room : PadRoom S
  qC : (q0 P D).length ≤ S.P.C.r
  qZ : (q0 P D).length ≤ S.P.Z.r

variable {P : P15} {S : Sz} {t : ℕ} {X : LIn S} {C C' : LCoins} {D : ℕ → Fmt.Drawn}

/-- At the data 0, the folded rows' messages hold their pads alone. -/
theorem lMem_other (h : AtFront P S t X C C' D) :
    lMem S (zeroIn X) C' D =
      (fun a => Pi.single S.padJ (C.pad a) : Bool → S.MJ → GE) +
        (fun a => Pi.single S.padJ (shPad S t X D a) : Bool → S.MJ → GE) := by
  rw [lMem_zero S X C' D h.room]
  funext a
  show (Pi.single S.padJ (C'.pad a) : S.MJ → GE) =
    Pi.single S.padJ (C.pad a) + Pi.single S.padJ (shPad S t X D a)
  rw [h.pad a, Pi.single_add]

/-- The folded rows' messages at the data X are those at the data 0 plus dMem. -/
theorem lMem_diff (h : AtFront P S t X C C' D) :
    lMem S X C D = lMem S (zeroIn X) C' D + dMem S t X D := by
  rw [lMem_other h, lMem_split S X C D h.room]
  unfold dMem fData
  abel

/-- The five front rounds are the same at both runs. -/
theorem lFront_same (h : AtFront P S t X C C' D) :
    lFront S t X C D = lFront S t (zeroIn X) C' D := by
  have e : ∀ a, smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) a =
      smAt S t (lSeed S D) (mu0 S t (lMem S (zeroIn X) C' D)) a := by
    intro a
    rw [lMem_other h, lMem_split S X C D h.room, add_comm]
    exact smAt_shift S t (lSeed S D) _ _ a
  unfold lFront
  rw [e false, e true]

/-- The verifier's state after the batching is the same at both runs. -/
theorem lT_same (h : AtFront P S t X C C' D) : lT P S t X C D = lT P S t (zeroIn X) C' D := by
  unfold lT
  rw [lFront_same h]
  rfl

/-- The packing of the first fold's coefficients at C is the one at C' plus dPhi. -/
theorem phi_diff (h : AtFront P S t X C C' D) :
    packedN (sg0 P) (C.body.W (sg0 P) 0) 0 =
      packedN (sg0 P) (C'.body.W (sg0 P) 0) 0 + dPhi P S t X X C D := by
  funext i
  show _ = packedN (sg0 P) (C'.body.W (sg0 P) 0) 0 i +
    -packedN (sg0 P) (shW0 P S t X X C D (sg0 P)) 0 i
  rw [h.W, packedN_add]
  exact (add_neg_cancel_right _ _).symm

/-- The first prover state at the data X is the one at the data 0 plus d0. -/
theorem lPS_add (h : AtFront P S t X C C' D) :
    lPS P S X C D = addPS (lPS P S (zeroIn X) C' D) (d0 P S t X X C D) := by
  unfold lPS d0
  rw [← firstPS_add, ← lMem_diff h, ← phi_diff h]
  have e1 : C'.tN + -shTN P S t X D = C.tN := by
    funext a i
    show C'.tN a i + -shTN P S t X D a i = C.tN a i
    rw [h.tN a i]
    exact add_neg_cancel_right _ _
  have e2 : C'.ψN + -shPsi P S t X X C D = C.ψN := by
    rw [h.psi]
    exact add_neg_cancel_right _ _
  rw [e1, e2]

/-- The first tree has equal columns at the two runs, at the positions at which it is opened. -/
theorem lCol_same (h : AtFront P S t X C C' D) {x : ℕ} (hx : x ∈ Fmt.listOf (q0 P D)) :
    lCol P S X C D x = lCol P S (zeroIn X) C' D x := by
  have hxQ : x ∈ q0 P D := (Fmt.listOf_mem _ _).mp hx
  unfold lCol
  refine firstColW_congr S _ _ _ _ _ _ _ _ x (fun a i hi => ?_) ?_
  · have e : membN S (lMem S X C D) a i =
        membN S (lMem S (zeroIn X) C' D) a i + membN S (dMem S t X D) a i := by
      rw [lMem_diff h]
      exact funext fun k => membN_add S _ _ a i k
    have e2 : C'.tN a i = C.tN a i + tailAt S.P.C id (q0 P D) (membN S (dMem S t X D) a i) := by
      rw [h.tN a i]
      unfold shTN
      rw [if_pos hi]
    rw [e, e2]
    exact symG_tailAt S.P.C (q0 P D) id h.qC _ _ _ hxQ
  · rw [phi_diff h, h.psi]
    exact symG_tailAt S.P.Z (q0 P D) (· % 2 ^ S.P.Z.a) h.qZ _ _ _ hxQ

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.lFront_same
#print axioms OnBytes.LinkSim.AtText.lT_same
#print axioms OnBytes.LinkSim.AtText.lPS_add
#print axioms OnBytes.LinkSim.AtText.lCol_same
