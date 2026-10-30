-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/OpeningRoomK4.lean: THE SHARED "SENDING" (the kind K1) AGAINST THE ENTRIES THAT THE
FEED-FORWARD LAYERS' OWN ROUNDS (the kind K4) READ OF A MASK ROW: THEY LIE WITHIN THE MASK ROWS'
ENTRIES OF THE OPENING's MESSAGE NUMBER 0. For the authors of K4's lots, whose laws take one number
L twice: the sender's sentence holds below L, and "the lookup's entries and K4's takes are at most
L + 1". PUBLIC DATA ALONE: plans' counts and a code's length: which entries are read, never what
stands in them. Two theorems; NO DEFINITION. A TRIAL THAT COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

IT STANDS OVER FILES OF ANOTHER HOUSE: Johnson/Desc/ProofFile/Honest/K4/Lot/PubG.lean (k4PubG) and
Johnson/Road/K4/C/PublicLight.lean (light_head).

Under h (the library's head: A HYPOTHESIS) and O:
  - maskReads_room: at a group g below 12, where k4PubG Zp g returns Qp: the number of the lookup's
    entries plus k4Takes at Qp is at most 8192. Two calls: the other house's light_head (that sum is
    at most the plan's number of slots) and the library's slots_paid
    (Johnson/Road/K4/K4PinsSlots.lean: that number is at most 8192).
  - maskReads_below: at g := 0: that sum is at most L + 1, with for L the very term of
    msgTxt_mask_slot's and mask_in's premise at our message number 0 (mask rows times the mask
    code's length; 8192 by openingLens_head, AtFullSide/K1/OpeningLengthsW.lean): the text of hL in
    the other house's k4Mask_covers and k4MaskTie_of_lot. In the first Qp is bound as here, by
    k4PubG; in the second by k4PubOf Zp x.2 = some Qp: hL's text is one, Qp's origin is not.

Kin. By its own pages the other house has the like under its LaidK4 and another reading of Qp:
takes_room_head (Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskBelowHead.lean) and slotsSharp_head
(…/Law/W/MaskEllHead.lean: the plan's slots and one more are at most 8192: sharper by one than
slots_paid): NOT IMPORTED: with each come more than eighty files of that house that are no part of
the library (88 and 81, itself counted; a program's walk over its pack of reading copies).

Limits. THE FULL SIZE ALONE. CONDITIONAL on h, O, hg and hP, at the format's second hash function. THERE IS
SLACK: the bound is 8192 where L + 1 is 8193; what the sum is at any group is not said. The second
speaks of GROUP 0 ALONE: the other eleven groups' mask rows are another sender's. That k4PubG
returns at any group is not said here. Nothing on a run, or on what any coin is. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.OpeningLengthsW
import Johnson.Desc.ProofFile.Honest.K4.Lot.PubG
import Johnson.Road.K4.C.PublicLight
import Johnson.Road.K4.K4PinsSlots
import Johnson.Road.K4.K4HeadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K1
open ProofFile.Honest.K4.Lot (k4PubG)
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Road.K4 (written_of_head slots_paid)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- h, O, hg AND hP ARE PREMISES. The lookup's entries and K4's takes at group g are together at
most 8192. -/
theorem maskReads_room (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) :
    OnBytes.Model.Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ 8192 := by
  unfold k4PubG at hP
  obtain ⟨hp, hG, hP'⟩ := Option.bind_eq_some_iff.1 hP
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hP'
  have l := (OnBytes.Road.K4.C.light_head h hg hG).2.2.2.2.2.1
  have s := slots_paid h.scope h.reads O (written_of_head h.toAtMg) g hg hp hG
  exact Nat.le_trans l s

/-- h, O AND hP ARE PREMISES. **WHAT K4 READS OF THE MASK ROW AT GROUP 0 LIES WITHIN THE MASK ROWS'
ENTRIES OF THE OPENING's MESSAGE NUMBER 0**, in the form of the premise hL, at L := that number. -/
theorem maskReads_below (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {Qp : K4Pub} (hP : k4PubG Zp 0 = some Qp) :
    OnBytes.Model.Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤
      (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).maskRows *
        ((K1.firstPar Bs.G₀.first (K1.gpOf Zp)).codes.mask.getD
          (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).maskCode default).ell + 1 := by
  rw [(openingLens_head h O).1]
  exact Nat.le_succ_of_le (maskReads_room h O (by omega) hP)

end AtFullSide.K1

#print axioms AtFullSide.K1.maskReads_room
#print axioms AtFullSide.K1.maskReads_below
