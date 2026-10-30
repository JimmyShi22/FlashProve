-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/SenderOwn.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: an entry of a message's mask rows, by the format's own number, written in the
program's elements, IS the part's own coin of the extension field number maskStart + that number, in
the frame's list of these coins (coinsE, Johnson/Desc/ProofFile/Honest/Sum.lean): for a message
whose table does not ride. A definition, statements and proofs, over
Johnson/Desc/ProofFile/Honest/K1/MaskLaw.lean.

  coinsE_getD: below the count the frame's list has the coin itself, written in the program's
    elements.
  maskRowE P ride data k cs ν: the entry with the format's number ν = c * m + rho of message number
    k's mask rows (m rows), as rowsR lays it of the part's own coins cs, in the program's elements.
    THE MASK DOES NOT READ data.
  sender_own: THE STATEMENT: for k < P.sent.size and ride k = none: at every cs, at every ν below
    the mask rows' entries: maskRowE P ride data k cs ν = (coinsE cs).getD (maskStart P ride k + ν)
    zeroE.
  sender_in: there maskStart P ride k + ν lies inside the part's count (mask_in under another name's
    form).
  sender_own_later, sender_in_later: the two at a segment's later moment (K1.parLater,
    Johnson/Desc/K1/Places.lean), where no table rides.

Limits. What is WRITTEN where: no sentence on what a mask row or a coin is for. AT MESSAGES WHERE NO
TABLE RIDES ALONE: of a riding message only its count enters maskStart; nothing is said on a riding
table's entries. sender_own's right side reads the list with zeroE behind it: it names a coin only
with sender_in beside it: THE TWO ARE TO BE SPENT TOGETHER. Nothing is said to be one-to-one or
onto. THE LAWS HOLD FOR ALL ENTRIES OF THE MASK ROWS, a pad's own places among them. That a ledger's
slot number in the verifier's statement is the format's number is not said. Nothing holds maskStart
against the book's maker's count. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.K1.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- Below the count the frame's list of the coins of the extension field has the coin itself. -/
theorem coinsE_getD {d : Due} (cs : Cs d) (i : Nat) (h : i < d.e) :
    (coinsE cs).getD i zeroE = E.ofTriple (ofE (cs.e ⟨i, h⟩)) := by
  unfold coinsE
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

/-- **The entry with the format's number ν of message number k's mask rows**, as rowsR lays it of
the part's own coins, in the program's elements. The mask does not read data. -/
def maskRowE (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
    (k : Nat) (cs : Cs (dueR P ride)) (ν : Nat) : E :=
  E.ofTriple (ofE ((rowsR P ride data cs k).mask (ν % (shapeAt P k).maskRows)
    (ν / (shapeAt P k).maskRows)))

/-- These numbers lie inside the part's count. -/
theorem sender_in (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (hk : k < P.sent.size)
    (hr : ride k = none) : ∀ ν,
    ν < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell →
    maskStart P ride k + ν < (dueR P ride).e :=
  fun ν hν => mask_in P ride k ν hk hr hν

/-- **THE ENTRY NUMBER ν IS THE PART's OWN COIN NUMBER maskStart + ν**, at a message whose table
does not ride. -/
theorem sender_own (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (k : Nat) (hk : k < P.sent.size)
    (hr : ride k = none) : ∀ (cs : Cs (dueR P ride)) (ν : Nat),
    ν < (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell →
    maskRowE P ride data k cs ν = (coinsE cs).getD (maskStart P ride k + ν) zeroE := by
  intro cs ν hν
  rw [coinsE_getD cs _ (sender_in P ride k hk hr ν hν)]
  unfold maskRowE
  rw [mask_slot P ride data cs k ν hr hν, ce_eq _ cs _ (sender_in P ride k hk hr ν hν)]

/-- At a segment's later moment no table rides: the numbers lie inside the part's count. -/
theorem sender_in_later (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment k : Nat)
    (hk : k < (K1.parLater q gp link piece moment).sent.size) : ∀ ν,
    ν < (shapeAt (K1.parLater q gp link piece moment) k).maskRows *
      ((K1.parLater q gp link piece moment).codes.mask.getD
        (shapeAt (K1.parLater q gp link piece moment) k).maskCode default).ell →
    maskStart (K1.parLater q gp link piece moment) (fun _ => none) k + ν <
      (dueR (K1.parLater q gp link piece moment) fun _ => none).e :=
  sender_in (K1.parLater q gp link piece moment) (fun _ => none) k hk rfl

/-- **The same at a segment's later moment.** -/
theorem sender_own_later (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (k : Nat)
    (hk : k < (K1.parLater q gp link piece moment).sent.size) :
    ∀ (cs : Cs (dueR (K1.parLater q gp link piece moment) fun _ => none)) (ν : Nat),
    ν < (shapeAt (K1.parLater q gp link piece moment) k).maskRows *
      ((K1.parLater q gp link piece moment).codes.mask.getD
        (shapeAt (K1.parLater q gp link piece moment) k).maskCode default).ell →
    maskRowE (K1.parLater q gp link piece moment) (fun _ => none) data k cs ν =
      (coinsE cs).getD (maskStart (K1.parLater q gp link piece moment) (fun _ => none) k + ν)
        zeroE :=
  sender_own (K1.parLater q gp link piece moment) (fun _ => none) data k hk rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.coinsE_getD
#print axioms ProofFile.Honest.K1.maskRowE
#print axioms ProofFile.Honest.K1.sender_in
#print axioms ProofFile.Honest.K1.sender_own
#print axioms ProofFile.Honest.K1.sender_in_later
#print axioms ProofFile.Honest.K1.sender_own_later
