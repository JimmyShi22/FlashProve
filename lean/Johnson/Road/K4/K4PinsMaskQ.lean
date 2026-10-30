-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsMaskQ.lean: TWO READINGS OF A SEGMENT's OWN MASK ROW ARE ONE. The one:
`PinPlan.mask` (Johnson/Road/K4/K4PinsRead.lean: the lookup's caller's `valAt` at the address
"mask j", over the tuple out of the pinned part): K4's value reads it. The other: the field mask of
`dataQ` (Johnson/Desc/Sound/FormsQ.lean: the batch's `dataOf` over the one accessor `tabQ`): the
table's items on forms read it. A Lean structure of conditions and one theorem, by unfolding. No
draw, no count.

  `MaskOne A own a`: THE CONDITIONS. ON THE PLAN: the caller's link has a first message with mask
    rows; it is a member of the caller's list. ON THE VERIFIER's STATE's PART a: the frame's mask
    oracle is a message number o; the book seats o, among own, AT THE SEAT OF THAT MEMBER; the
    statement gives o's mask table no row bits (one mask row). "There is" on both sides: no side may
    be silent.
  **`mask_dataQ`**: under `MaskOne`, at every entry j inside the member's mask row:
    `A.mask t j = (dataQ own a t.1).mask j`, at every tuple t.

OBJECT: none of its own. USER: none yet; meant: whoever ties the table's item formsT m 3 "own" to
the road's sentence on the forms. LETTERS, filled by nobody: every field of `PinPlan`, own, a.

Limits. K04_law IS NOT PROVED BY THIS. `MaskOne` IS A PREMISE; IT HAS RUN NOWHERE. ITS SECOND HALF
SPEAKS OF THE VERIFIER's STATE (frame, book, statement): it is for the table's promise (the book is
the plan's; the frame is the description's) to give: that road is not typed here. Beyond the
member's mask row both readings are whatever the table at that seat holds there, or 0: not compared.
THE ARRAYS' CELLS ARE NOT COMPARED HERE: `dataOf`'s cell is a sum over the layout's blocks and over
all entries of a table ("Meant: one entry, or none. Not proved here":
Johnson/Desc/First/Batch/Law/AsRow.lean), the caller's a read at one place (`laidPlace`): that the
two agree: Johnson/Road/K4/K4PinsCellQ.lean, over the law on blocks of K4PinsBlocks.lean. `MaskOne`
IS A STRUCTURE WITH DATA (it lives in Type, not in Prop): whoever pays it BUILDS the two numbers.

-/
import Johnson.Road.K4.K4PinsRead
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls valAt finOf_some messagesAt
  keptAt)
open VerifiableInference.Desc.Sound (dataQ tabQ)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.K9L (dataOf maskOracle)

variable {Cells : Type} (A : PinPlan Cells)

/-- **The conditions**: on the plan, and on the verifier's state's part. -/
structure MaskOne (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part) where
  /-- the number, among the link's messages, of the first with mask rows -/
  mI : ℕ
  first : ((messagesAt A.D A.link).findIdx? fun x => x.shape.maskRows != 0) = some mI
  /-- it is a member of the caller's list, behind the kept ones -/
  member : (keptAt A.D A.link).length + mI < (sigListCalls A.D A.rad A.link).length
  rows : 0 < ((sigListCalls A.D A.rad A.link).get ⟨_, member⟩).1.maskRows
  /-- the verifier's state's side -/
  o : ℕ
  oracle : maskOracle a.L.check.frame = some o
  seated : seatAt own a.d.book o = some (A.seatT ⟨_, member⟩)
  oneRow : a.d.st.rowBits o .mask = 0

/-- **The two readings of the mask row are one**, under `MaskOne`, inside the member's mask row. -/
theorem mask_dataQ (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part)
    (H : MaskOne A own a) (t : PinM Cells) (j : ℕ)
    (hj : j < (pMask A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨_, H.member⟩).1).ell) :
    A.mask t j = (dataQ own a t.1).mask j := by
  have L1 : A.mask t j = t.1 (A.seatT ⟨_, H.member⟩) true 0 j := by
    unfold PinPlan.mask valAt seatCalls
    rw [H.first]
    show (VerifiableInference.Desc.First.Look.readAt A.D.codes _ (A.tuple t)
      ⟨(keptAt A.D A.link).length + H.mI, true, 0, j⟩).getD 0 = _
    unfold VerifiableInference.Desc.First.Look.readAt
    rw [dif_pos H.member, if_pos rfl, finOf_some H.rows, finOf_some hj]
    rfl
  have R1 : (dataQ own a t.1).mask j = t.1 (A.seatT ⟨_, H.member⟩) true 0 j := by
    show (match maskOracle a.L.check.frame with
      | some o => tabQ own a.d.st a.d.book t.1 o .mask j
      | none => 0) = _
    rw [H.oracle]
    show tabQ own a.d.st a.d.book t.1 H.o .mask j = _
    unfold tabQ
    rw [H.seated, H.oneRow, Nat.pow_zero, Nat.mod_one, Nat.div_one]
    rfl
  rw [L1, R1]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mask_dataQ
