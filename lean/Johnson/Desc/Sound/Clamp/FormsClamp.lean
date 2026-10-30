-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Clamp/FormsClamp.lean: THE SENTENCES OF THE CLAIMS ON LINEAR FORMS AT THE
CLAMPED READER ARE THE COMPOSED MEANING's OWN: at `LinkJoin.rdC cs arr ms w`
(Johnson/Desc/First/Link/Law/ClampPin.lean: each member's typed message read back as a table, 0
outside its ranges) and at `seatTab cs arr ms w` (at which `mgAll`, Johnson/Desc/Sound/MgAll.lean,
states them) `formsQ`, `formsQA`, `formsTQ`, `totalQ`, `totalBQ` have one truth value, UNDER ONE
NAMED PREMISE ON THE STATE AND THE LIST OF MEMBERS (`InsideAt`; at `formsQA` a second,
`InsideAhead`; at `formsTQ` two more, on the stated functions). Definitions and theorems.
Why. A law that needs "two pinned witnesses have one table" can be met at the clamped reader alone
(a pin fixes nothing outside a member's ranges). With these lemmas such a law's sentences are the
composed meaning's.
  `InsideAt cs ms own a`: every entry of a table that the open segment's data read lies inside the
    ranges of the member that sits at its seat: (main) at every index J that a block of an array
    of the layout holds; (mask) at every slot below the ledger's number of slots, or below the
    size of its list of coefficients.
  `InsideAhead cs ms sent own a`: the like for the arrays that are read ahead of their sending.
  `agreeQ_clamp`, `agreeQA_clamp`: under these the two readers agree (`AgreeQ`, `AgreeQA`,
    Johnson/Desc/Sound/FormsAgree.lean).
  `formsQ_clamp`, `formsQA_clamp`, `formsTQ_clamp`, `totalQ_clamp`, `totalBQ_clamp`: each an "if
    and only if".
How: other files' lemmas: `dataQ_cell_agree`, `dataQ_mask_agree` (Clamp/CellAgree.lean),
`cellA_agree` (Clamp/AheadAgree.lean), `tabQ_clamp` (Clamp/TabClamp.lean), `LinkJoin.rdC_inside`.
Limits: `InsideAt` AND `InsideAhead` ARE SHOWN AT NO STATE HERE. What they want: the programs'
three tests on the codes, the request's shape and its layout (then a block's rectangle lies inside
the message's rows and length: Johnson/Goal/Meaning/LaidInside.lean); that the state's
layout, frame and statement are the plan's; that the member at the seat has the message's shape;
for the mask row, that the ledger's slots are at most the mask code's length less the pad. No
soundness is claimed.

-/
import Johnson.Desc.Sound.FormsAgree
import Johnson.Desc.Sound.Clamp.AheadAgree
import Johnson.Desc.Sound.Clamp.TabClamp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Readers segAt? atS aheadIn rowBitsOf placeBitsOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (rdC rdC_inside)

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (own : List (ℕ × ℕ))

/-- **Every entry that the open segment's data read lies inside the ranges of the member at its
seat.** -/
structure InsideAt (a : K9.Part) : Prop where
  main : ∀ born name A o b J x y, reqArray a.L.check.rows.layout born name = some A →
    a.L.check.frame.whereIs born A.message = some o → b ∈ A.blocks →
    J < 2 ^ (a.d.st.rowBits o .main + a.d.st.placeBits o .main) →
    (K9L.inBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) J : GQ) ≠ 0 →
    K9.seatAt own a.d.book o = some x →
    (ms.find? fun y => decide (seatOf y = x)) = some y →
    InMsg cs (y.1.l.get y.2).1 false (J % 2 ^ a.d.st.rowBits o .main)
      (J / 2 ^ a.d.st.rowBits o .main)
  mask : ∀ o j x y, K9L.maskOracle a.L.check.frame = some o →
    j < a.F.ns ∨ j < a.F.LS.size → K9.seatAt own a.d.book o = some x →
    (ms.find? fun y => decide (seatOf y = x)) = some y →
    InMsg cs (y.1.l.get y.2).1 true (j % 2 ^ a.d.st.rowBits o .mask)
      (j / 2 ^ a.d.st.rowBits o .mask)

theorem agreeQ_clamp (w : Wit Cells Tok MsgT) (a : K9.Part) (h : InsideAt cs ms own a) :
    AgreeQ own a (seatTab cs arr ms w) (rdC cs arr ms w) where
  cell := dataQ_cell_agree own a _ _ fun born name A o b J h1 h2 h3 h4 h5 =>
    tabQ_clamp cs arr ms own a.d.st a.d.book w o J .main fun x y hx hy =>
      h.main born name A o b J x y h1 h2 h3 h4 h5 hx hy
  mask := fun j hj => dataQ_mask_agree own a _ _ j fun o ho =>
    tabQ_clamp cs arr ms own a.d.st a.d.book w o j .mask fun x y hx hy =>
      h.mask o j x y ho hj hx hy

variable (Rd : Readers)

theorem formsQ_clamp (piece : ℕ) (run : String) (s : S) (w : Wit Cells Tok MsgT)
    (h : ∀ a, segAt? s = some a → InsideAt cs ms own a) :
    formsQ Rd own piece run s (rdC cs arr ms w) ↔ formsQ Rd own piece run s (seatTab cs arr ms w) :=
  ⟨formsQ_agree own Rd piece run s _ _ fun a ha =>
      (agreeQ_clamp cs arr ms own w a (h a ha)).symm own,
    formsQ_agree own Rd piece run s _ _ fun a ha => agreeQ_clamp cs arr ms own w a (h a ha)⟩

theorem formsTQ_clamp (St : Stated) (piece : ℕ) (run : String) (s : S) (w : Wit Cells Tok MsgT)
    (hC : ∀ D D' : K9L.Bound GQ, D'.cell = D.cell → (St.at1 s D').cell = (St.at1 s D).cell)
    (hM : ∀ D : K9L.Bound GQ, (St.at1 s D).mask = D.mask)
    (h : ∀ a, segAt? s = some a → InsideAt cs ms own a) :
    formsTQ Rd St own piece run s (rdC cs arr ms w) ↔
      formsTQ Rd St own piece run s (seatTab cs arr ms w) :=
  ⟨formsTQ_agree own Rd St piece run s _ _ hC hM fun a ha =>
      (agreeQ_clamp cs arr ms own w a (h a ha)).symm own,
    formsTQ_agree own Rd St piece run s _ _ hC hM fun a ha =>
      agreeQ_clamp cs arr ms own w a (h a ha)⟩

theorem totalQ_clamp (s : S) (w : Wit Cells Tok MsgT)
    (h : ∀ a, atS.get? s = some a → InsideAt cs ms own a) :
    totalQ own s (rdC cs arr ms w) ↔ totalQ own s (seatTab cs arr ms w) :=
  ⟨totalQ_agree own s _ _ fun a ha => (agreeQ_clamp cs arr ms own w a (h a ha)).symm own,
    totalQ_agree own s _ _ fun a ha => agreeQ_clamp cs arr ms own w a (h a ha)⟩

theorem totalBQ_clamp (after : S → Except String S) (s : S) (w : Wit Cells Tok MsgT)
    (h : ∀ s' a, after s = .ok s' → atS.get? s' = some a → InsideAt cs ms own a) :
    totalBQ after own s (rdC cs arr ms w) ↔ totalBQ after own s (seatTab cs arr ms w) :=
  ⟨totalBQ_agree own after s _ _ fun s' a h1 ha =>
      (agreeQ_clamp cs arr ms own w a (h s' a h1 ha)).symm own,
    totalBQ_agree own after s _ _ fun s' a h1 ha => agreeQ_clamp cs arr ms own w a (h s' a h1 ha)⟩

variable (sent : ℕ → List (ℕ × ℕ))

/-- The like for the arrays that are read ahead of their sending. -/
def InsideAhead (a : K9.Part) : Prop :=
  ∀ b0 h b J y, aheadIn sent own a b0 = some h → b ∈ h.A.blocks →
    J < 2 ^ (rowBitsOf h.shape .main + placeBitsOf a.d.st.codes h.shape .main) →
    (K9L.inBlock b (rowBitsOf h.shape .main) (placeBitsOf a.d.st.codes h.shape .main) J : GQ) ≠ 0 →
    (ms.find? fun y => decide (seatOf y = h.seat)) = some y →
    InMsg cs (y.1.l.get y.2).1 false (J % 2 ^ rowBitsOf h.shape .main)
      (J / 2 ^ rowBitsOf h.shape .main)

theorem agreeQA_clamp (w : Wit Cells Tok MsgT) (a : K9.Part) (h : InsideAt cs ms own a)
    (hA : InsideAhead cs ms own sent a) :
    AgreeQA sent own a (seatTab cs arr ms w) (rdC cs arr ms w) where
  toAgreeQ := agreeQ_clamp cs arr ms own w a h
  ahead := fun b0 x hx => cellA_agree a.d.st.codes x _ _ fun b J hb hJ hin => by
    cases e : ms.find? fun y => decide (seatOf y = x.seat) with
    | some y => exact rdC_inside cs arr ms w x.seat y e _ _ _ (hA b0 x b J y hx hb hJ hin e)
    | none =>
      unfold rdC seatTab
      rw [e]

theorem formsQA_clamp (piece : ℕ) (run : String) (s : S) (w : Wit Cells Tok MsgT)
    (h : ∀ a, segAt? s = some a → InsideAt cs ms own a ∧ InsideAhead cs ms own sent a) :
    formsQA sent own Rd piece run s (rdC cs arr ms w) ↔
      formsQA sent own Rd piece run s (seatTab cs arr ms w) :=
  ⟨formsQA_agree sent own Rd piece run s _ _ fun a ha =>
      (agreeQA_clamp cs arr ms own sent w a (h a ha).1 (h a ha).2).symm sent own,
    formsQA_agree sent own Rd piece run s _ _ fun a ha =>
      agreeQA_clamp cs arr ms own sent w a (h a ha).1 (h a ha).2⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.agreeQ_clamp
#print axioms VerifiableInference.Desc.Sound.agreeQA_clamp
#print axioms VerifiableInference.Desc.Sound.formsQ_clamp
#print axioms VerifiableInference.Desc.Sound.formsQA_clamp
#print axioms VerifiableInference.Desc.Sound.formsTQ_clamp
#print axioms VerifiableInference.Desc.Sound.totalQ_clamp
#print axioms VerifiableInference.Desc.Sound.totalBQ_clamp
