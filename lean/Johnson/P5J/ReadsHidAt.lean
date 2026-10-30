-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsHidAt.lean: THE HIDDEN INTEGERS OF A SEGMENT READ OF THE WITNESS ONLY WHAT THE
TABLE BOOKS FOR THAT SEGMENT: the fields `base`, `lay` and `att` of `HidReads`
(Johnson/Desc/Sound/ReadsConstr.lean) at the closed constant. One closed test with code and ten
theorems: two by the kernel (one a negative test), the others joinings.
Why. The items `constr k p` ride past most sub-protocols; every kind's fifth tie asks that their
sentences read the witness through the booked components alone. The hidden values are built by a
make that, where a segment only reads an array, takes the OWNER's list: so a segment's sentence
might read another segment's messages. It does not, in value: where reader's and owner's readings
agree, the lists of the hidden values are the segments' own.
  `AtMgA.readAt_one`: two witnesses that are one on what the table books for `constr k p` give
    segment k one reading.
  `AtMgA.MG_own`, `AtMgA.MA_own`: under hp : `OffPad.padsAtZ Zp = true`, for g < 12: the hidden
    list of group g of layers is segment 2 g's own list, off its own reading; that of attention g
    is segment 2 g + 1's.
  `AtMgA.hidReads_base`: the field base: no test is spent.
  `AtMgA.hidReads_lay`, `AtMgA.hidReads_att`: the two fields, under hp.
  `AtMgA.hidReads_lay_pin`, `AtMgA.hidReads_att_pin`: the same under the pin on what the planner
    made.
  `linksLayB_full`, `linksLay_control`: the even segments below 24 of the written list are layers'
    segments: by the kernel; segments 1 and 24 are not.
How: `hidAtF_MG`, `hidAtF_MA`, `ownAtF_eq` (Johnson/Goal/Meaning/HidFamily.lean) with
`fit_sizesOf` and `k03_reads_at` (Johnson/P5J/PadsFreeAt.lean); `oneOn_of_reads`,
`readAt_same` (Johnson/Desc/Kinds/Law/ReadsOkK6.lean); `partG_congr` (Sound/ReadsConstr.lean).
Limits: NO PROMISE AND NO "REACHED" IS SPENT. The head h is a premise. `padsAtZ Zp` is a test with
code on public data: evaluated true at both full-size sets of public files, with three coarse
negative tests: an evaluation. The field digits is not touched; head:
Johnson/P5J/ReadsHeadAt.lean. The full size alone. No soundness is claimed.

-/
import Mathlib
import Johnson.Desc.Sound.ReadsConstr
import Johnson.Desc.Kinds.Law.ReadsOkK6
import Johnson.Goal.Meaning.HidFamily
import Johnson.P5J.PadsFreeAt
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model OnBytes.Road
open Inst.Model Inst.Model.All
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.First (Item Comp ModelPart)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (szOf)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ tests_of_pin Came.oneOn_of_reads
  Came.readAt_same)
open VerifiableInference.PlanWritten (madePinnedAt)
open _root_.Meaning (fLay sizesOf fit_sizesOf hidAtF_MG hidAtF_MA ownAt)

/-- The even segments below 24 of the written list are layers' segments. -/
def linksLayB : Bool := (List.range 12).all fun g => At.links[2 * g]? == some ModelPart.layers

theorem linksLayB_full : linksLayB = true := by decide +kernel

/-- **Negative tests**: segment 1 (an attention's) and segment 24 (the head's) are no layers'. -/
theorem linksLay_control :
    (At.links[1]? == some ModelPart.layers) = false ∧ (At.links[24]? == some ModelPart.layers) = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "WT" => Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT

/-- Segment k's reading is one at witnesses that are one on what is booked for `constr k p`. -/
theorem AtMgA.readAt_one (h : AtMgA o Z D r Zp Np cF x) (k : ℕ) (p : TPart) (w w' : WT)
    (hs : SameAt h.𝔇 At.links k p w w') :
    readAt (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) k w =
      readAt (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) k w' :=
  Came.readAt_same (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) k w w'
    (Came.oneOn_of_reads (At.arr Zp) (At.N Zp cF) At.links (.constr k p) w w' hs)

/-- The hidden list of a group of layers is its segment's own, off that segment's own reading. -/
theorem AtMgA.MG_own (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true) {g : ℕ}
    (hg : g < 12) (w : WT) :
    (h.𝔇.H.hid w).MG g =
      ownAt (sizesOf (At.X Zp))
        (_root_.Meaning.seatBy (fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (sizesOf (At.X Zp)))
        (readAt (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (2 * g) w) (2 * g) :=
  hidAtF_MG (fit_sizesOf h.toAtMg.pubOne h.toAtMg.coreScope (fLay (At.layout Zp) (At.num Zp))).1
    (k03_reads_at h hp w) (tokVOf w.tok) hg

/-- The like for an attention sub-proof. -/
theorem AtMgA.MA_own (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true) {g : ℕ}
    (hg : g < 12) (w : WT) :
    (h.𝔇.H.hid w).MA g =
      ownAt (sizesOf (At.X Zp))
        (_root_.Meaning.seatBy (fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (sizesOf (At.X Zp)))
        (readAt (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (2 * g + 1) w)
        (2 * g + 1) :=
  hidAtF_MA (fit_sizesOf h.toAtMg.pubOne h.toAtMg.coreScope (fLay (At.layout Zp) (At.num Zp))).1
    (k03_reads_at h hp w) (tokVOf w.tok) hg

/-- **The field `base` of `HidReads`, at the constant.** -/
theorem AtMgA.hidReads_base (h : AtMgA o Z D r Zp Np cF x) :
    ∀ k w w', k < At.links.length → SameAt h.𝔇 At.links k .small w w' →
      h.𝔇.H.base k w → h.𝔇.H.base k w' := by
  intro k w w' _ hs hb
  have e := h.readAt_one k .small w w' hs
  have hb0 : Cb.Pv.Tail.Base (_root_.Meaning.symAt (sizesOf (At.X Zp) k)
      (_root_.Meaning.seatBy (fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (sizesOf (At.X Zp)) k)
      (readAt (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) k w)) := hb
  show Cb.Pv.Tail.Base (_root_.Meaning.symAt (sizesOf (At.X Zp) k)
      (_root_.Meaning.seatBy (fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (sizesOf (At.X Zp)) k)
      (readAt (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) k w'))
  rw [← e]
  exact hb0

/-- **The field `lay`.** -/
theorem AtMgA.hidReads_lay (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true) :
    ∀ k p i a w w', k < At.links.length → k ≠ headLink (At.X Zp) → k % 2 = 0 → p ≠ .lookDigits →
      SameAt h.𝔇 At.links k p w w' →
      partG (At.X Zp) i (h.𝔇.put (h.𝔇.H.req a) (h.𝔇.H.hid w).tok).val (h.𝔇.H.hid w).MG (k / 2) p →
      partG (At.X Zp) i (h.𝔇.put (h.𝔇.H.req a) (h.𝔇.H.hid w').tok).val (h.𝔇.H.hid w').MG (k / 2)
        p := by
  intro k p i a w w' hk h24 he _ hs hw
  rw [headLink_in_scope h.scope h.reads h.pubOne] at h24
  have hk25 : k < 25 := hk
  have hg : k / 2 < 12 := by omega
  have e2 : 2 * (k / 2) = k := by omega
  have hM : (h.𝔇.H.hid w).MG (k / 2) = (h.𝔇.H.hid w').MG (k / 2) := by
    rw [h.MG_own hp hg w, h.MG_own hp hg w', e2, h.readAt_one k p w w' hs]
  have hlay : At.links[k]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayB_full (k / 2) (List.mem_range.2 hg)
    rw [e2] at h0
    simpa using h0
  refine partG_congr hM (fun hpp => ?_) hw
  have htok : w.tok = w'.tok := by
    refine hs Comp.tok ?_
    unfold Item.reads
    refine List.mem_append_right _ ?_
    rcases hpp with rfl | rfl
    · simp [hlay]
    · simp [hlay]
  show (h.𝔇.put (h.𝔇.H.req a) (tokVOf w.tok)).val = (h.𝔇.put (h.𝔇.H.req a) (tokVOf w'.tok)).val
  rw [htok]

/-- **The field `att`.** -/
theorem AtMgA.hidReads_att (h : AtMgA o Z D r Zp Np cF x) (hp : OffPad.padsAtZ Zp = true) :
    ∀ k p w w', k < At.links.length → k ≠ headLink (At.X Zp) → k % 2 ≠ 0 → p ≠ .lookDigits →
      SameAt h.𝔇 At.links k p w w' →
      partA (Hd.shapeA (At.X Zp) (k / 2)) ((h.𝔇.H.hid w).MA (k / 2)) p →
      partA (Hd.shapeA (At.X Zp) (k / 2)) ((h.𝔇.H.hid w').MA (k / 2)) p := by
  intro k p w w' hk _ he _ hs hw
  have hk25 : k < 25 := hk
  have hg : k / 2 < 12 := by omega
  have e2 : 2 * (k / 2) + 1 = k := by omega
  have hM : (h.𝔇.H.hid w).MA (k / 2) = (h.𝔇.H.hid w').MA (k / 2) := by
    rw [h.MA_own hp hg w, h.MA_own hp hg w', e2, h.readAt_one k p w w' hs]
  rw [← hM]
  exact hw

/-- The two under the pin on what the planner made. -/
theorem AtMgA.hidReads_lay_pin (h : AtMgA o Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ∀ k p i a w w', k < At.links.length → k ≠ headLink (At.X Zp) → k % 2 = 0 → p ≠ .lookDigits →
      SameAt h.𝔇 At.links k p w w' →
      partG (At.X Zp) i (h.𝔇.put (h.𝔇.H.req a) (h.𝔇.H.hid w).tok).val (h.𝔇.H.hid w).MG (k / 2) p →
      partG (At.X Zp) i (h.𝔇.put (h.𝔇.H.req a) (h.𝔇.H.hid w').tok).val (h.𝔇.H.hid w').MG (k / 2)
        p :=
  h.hidReads_lay (tests_of_pin h.toAtMg hy).2

theorem AtMgA.hidReads_att_pin (h : AtMgA o Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ∀ k p w w', k < At.links.length → k ≠ headLink (At.X Zp) → k % 2 ≠ 0 → p ≠ .lookDigits →
      SameAt h.𝔇 At.links k p w w' →
      partA (Hd.shapeA (At.X Zp) (k / 2)) ((h.𝔇.H.hid w).MA (k / 2)) p →
      partA (Hd.shapeA (At.X Zp) (k / 2)) ((h.𝔇.H.hid w').MA (k / 2)) p :=
  h.hidReads_att (tests_of_pin h.toAtMg hy).2

end P5J

#print axioms P5J.linksLayB_full
#print axioms P5J.linksLay_control
#print axioms P5J.AtMgA.readAt_one
#print axioms P5J.AtMgA.MG_own
#print axioms P5J.AtMgA.MA_own
#print axioms P5J.AtMgA.hidReads_base
#print axioms P5J.AtMgA.hidReads_lay
#print axioms P5J.AtMgA.hidReads_att
#print axioms P5J.AtMgA.hidReads_lay_pin
#print axioms P5J.AtMgA.hidReads_att_pin
