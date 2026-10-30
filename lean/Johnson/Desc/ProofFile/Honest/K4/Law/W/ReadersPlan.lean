-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ReadersPlan.lean: CONDITIONAL: on the library's hypothesis h
on the public files. THE FULL SIZE ALONE.

What is here. THE PLAN's SIDE OF THE TWO TIES ON THE LIBRARY's READERS in front of the member of the
feed-forward layers' own rounds (sub-protocol K4): three statements on public values, under h and
`LaidK4` alone. Law/W/ReadersHead.lean imports this file.
Why
they are laid apart: so that a law which needs them need not import what that file imports besides
(through Law/W/NuHead.lean: laws at a state with an accepted step of the member). Nothing new is
shown.

  `pinsTests_head`   the library's `K4PinsTests` under h and `LaidK4`.
  `sitsIn_head`   the library's `SitsIn` at the lookup's place of the segment.
  `arrayNames_head`   the link's list of names in what the caller reads is `P5J.At.names3`.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). Lh (`LaidK4`,
Law/SeatedHead.lean) and hx: on public lists and numbers. Beneath `pins_head` and `first_paid` stand
closed facts on written values that Lean's kernel has decided in the library. TWO STATEMENTS OF
FILES UNDER Johnson/Goal/ ARE CALLED BY NAME: `Meaning.scope_plans` in `sitsIn_head` and
`OnBytes.Road.Hd.core_of_scope` in `pinsTests_head`. THE FULL SIZE ALONE, and the format's second
hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RecFrontHead
import Johnson.Road.K4.W.TwoReaders
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PlanAllPaid
import Johnson.Road.K4.K4PinsFirstScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (eAll parOf K4PinsTests pins_head first_paid written_of_head xNine_of_laid
  namesTied_of_scope XNine SitsIn fitF_wide pinsFill_const group_at layAt_plan cutW posFree
  maskRowsAt refPub_in_scope)
open OnBytes.Road.K4.W (sym_two mask_two)
open OnBytes.Maker (WholeD)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.PlanWritten (publicSteps_of)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt pubAt stepOf sigListCalls Stored.entries)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ mgBase seatTab)
open VerifiableInference.OnPublicFiles (layNu)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Here_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 The plan's side, under h -/

/-- CONDITIONAL: on h and Lh. **The library's tests on the pinned readers.** -/
theorem pinsTests_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    K4PinsTests h.𝔇 (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull) Zp (28 * g + 4) g
      (parOf x) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, -, Hh⟩ := k4Here_head h Lh
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  have W := written_of_head h.toAtMg
  have H9 : XNine Zp.p.X :=
    xNine_of_laid hpub (OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub) W.layout h.plan.laid
  exact pins_head h VerifiableInference.Desc.K13.Law.LFull (P5J.laid_at_head h.toAtMg) O g Lh.lt x
    blk₀ Hh (first_paid W H9 (namesTied_of_scope h.scope h.reads O) Lh.lt)

/-- CONDITIONAL: on h, Lh and hx. **The library's `SitsIn` at the lookup's place of the
segment.** -/
theorem sitsIn_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    SitsIn (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link) (fun j => h.𝔇.l3.seat xl.link false j.1)
      h.𝔇.ms h.𝔇.N (2 * g) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, -, Hh⟩ := k4Here_head h Lh
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  have N := nine_head h Lh
  obtain ⟨x₁, hx₁, el, e1, e2, e3, _⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at el e1 e2 e3
  obtain ⟨k4, _, _⟩ := _root_.Meaning.scope_plans h.scope h.reads hpub
  have Pf := pinsFill_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Z) h.plan.shape Z.lay h.plan.laid
    h.plan.hN h.plan.hG xh OnBytes.Flat.numsFull.rows
  obtain ⟨radM, Q3⟩ := Pf.ms
  have eg : (parOf x).g = g := Lh.grp
  have Pt := pinsTests_head h Lh
  have F := fitF_wide Zp radM h.𝔇 (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase
    (parOf x)
    Pf.sent Pf.arr Q3 Pf.nSent Pf.nIndex Pf.seat3 (by rw [eg]; exact Pt.first)
    (by rw [eg]; exact Lh.lt) xl (by rw [el, eg]; exact Lh.seg) (O.W ▸ Hh.G) (posFree 0)
    (publicSteps_of hpub) (refPub_in_scope h.scope h.reads hpub (by rw [eg]; exact Lh.lt))
    (O.W ▸ Hh.P) ⟨e1.trans N.Sx.shape, by rw [N.Sx.y]; exact e2, e3⟩ (group_at k4 _)
    (by rw [eg, ← Lh.seg]; exact N.Sx.notHead)
  have q := F.sits
  rw [eg] at q
  exact q

/-- CONDITIONAL: on h. The link's list of the arrays' names. -/
theorem arrayNames_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (l : ℕ) :
    h.𝔇.sent.arrayOf.getD l #[] = P5J.At.names3 Zp l := by
  have Pf := pinsFill_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Z) h.plan.shape Z.lay h.plan.laid
    h.plan.hN h.plan.hG xh OnBytes.Flat.numsFull.rows
  have e : h.𝔇.sent = OnBytes.Road.K4.sentAt Zp := Pf.sent
  rw [e]
  show (Zp.made.p.built.links.map (·.arrayOf)).getD l #[] =
    ((Zp.made.p.built.links[l]?).map (·.arrayOf)).getD #[]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.pinsTests_head
#print axioms ProofFile.Honest.K4.W.sitsIn_head
#print axioms ProofFile.Honest.K4.W.arrayNames_head
