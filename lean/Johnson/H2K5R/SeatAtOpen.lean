-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/SeatAtOpen.lean: kind K5: **WHAT SITS AT THE KIND's TWELVE NUMBERS OF THE FIRST CHAIN, AND THE PLAN's FACTS THERE, FROM AN OPENING OF THE PROOF FILE's DESCRIPTION**, in scope. No piece, no table: the description's
own list c.blocksInOrder alone. One theorem, its steps lifted out of three bodies that were compiled by Lake: k05_kindTied (Johnson/H2K5R/KindTied.lean), K05_tied_at (TiedAtEntry.lean), K3Lot.tied_of_alone (Johnson/P5K3R/SitsAny.lean).

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Main name: k5_seat_of_open: for g < 12 there are blk (the kind's sub-protocol off the plan), E (the description's own sub-protocol), a, x, xd (the group's plan; the places of the segment's two lookup arguments) with:
  c.blocksInOrder[14 (2 g + 1) + 4]? = some E · E tells no oracle message · E's rounds are the plan's · SeatOf blk E ·
  PlanIs · profile 4 · W.A[g] · two returns of lookAt · K5Plan (seven facts) · k5AtN … = some blk · its own test on the plan · the guard's yes.
IS IT EMPTY HERE? Under an opening in scope: NO OPENING IS SHOWN IN LEAN.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.H2K5R.KindTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Claim RoundAsG Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers start flatPlaces flatPlacesOf)

/-- **The seat and the plan at the kind's place of group g, from an opening.** -/
theorem k5_seat_of_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : WholeD} (hs : ∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction P.pol lay P.KL F D, t.2 = true) {g : ℕ} (hg : g < 12) :
    ∃ (blk E : Block First.S Claim) (a : Attention.Plan) (x xd : VerifiableInference.Desc.First.Look.Place),
      c.blocksInOrder[14 * (2 * g + 1) + 4]? = some E ∧ E.oracles.flatten = [] ∧
      E.rounds = rounds (parO Bs.G₀.W (2 * g + 1) a ((H2K5.k5Before? Z ("A" ++ toString g)).getD [])) ∧ SeatOf blk E ∧
      PlanIs Bs.G₀.W ∧ Bs.G₀.W.p4 = true ∧ Bs.G₀.W.A[g]? = some a ∧ lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
      lookAt Bs.G₀.W (2 * g + 1) true = some xd ∧
      K5Plan (parO Bs.G₀.W (2 * g + 1) a ((H2K5.k5Before? Z ("A" ++ toString g)).getD [])).own (2 * g + 1)
        (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) false x) (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) true xd)
        a.seam.tl.f9 (Forest.elems a.fs) (slotsOf (script a.own) + Forest.elems a.seam.tl.f9) a.ns ∧
      k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some blk ∧ blk.planOk = true ∧
      k5GuardN Bs.G₀.W (2 * g + 1) g = true := by
  obtain ⟨h4, g', hg', e⟩ := att_only O.pub O.blank (IM.subs_att hS hR O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨Lk, Eb, -, e1, e2, -, -⟩ := k5_alone O h4 hg'
  have e3 := IM.flatIx_scope hS hR O (l := 2 * g' + 1) (by omega) 2
  have hfl : c.blocksInOrder[14 * (2 * g' + 1) + 4]? = some Eb := by
    have hfl0 := IM.hear_at_flat e1 e2
    rw [e3, show 14 * (2 * g' + 1) + 2 + 2 = 14 * (2 * g' + 1) + 4 by omega] at hfl0
    exact hfl0
  obtain ⟨sv, hfp', -, hk0, -⟩ := K05_place_at O h4 hg'
  have eP : Eb.place = ⟨1, some (2 * g' + 1), 3, .K5⟩ := by
    rw [← hfp', List.getElem?_map, IM.hear_at_flat e1 e2] at hk0
    exact Option.some.inj hk0
  obtain ⟨-, hP, Hx⟩ := K05_facts_of_open O hpl hs
  obtain ⟨g2, blk, a, x, -, hg2, hfl2, hla, hat, -, hok, hG, ea, hx, -⟩ :=
    Hx Eb (List.mem_of_getElem? hfl) (by rw [eP])
  obtain ⟨sv2, hfp2, -, hk2, -⟩ := K05_place_at O h4 hg2
  have eP2 : Eb.place = ⟨1, some (2 * g2 + 1), 3, .K5⟩ := by
    rw [← hfp2, List.getElem?_map, hfl2] at hk2
    exact Option.some.inj hk2
  obtain rfl : g2 = g' := by
    have e4 : (some (2 * g2 + 1) : Option ℕ) = some (2 * g' + 1) :=
      congrArg Place.link (eP2.symm.trans eP)
    have e5 := Option.some.inj e4
    omega
  obtain ⟨xd, hxd, -, -, hPn⟩ := k5Plan_of_public hP h4 ea hx (Params.settingOf Bs.G₀.W.P.frame)
  have Pn := hPn (digits_shape hP h4 ea hxd _)
  obtain ⟨a', ea', eb⟩ := k5AtN_is _ _ _ _ _ hat
  have haa : a' = a := Option.some.inj (ea'.symm.trans ea)
  rw [haa] at eb
  have er : Eb.rounds = rounds (parO Bs.G₀.W (2 * g2 + 1) a
      ((H2K5.k5Before? Z ("A" ++ toString g2)).getD [])) := by
    rw [(IM.alone_underR hla).1]
    show blk.rounds = _
    rw [eb]
    rfl
  have ho : Eb.oracles.flatten = [] := by
    rw [IM.alone_oracles hla]
    show blk.oracles.flatten = []
    rw [eb]
    show ((rounds (parO Bs.G₀.W (2 * g2 + 1) a ((H2K5.k5Before? Z ("A" ++ toString g2)).getD []))).map
      fun _ => []).flatten = []
    simp
  exact ⟨blk, Eb, a, x, xd, hfl, ho, er,
    seatOf_same (Bst' := IM.k5Dress Z ("A" ++ toString g2) blk) rfl rfl
      ⟨IM.alone_underR hla, fun s rs gs t hy => ((IM.yes_alone hla (fun e => nomatch e) s t rs gs).1 hy).2.1⟩,
    hP, h4, ea, hx, hxd, Pn, hat, hok, hG⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5_seat_of_open
