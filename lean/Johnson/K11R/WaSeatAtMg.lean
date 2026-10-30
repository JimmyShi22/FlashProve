-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-



Johnson/K11R/WaSeatAtMg.lean: two of the
named conditions under which the kind K11's law holds at the composed meaning's closed constant (the
fields frontWa and weights of `K11.K11Cond`, LawAtMg.lean), in these fields' own text, at one choice
of the parameter Wa: the condition on the state with its eighth clause (`WaSeat`,
Johnson/Top/H0/MergeLaw/WtJoinsSeat.lean). Two theorems, each one call or a pair of calls.

THE CHOICE. Wa := `WaSeat h.𝔇.arr h.𝔇.N (At.X Zp) (At.num Zp 24 0) 0 V'`, that is: fun s => WaK6
(At.X Zp) V' s ∧ MaskSeatAt h.𝔇.arr h.𝔇.N (At.num Zp 24 0) 0 s. WHY n := At.num Zp 24 0 AND rb := 0:
the constant's sentence for "weights" is `wtK6 cs arr ms N X layout num (num 24 0) 0` (`At.wt`,
`At.wt_reads_own`, Johnson/P5J/LettersAt4.lean). SO R = 0, IN `K11Cond`'s OWN PARAMETER R: its field
front is taken here at R := 0.

THE SEAT IS (73, 2) = seatOf xM (the premise hxM). Where it comes from in `k11_law_atMg`:
`members_atAll` (Johnson/K11R/AtAll.lean) gives pM and xM with `maskPlace (P5T.planSeats Zp Zp.D.1)
Zp.first.shape 24 = some pM` and `xAt (At.ms Zp Z.lay) pM = some xM`; the second gives seatOf xM =
pM (as LawAtMg.lean itself draws it); under the structure that `maskPlace …` is some (73, 2)
(`AtMg.mask_place`, Johnson/HB/LLHARD/MaskSeatWritten.lean): so pM = (73, 2).

WHAT STAYS AS A PREMISE OF EACH, BY NAME, AND WHAT DOES NOT.
  `frontWa_at`. STAYS, on the family Rch: hK6: `WaK6 (At.X Zp) V'` at the unmarked states that meet
    Rch 346 and the table's condition. (A source: waK6_rchAt_at, Johnson/P4R/WaK6AtRchAt.lean, at V'
    := (At.X Zp).P.h.V. It has another form: no table's condition; "a.1.2.failed = none"; its own
    premises hS, hR, O, hOk, hX; and it stands at the family RchAt (FD Z A B c).) TAKEN FROM
    `K11Cond` ITSELF: hfront: its field front, at R := 0: its first fact is the condition `MaskAt`,
    so no second fact on the mask row is wanted of the family (`maskSeatAt_of_front`,
    MaskJoinsNamed.lean). hxM: see above. DO NOT STAY: the two closed premises: `AtMg.mask_sent` and
    `AtMg.mask_num`.
  `weights_at`. STAY, all closed, all `wtK6_of_wtP1`'s own: hplan · hTT · Zs · hl · hlam · hV2 ·
    hd5; and hb : ProofFile.blankBy mk Zp = some Bs.G₀ (in `k11_law_atMg` it is had as hG at mk :=
    ProofFile.pureRoad.links). DO NOT STAY: hcellOf (it is `cellAtNo`'s own text: rfl) · hlay (`hlay_at
    hb`, PlanNumsAt.lean) · hr, hc (`rows_fit`, `cols_fit`, MaskSeatWritten.lean) · h1
    (`AtMg.mask_named`) · hns (`nMsg_le_ns hb`, MaskJoins.lean).

The steps go through:
`h.𝔇.wt` unfolds to `wtK6` at h.𝔇's own fields; h.𝔇.arr and
h.𝔇.N are `At.arr Zp` and `At.N Zp cF` by unfolding; the two rewritings by hxM; `At.X Zp` is
`Zp.p.X`. Two functions are named parOf: the merge's is `K11.parOf`, the output head's
`Kinds.Head.parOf`: both are written out. That the two ends are the fields' text of LawAtMg.lean
(the form with fourteen fields) is Lean's word in Johnson/K11R/CondOfRest.lean, which lays them
into the structure.

Limits. Calls. No premise that stays is shown at any value here. The sentence for "weights" in which
`weights_at` ends is `wtK6` (Johnson/Desc/Kinds/Law/WtK6.lean): by that file's head it speaks AT A
WITNESS WHOSE CELLS HOLD AN INDEX; elsewhere it says nothing. The head is the head with the
fourteen entry tests: `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), on which `mask_sent`,
`mask_num` and `mask_named` rest, stands over the form of the proof file's entry tests with fourteen
rows, two of which are the comparisons with the written plan; the head's field laid says that every
entry test accepts. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.P5J.MgAtAll
import Johnson.K11R.LawAtMg
import Johnson.Top.H0.MergeLaw.MaskJoinsNamed
import Johnson.Top.H0.MergeLaw.WtJoinsSeat
import Johnson.HB.LLHARD.MaskSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (Frame onQ linksFull maskRowAt Mem seatOf)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw (MergeFront maskSeatAt_of_front nMsg_le_ns hlay_at)
open VerifiableInference.Desc.First.FillP1 (wtP1)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6 WaSeat wtK6_of_wtP1_seat)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open P5J (AtMgA mgAtAll TS)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The field frontWa at Wa := `WaSeat …`.** -/
theorem frontWa_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (V' ni : ℕ) (xM : Mem)
    (hxM : seatOf xM = (73, 2))
    (hK6 : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → WaK6 (P5J.At.X Zp) V' a.1)
    (hfront : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      MergeFront (h.𝔇.N.group 24) xM 0 ni a.1) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      WaSeat h.𝔇.arr h.𝔇.N (P5J.At.X Zp) (P5J.At.num Zp 24 0) 0 V' a.1 :=
  fun z a hon hr hm =>
    ⟨hK6 z a hon hr hm,
      maskSeatAt_of_front Rch h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) 346 h.𝔇.arr
        h.𝔇.N (h.𝔇.N.group 24) xM 0 ni (P5J.At.num Zp 24 0)
        (by rw [hxM]; exact h.toAtMg.mask_sent) (by rw [hxM]; exact h.toAtMg.mask_num) hfront z a
        hon hr hm⟩

/-- **The field weights at Wa := `WaSeat …`.** -/
theorem weights_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase) (ni V' : ℕ)
    {mk : ProofFile.LinksBy} (hb : ProofFile.blankBy mk Zp = some Bs.G₀)
    (hplan : (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
      (workOf (P5J.At.X Zp))).ok = true)
    (hTT : (P5J.At.X Zp).T = (P5J.At.X Zp).hS.T)
    {sh : OnBytes.Model.WsShape} (Zs : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok (P5J.At.X Zp).layers.wsLay)
    (hlam : (P5J.At.X Zp).H.lamS = 13) (hV2 : (P5J.At.X Zp).hS.V = 202048)
    (hd5 : (P5J.At.X Zp).hS.d = 5120) :
    ∀ a y w, WaSeat h.𝔇.arr h.𝔇.N (P5J.At.X Zp) (P5J.At.num Zp 24 0) 0 V' a.2 →
      wtP1 (K11.parOf Zp Bs.G₀) ni
        (fun w => VerifiableInference.Desc.K13.Law.cellAtNo w.cells)
        (maskRowAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N 24) a y w → h.𝔇.wt 24 a y w :=
  fun a y w hWa hw =>
    wtK6_of_wtP1_seat h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.X Zp) h.𝔇.layout (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 hplan hTT V' P5J.rows_fit P5J.cols_fit (K11.parOf Zp Bs.G₀)
      (hlay_at hb).symm ni (fun w => VerifiableInference.Desc.K13.Law.cellAtNo w.cells)
      (fun _ _ _ => rfl) h.toAtMg.mask_named (nMsg_le_ns hb) Zs hl hlam hV2 hd5 a y w hWa hw

end K11

#print axioms K11.frontWa_at
#print axioms K11.weights_at
