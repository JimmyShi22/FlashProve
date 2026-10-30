-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ShowsAtReach.lean: the smallness test (K8): the verifier's state and public
data alone: UNDER THE LIBRARY's HEAD, AT EVERY STATE THAT IS REACHED IN FRONT OF A SEGMENT's DRAW,
HAS NOT FAILED AND PASSES THE TABLE's TEST ON THE BOOK (`bookAt`, Johnson/Desc/First/Borders.lean),
THE LIBRARY's SENTENCE ON THE LAYOUT `ShowsAt` (Johnson/P1K8R/SmallJoin.lean) HOLDS, AT EVERY
WITNESS: the state's record has the plan's number and list of matrices, and the cell that `cellsAt`
reads in a matrix's symbol array is the entry that `readAt` (Johnson/Desc/Sound/ReadAt.lean) reads
in the witness's message of the plan's number, at the row and place at which the layout lays the
element. One theorem; no definition.

  **`shows_at_reach`**
How. It is the middle of the library's own proof of `small_of_owes`
(Johnson/P1K8R/SmallAtDraw.lean), cut out and given a name. That law's premises on the plan and on
every reached state are met under the head by laws of the library: `atMgR_of_head`
(Johnson/P5J/StartAtHead.lean: the facts on every reached state), `smallPlan_at`
(Johnson/K8Q35R/MatsAtHead.lean), `k08_fold_at` (Johnson/P1K8R/FoldAtDraw.lean), `matAt_of_fold`
(Johnson/P1K8R/MatAtFold.lean), `k8LaidOwn` (Johnson/P1K8R/FrontAtSeat.lean), `fork_of_link`,
`seat_of_laidThere` (Johnson/Goal/Meaning/HidSeatsOf.lean), `read_is_entry` and `cell_is_entry`
(Johnson/P1K8R/ShowsJoin.lean). THREE PREMISES ON THE STATE STAY: hr (it is reached), hu (it has not
failed), hB (the test on the book).
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath.
Tactics that search: `omega` on two lines, on l.
Limits. The head is a hypothesis. The full size alone. It says which entry of a witness is read, and
nothing of what any witness holds there. No prover, no Script, no input, no coin.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.K8Q35R.MatsAtHead
import Johnson.P1K8R.SmallAtDraw
import Johnson.P1K8R.SmallAtHead
import Johnson.P1K8R.FillAt
import Johnson.P5J.StartAtHead
import Johnson.HB.LLHARD.Q38A.ForkOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Block Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf bookAt)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7_of_test)
open VerifiableInference.Desc.K9 (seatAt seatAt_mem)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA)
open P1K8T (ShowsAt seatC)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The library's sentence on the layout, at every reached state in front of a draw.** On the
verifier's state and public data alone; the witness is a letter. -/
theorem shows_at_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) (z : ProofFile.InstPub) (s : S)
    (hr : RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (drawAt l) ((z, s), ()))
    (hu : s.failed = none)
    (hB : bookAt (P5J.At.N Zp cF) (flatPlacesOf linksFull true)[drawAt l]? s = true)
    (w : Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT) : ShowsAt Zp cF Z.lay l (z, s) w := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨L₀, A₀⟩ := P5J.atMgR_of_head h (Str := Unit)
    (fun k a => RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a) (fun _ _ u => u)
  have T := K8Q35.smallPlan_at h A₀.listed hG hl e3
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr' : RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) ((z, s), ()) := by
    rw [← P1K8T.drawAt_place]
    exact hr
  obtain ⟨L, -, -, hL, -, -, -, e1, e2, -, -, -⟩ := P1K8T.k08_fold_at h hG hl e3 ((z, s), ()) hr
  have hL' : s.link? = some L := hL
  obtain ⟨F, hF⟩ := Q38.fork_of_link s L hL'
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx ((z, s), ()) hr'
  have eP : tlP = Meaning.tlAt (P5J.At.X Zp) l := by
    rw [P1K8T.planAt_tlAt hv, O.W]
    rfl
  intro tl ht
  have e7 : seven tl = seven (Meaning.tlAt (P5J.At.X Zp) l) := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [show (((z, s), ()) : (ProofFile.InstPub × S) × Unit).1.2.tl? = some tl from ht] at e
    rw [← eP]
    exact Option.some.inj e
  have eG : tl.gtTree = (Meaning.tlAt (P5J.At.X Zp) l).gtTree := congrArg (·.1) e7
  refine ⟨congrArg (·.2.2.2.2.1) e7, congrArg (·.2.2.2.2.2.2) e7, fun μ r c hr1 hc1 => ?_⟩
  obtain ⟨A, rp, hA, -, -, hrp, eS⟩ :=
    Meaning.seat_of_laidThere h.plan.laid (P5J.At.num Zp) (by omega : l < 25) μ hr1 hc1
  obtain ⟨p, hp, hlk, hpc, hmo⟩ := P1K8T.draw_place_full l hl
  have T1 := T.mats μ.val μ.isLt A hA
  rw [← hmo] at T1
  obtain ⟨o, q, hwi, hok, hq, hn⟩ := P1K8T.matAt_of_fold (Zp := Zp) (cF := cF) A₀.fold
    (a := ((z, s), ())) (l := l) hr hu hp hlk hpc hL' hB T.lawful
    (name := Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val)))
    ((Meaning.reqArray_eq_arrayOf _ _ _).trans hA) T1
  have hxx : L.arrayOf[tl.gtTree.getD μ 0]? =
      some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val))) := by
    rw [e1, eG]
    exact T.names μ.val μ.isLt
  have haa : OnBytes.reqArray L.check.rows.layout
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val))) = some A := by
    rw [e2, P1K8T.layout_at hG, Meaning.reqArray_eq_arrayOf]
    exact hA
  have hN1 := h.plan.hN l μ r c hr1 hc1
  rw [eS] at hN1
  rw [show seatC Zp l μ r c = _ from eS,
    P1K8T.read_is_entry (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l w hN1
      (seatAt_mem _ _ _ _ hq) hn]
  exact (P1K8T.cell_is_entry (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
    z s hL' hF ht hxx haa hwi hok hq w hrp).symm

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.shows_at_reach
