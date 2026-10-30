-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftCells.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THE SENTENCE cells
OF THE NAMED REST OF THE FIELD hLeft (`LeftRest`, Johnson/Desc/First/Link/Law/LeftOfRest.lean): AT
THE PART THAT KIND K9's LENS READS IN FRONT OF THE BATCHING, UNDER THE TABLE's PROMISE AND
"REACHED": THE DICTIONARY ON THE DIGITS' CELLS (CellOkR): FROM THE HEAD, ONE PREMISE ON REACHED
STATES (F: the structure FoldFacts, which other files have from the head) AND SEVEN PREMISES ON
PUBLIC DATA, IN FOUR GROUPS. No other premise on a state is left. Theorems: a joining, by calls. A
law file; no running text imports it.
  `cells_have_seats`  DigOK ⊢ every cell that the first four claims read has a seat, which lies in
                    its table: the two kinds of cells are among the addresses that the lookup reads
                    (reads_bz, reads_zz; "2 ^ cK = NC" and "a piece's first column is
                    its call's" out of DigOK's own test on the structure).
  `AtMgA.left_cells`  the sentence, at the letters of what is left of K9.
WHO PAYS WHAT. On the state: the frame, the layout, the list of arrays: cell_front
(CellFront.lean) · the codes, the two tests atFirstSeats and atFirstShapes, the live request's own
messages' numbers: FoldFacts' fields codes, seatsCarried, msgShapes, frameIs · bookAt: the promise
(onT_bools) · no mark: the promise. LEFT, ALL ON PUBLIC DATA: hp | hpl (the batching's place bears
the link: closed) · h3 (the link has at most three moments) · hT1 | hT2 (seatsPubB | shapesPubB,
CellTests.lean: the plan's lists have the list's seats and shapes at the own messages' numbers) · hB
| hZ (laidArrB, CellPub.lean: the layouts of the counts' and the digits' arrays pass the programs'
own test).

Limits. AN IMPLICATION. F is a premise (other files have it from the head). The public sentences
are evaluated at no plan here. At OnBytes.secondHashFunction. Nothing on soundness or on hiding.

-/
import Johnson.P5J.K09LeftPub
import Johnson.P5J.K09List
import Johnson.P5J.FoldAt
import Johnson.LPFK9R.HtinAtConstant
import Johnson.TocK8R.AtSeat
import Johnson.Desc.First.Link.Law.CellTests
import Johnson.Desc.First.Link.Law.CellPub
import Johnson.Desc.First.Link.Law.CellFront
import Johnson.Desc.First.Link.Law.FromPromise
import Johnson.Desc.First.Look.K3DigRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S FoldFacts momentAt shiftAt)
open VerifiableInference.Desc.First.Look (digList DigOK seatOf ReadsDig reads_bz reads_zz)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.LinkJoin (batchAt onTR onT_bools seatsPubB shapesPubB laidArrB
  laidPub_of_B cellOkR_of_facts cell_front part_reads)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- Every read cell has a seat, which lies in its table. -/
theorem cells_have_seats {set : Params.Setting} {y : Desc.First.Look.Place} {tl : HTailF2}
    {Ds : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {pp : ℕ} (H : DigOK set y tl Ds rad pp) :
    ∀ ad, cellAddr tl ad →
      ∃ s, seatOf Ds y.link ad = some s ∧ s.Fits Ds.codes (digList y Ds rad) := by
  obtain ⟨-, hT, hP⟩ := DgP.shape2_parts H.tail
  intro ad had
  have hRd : ReadsDig tl y.F.next ad := by
    rcases had with ⟨r, i, hr, hi, rfl⟩ | ⟨q, pc, r, i, hq, hpc, hr, hi, rfl⟩
    · exact reads_bz tl _ hP.full hr hi
    · exact reads_zz tl _ hT hq hpc (hP.held q (by rw [hT.nc]; exact hq) pc hpc).2.2 hr hi
  exact (H.resolves ad hRd).2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

open VerifiableInference.Desc in
/-- **cells.** -/
theorem AtMgA.left_cells (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Ld : Laid}
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps)
    {m : ℕ} (hm : m < 25) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (At.X Zp) m = some (xx, tlD)) {p : Desc.Place}
    (hp : At.ps[batchAt fullLinks At.ps m]? = some p) (hpl : p.link = some m)
    (h3 : ∀ L, Zp.first.shape.link[m]? = some L → reqMoments L ≤ 3)
    (hT1 : seatsPubB ((At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece)) h.𝔇.N
      (some p) Ld (h.𝔇.N.group m)
      (List.ofFn fun j : Fin (digList xx h.𝔇.sent h.𝔇.l3.rad).length =>
        h.𝔇.l3.seat xx.link true j.1) = true)
    (hT2 : shapesPubB ((At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece)) h.𝔇.N
      (some p) (msgsOfChain Zp.made.proof.1) ((digList xx h.𝔇.sent h.𝔇.l3.rad).map (·.1)) = true)
    (hB : laidArrB h.𝔇.sent (digList xx h.𝔇.sent h.𝔇.l3.rad) xx.link tlD.ix.BZ = true)
    (hZ : laidArrB h.𝔇.sent (digList xx h.𝔇.sent h.𝔇.l3.rad) xx.link tlD.ix.ZZ = true)
    (z : ProofFile.InstPub) :
    ∀ a pa, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) a → atS.get? a.1 = some pa →
      CellOkR xx tlD h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
        (h.𝔇.N.group m) pa := by
  intro a pa ho hpa
  obtain ⟨set, pp, H⟩ := h.left_dig hm hd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, Xl, _, e3, _⟩ := TocK8.k08_scope h.scope h.reads O m hm
  have hu : a.1.failed = none := Classical.not_not.1 ho.1.2
  have hrch : h.toAtMg.rch (batchAt fullLinks At.ps m) ((z, a.1), a.2) := ho.2
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * m + IM.nAt m + 2) (z, a.1) := by
    rw [← LPFK9.batch_nAt m hm]
    exact list_rchIs h z _ _ ho.2
  have el : xx.link = m := IM.lookAt_link (look_of_dig hd)
  obtain ⟨c1, c2, c3, -⟩ := cell_front h.scope h.reads O hm e3 h3 hr hpa
  have hL := (part_reads a.1 pa hpa).1
  obtain ⟨-, hown, -, -⟩ := F.frameIs _ ((z, a.1), a.2) p m pa.L hrch hu hp hpl hL
  have hbook := (onT_bools _ _ _ _ z _ a ho.1).2.2.2.2.2
  rw [hp] at hbook
  refine cellOkR_of_facts xx tlD h.𝔇.sent h.𝔇.l3.rad _ _ hpa (by rw [el]; exact c1) c2
    (by rw [el]; exact c3) (F.codes _ _ hrch hu) hown hbook (F.seatsCarried _ _ hrch hu)
    (F.msgShapes _ _ hrch hu) hT1 hT2 (fun ad had => ?_) (fun ad s had hs => ?_)
    (laidPub_of_B _ _ _ _ hB hZ)
  · obtain ⟨s, hs, -⟩ := cells_have_seats H ad had
    rw [hs]
    rfl
  · obtain ⟨s', hs', hf⟩ := cells_have_seats H ad had
    obtain rfl : s' = s := Option.some.inj (hs'.symm.trans hs)
    exact hf

end P5J

#print axioms P5J.cells_have_seats
#print axioms P5J.AtMgA.left_cells
