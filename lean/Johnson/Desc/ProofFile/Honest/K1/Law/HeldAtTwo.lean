-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtTwo.lean: the kind K1's opening (number 2 of the first
chain's flat list), under the library's head: the samples' test holds at border 3 behind an
accepting step, at a state in front that is reached and passes the test on the book, at a meaning
whose held is smpHeld. Beside the step no premise speaks of the state behind, and the samples' test
in front is not asked.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), blk whatever stands at number 2 in the first chain's flat list, and s, s'
the states in front of and behind an accepting step of blk (IM.Yes).
  - samples_opening_head: samplesHeld (Johnson/Desc/First/Borders.lean) at the numbers
    P5J.At.N Zp cF and the written lists IM.linksW and IM.placesW holds at border 3 at s'. Its
    premises beside the step: the meaning's held is smpHeld (hH); s is reached at number 2 of the
    flat list (hreach); the test on the book at s (hbk). The form is samples_W_head's
    (Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtW.lean), less the samples' test in front: nothing
    rides here: every seat with a sample that is open at border 3 is a new message's
    (seatsIn_written's second half, Johnson/Desc/K1/Law/RadiiAtTwo.lean, by Lean's kernel: each is
    the seat, behind no tree, of a message of the first sending that has an out-of-domain (OOD)
    sample).
No thread, no prover and no proof file's bytes occur. No definition. One theorem.

How it fits. What stands at number 2 stands under the bare joined sub-protocol K1.openingZero
(first_under, Johnson/IMR/FirstUnder.lean), which is a sending of firstPar Bs.G₀.first (gpOf Zp)
(isSend_openingZero) and leaves the book as a sending does (openingZero_rec's fifth clause:
Johnson/Desc/K1/Law/OpeningZero.lean). These parameters are the written parGF (eG_atAll), the head's
numbers read, in the four fields that sampledIn reads, as N0Full (atAll_letters;
atBlocks_seats, Johnson/Desc/First/NumbersAtBlocks.lean, says that atBlocks leaves the four), and
the book in front has no tree (hbk, nums_atAll). Then held_behind_send (HeldAtW.lean), which is
general in the sending, at the message that seatsIn_of gives out of seatsIn_written.
The statement is not idle, and the sealed test can fail: there are four such seats (tenants_three,
tenants_three_ne, Johnson/Desc/K1/Law/TenantsAtThree.lean); at the seat of the mask's message the
test says no (seatsIn_rejects, RadiiAtTwo.lean).
That no seat with a sample is open at border 2 is RowG's field noneIn
(Johnson/Desc/K13/Law/AtTableFirst.lean; rowG_head,
Johnson/Desc/ProofFile/Honest/K1/Law/OpeningAtHead.lean): it is not used here.
No mark behind the step: mark_opening_head (OpeningAtHead.lean). The six tests: xk_opening_head
(the same file).

Lemmas used beside these: StepG.decide (AtTableFirst.lean), Yes.under (Johnson/IMR/HandsDef.lean);
eG_atAll, nums_atAll (Johnson/Desc/K1/Law/TiesAtAll.lean), atAll_letters, hOk_atAll
(Johnson/Desc/K1/Law/TestsAtAll.lean), pin1_atAll, pin2_atAll
(Johnson/Desc/K1/Law/PinsAtHead.lean); own_first, planOwn_of (Johnson/Desc/K1/Law/PlanOwn.lean);
atFirstFits_all (Johnson/IMR/AtReach.lean), bookFitsB_iff (Johnson/Desc/Sound/BookTestsLaw.lean);
linksW_full, placesW_full (Johnson/IMR/K8Owed.lean); head_N_is
(Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean); the opening from the head (LaidAt.opened,
Johnson/P5J/LaidOpens.lean).

Limits, the weightiest first.
  1. This file shows no value of the head h, and no state at which the premises of
    samples_opening_head hold. That blk accepts anywhere is not shown here.
  2. hH, hreach and hbk are premises, the last two at the state in front. This file does not prove
    them.
  3. "Held" is a test on the verifier's state: sample rows lie in the statement, and a seed can be
    read back off the first. It does not say that the seed reads in the field (msg_behind_send's own
    limit, Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtFifty.lean).
  4. The meaning's field pubP at border 3 is not touched here.
  5. At the full size's written lists and under IM.Open at the earlier hash OnBytes.secondHashFunction alone.
  6. The sealed closed facts that it leans on are evaluations in Lean's kernel (decide +kernel) over
    the written numbers and parameters.
  7. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtW
import Johnson.IMR.FirstUnder
import Johnson.Desc.K13.Law.AtTableFirst
import Johnson.Desc.K1.Law.OpeningZero
import Johnson.Desc.K1.Law.PlanOwn
import Johnson.Desc.K1.Law.TenantsAtThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place smpHeld)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf samplesHeld)
open VerifiableInference.Desc.Sound (linksFull moreAll)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (openAt StepG)
open VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5T (N0Full)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The samples' test at border 3, behind an accepting step of what stands at number 2**, under
the head: from the test on the book in front, at a state that is reached there, at a meaning whose
held is smpHeld. Beside the step no premise speaks of the state behind. -/
theorem samples_opening_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[2]? = some blk) {W : Type}
    (Mg : Meaning ProofFile.InstPub W)
    (hH : Mg.held = fun j t (a : ProofFile.InstPub × S) => smpHeld a.2.st a.2.book j t)
    (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s))
    (hbk : First.bookAt (P5J.At.N Zp cF) IM.placesW[2]? s = true) (hy : IM.Yes ft blk s s') :
    samplesHeld (P5J.At.N Zp cF) Mg (IM.openAt IM.linksW IM.placesW (2 + 1)) (z, s') = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, nm, X, he, -, hu⟩ := IM.first_under h.scope h.reads O
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  rw [IM.placesW_full, IM.linksW_full, ← head_N_is h]
  rw [IM.placesW_full, ← head_N_is h] at hbk
  obtain ⟨rs, cols, n, e'⟩ := hy.under hu
  have hst : StepG ProofFile.Cl Bs.G₀.first (K1.gpOf Zp) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links) Zp.first.lin.kCol (z, s) (z, s') :=
    ⟨rfl, ft, rs, cols, n, e'⟩
  obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
  have eP := K1.eG_atAll h O (K1.pin1_atAll h)
  have hS := isSend_openingZero (Cl := ProofFile.Cl) Bs.G₀.first (K1.gpOf Zp) nm X
    (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links) Zp.first.lin.kCol
  have hB := (openingZero_rec hd).2.2.2.2.1
  rw [eP] at hS hB
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  have hfit : BookFits s.book := (Sound.bookFitsB_iff _).1
    (Meaning.K2.atFirstFits_all O (fun b hb' => (K1.hOk_atAll h O b hb').1) hreach)
  have ht : s.book.trees.size = 0 :=
    hbk.1.1.trans (K1.nums_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)).1.2
  have eN : First.sampledIn h.𝔇.N (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) =
      First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) :=
    (congrArg
      (fun N => First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)))
      (K1.atAll_letters h O (K1.pin1_atAll h)).1).trans rfl
  unfold samplesHeld
  refine List.all_eq_true.2 fun u hu' => ?_
  rw [hH]
  have hu'' : u ∈ First.sampledIn h.𝔇.N (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) :=
    hu'
  rw [eN] at hu''
  obtain ⟨j, hj, hu2⟩ := seatsIn_of seatsIn_written.2 u hu''
  have hq := held_behind_send parGF hS hd hB hbk.1.2 hfit (planOwn_of own_first) j hj
  rw [ht] at hq
  show smpHeld s'.st s'.book u.1 u.2 = true
  rw [hu2]
  exact hq

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.samples_opening_head
