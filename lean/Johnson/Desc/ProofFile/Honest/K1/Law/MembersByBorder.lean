-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/MembersByBorder.lean: THE SHARED "SENDING" (the kind K1): UNDER
THE LIBRARY's HEAD THE 52 JOBS OF THE TWO LOTS' LISTS, lotJobs ++ wJobs, EACH WITH THE NUMBER OF ITS
OWN PLACE IN THE FIRST CHAIN's FLAT LIST (borderNo, Johnson/Desc/ProofFile/Honest/Thread/Thr.lean),
ARE k1MembersW (LotsAtAll.lean) AT jobs_at_head's THREE WRITTEN LETTERS (JobsAtAll.lean). Eight
theorems; no definition.

WHY. Our laws on K1's 52 senders stand at k1MembersW's WRITTEN numbers: 2, K1.noL l d, 356. Whoever
lays each job beside the number of its own place, so that one term serves at every size, wants these
two lists to be one at the full size. By another house's own word its byNo unfolds to the left side
of members_by_border: that text was not seen here.

  bordersW          A CLOSED FACT ON THE WRITTEN LIST OF PLACES P5J.At.ps
                    (Johnson/P5J/LettersAt.lean), by Lean's kernel: the first entry that is the
                    opening's place stands at 2; that is link l's reads' or digits' place, at
                    K1.noL l d, at all 25 links; that is W's place, at 356
  bordersW_bites    a negative test: at a place that no entry bears the search gives 358, the
                    list's length: no member's number
  bordersW_teeth    a negative test that bites bordersW itself: each of its three kinds of test is
                    false at another number
  borderNo_written  UNDER h (the library's head: A HYPOTHESIS): borderNo over the flat list, at
                    every place p, is the search for p in the written list
  borderNo_two      UNDER h: borderNo at the opening's place is 2
  borderNo_fifty    UNDER h, at l < 25 and each d: borderNo at ⟨1, some l, IM.k1Ix l d + 1, .K1⟩
                    is K1.noL l d
  borderNo_w        UNDER h: borderNo at W's place is 356
  members_by_border UNDER h AND O: (lotJobs no Dt Zp Bs.G₀ ++ wJobs no Dd Zp Bs.G₀).map fun J =>
                    (borderNo cF.blocksInOrder J.P.place, J) = k1MembersW J₂ Jl Jw at the three written
                    letters

WHICH LAW GIVES WHAT. That the flat list's places are the written list: P5J.At.places_paid
(Johnson/P5J/PlacesPaid.lean), under the head's scope, reads and laid: borderNo_written is that law
and an induction on a list. The three numbers: bordersW's three conjuncts. That the 52 jobs are
k1MembersW's, in order: jobs_at_head (JobsAtAll.lean). Which entries k1MembersW has: mem_k1MembersW
(LotsAtAll.lean), mem_k1Members (LotsAtHead.lean). That each job's plan has its place: by unfolding.

PUBLIC TERMS ALONE: places, numbers, plans, folds and the letters no, Dt, Dd. No coin, no run, no
input.

KIN, TOLD. THE OTHER ROAD TO THE THREE NUMBERS, NOT TAKEN: where no two members share a place a
member's number is borderNo at its place: borderNo_at
(Johnson/Desc/ProofFile/Honest/Thread/Rows.lean), borderNo_of_nodup
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SitePays.lean); that the places are apart under the
head: nodupAtFull (Johnson/Desc/K11/Exchange/NodupAtFull.lean); that member b is at the written
place b: head_place (Johnson/Desc/ProofFile/Honest/Thread/HeadForm.lean). None is called here:
findIdx finds the first entry, whether or not a second follows. THE OTHER WAY ROUND, "the entry at
the number is the place": ps_two (RecordAtHead.lean), place356W (SeatsAtW.lean), m4_place
(Johnson/Desc/ProofFile/Honest/K13/ExchangeM4At.lean); onlyAt (Johnson/P1K8R/PlacesAtFlat.lean): a
test that a place stands in a list at one number and nowhere else.

Limits. THE FULL SIZE ALONE; the format's second hash function alone. THE THREE CLOSED FACTS SPEAK OF THE
WRITTEN LIST P5J.At.ps, not of any description: the head carries them to cF.blocksInOrder. AT ANOTHER SIZE
NOTHING IS SAID HERE. WHICH DATA Dt AND Dd ARE IS NOT SAID: THEY ARE LETTERS. AT THE DESCRIPTION's
OWN GROUND Bs.G₀. That any filling or Script lays such a list is not said here. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.JobsAtAll
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 On the written list of places: closed facts -/

set_option maxRecDepth 1000000 in
/-- **IN THE WRITTEN LIST OF PLACES THE FIRST ENTRY THAT IS K1's PLACE STANDS AT K1's NUMBER**: the
opening's at 2; link l's reads' and digits' at K1.noL l d, at all 25 links; W's at 356. -/
theorem bordersW : (P5J.At.ps.findIdx (· == ⟨1, some 0, 1, .K1⟩) == 2 &&
    ((List.range 25).all fun l => [false, true].all fun d =>
      P5J.At.ps.findIdx (· == ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) == K1.noL l d) &&
    P5J.At.ps.findIdx (· == ⟨1, none, 4, .K1⟩) == 356) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A NEGATIVE TEST: at a place that no entry bears the search gives the list's length, 358: no
member's number. -/
theorem bordersW_bites : (P5J.At.ps.findIdx (· == ⟨1, some 99, 1, .K1⟩), P5J.At.ps.length) =
    (358, 358) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A NEGATIVE TEST THAT BITES bordersW ITSELF: each of its three kinds of test is false at another
number: the opening's at 3; link 0's reads' at the digits' number; W's at 355. -/
theorem bordersW_teeth : (P5J.At.ps.findIdx (· == ⟨1, some 0, 1, .K1⟩) == 3,
    P5J.At.ps.findIdx (· == ⟨1, some 0, IM.k1Ix 0 false + 1, .K1⟩) == K1.noL 0 true,
    P5J.At.ps.findIdx (· == ⟨1, none, 4, .K1⟩) == 355) = (false, false, false) := by
  decide +kernel

/-! ## 2 Under the head: borderNo at K1's places -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD borderNo OVER THE FLAT LIST IS THE SEARCH IN THE WRITTEN LIST OF PLACES.** By
P5J.At.places_paid (Johnson/P5J/PlacesPaid.lean). -/
theorem borderNo_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (p : Place) :
    borderNo cF.blocksInOrder p = P5J.At.ps.findIdx (· == p) := by
  have key : ∀ l : List (Block S ProofFile.Cl),
      l.findIdx (fun y => y.place == p) = (l.map (·.place)).findIdx (· == p) := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp only [List.map_cons, List.findIdx_cons, ih]
  rw [← P5J.At.places_paid h.scope h.reads h.laid]
  exact key cF.blocksInOrder

/-- The opening's. -/
theorem borderNo_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    borderNo cF.blocksInOrder ⟨1, some 0, 1, .K1⟩ = 2 := by
  rw [borderNo_written h]
  have b := bordersW
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at b
  exact eq_of_beq b.1.1

/-- The fifty's. -/
theorem borderNo_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    (d : Bool) :
    borderNo cF.blocksInOrder ⟨1, some l, IM.k1Ix l d + 1, .K1⟩ = K1.noL l d := by
  rw [borderNo_written h]
  have b := bordersW
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at b
  have b2 := List.all_eq_true.1 (List.all_eq_true.1 b.1.2 l (List.mem_range.2 hl)) d
    (by cases d <;> simp)
  exact eq_of_beq b2

/-- W's. -/
theorem borderNo_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    borderNo cF.blocksInOrder ⟨1, none, 4, .K1⟩ = 356 := by
  rw [borderNo_written h]
  have b := bordersW
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at b
  exact eq_of_beq b.2

/-! ## 3 The list -/

variable {Xi X : Type}

/-- **THE 52 JOBS OF THE TWO LISTS, EACH WITH THE NUMBER OF ITS OWN PLACE IN THE FLAT LIST, ARE
k1MembersW AT jobs_at_head's THREE WRITTEN LETTERS.** -/
theorem members_by_border (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    (lotJobs (X := X) no Dt Zp Bs.G₀ ++ wJobs (X := X) no Dd Zp Bs.G₀).map
        (fun J => (borderNo cF.blocksInOrder J.P.place, J)) =
      k1MembersW
        (placeJob (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩)
          (firstFold Bs.G₀.first) (Dt Zp Bs.G₀))
        (fun l d => laterJobAt Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l d + 1) (if d then 2 else 1)
          (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt Zp Bs.G₀))
        (wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp Bs.G₀)) := by
  rw [jobs_at_head h O no Dt Dd, List.map_map]
  refine (List.map_congr_left ?_).trans (List.map_id _)
  intro y hy
  rcases mem_k1MembersW.1 hy with hy | rfl
  · rcases mem_k1Members.1 hy with rfl | ⟨l, hl, d, rfl⟩
    · exact Prod.ext (borderNo_two h) rfl
    · exact Prod.ext (borderNo_fifty h hl d) rfl
  · exact Prod.ext (borderNo_w h) rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.bordersW
#print axioms ProofFile.Honest.K1.bordersW_bites
#print axioms ProofFile.Honest.K1.bordersW_teeth
#print axioms ProofFile.Honest.K1.borderNo_written
#print axioms ProofFile.Honest.K1.borderNo_two
#print axioms ProofFile.Honest.K1.borderNo_fifty
#print axioms ProofFile.Honest.K1.borderNo_w
#print axioms ProofFile.Honest.K1.members_by_border
