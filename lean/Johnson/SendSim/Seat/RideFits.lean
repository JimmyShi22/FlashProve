-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/RideFits.lean: where the proof file's description passes its own tests on the
plan, the opening's job fits its place; the job at the request's own table fits if one public test
on the first stage of that table's proximity test accepts.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The premises are IM.Open and F.planOk = true.
  fits_at_first   The opening's job fits its place (sendFits). No further premise is left.
  fits_at_w       The job at the request's own table fits its place, if wStageB accepts.
  fits_at_lots    So every job of lotJobs and wJobs fits its place, if wStageB accepts.
  wStageB         The public test, with code: the first stage of the proximity test on the request's
                  own group has at least one row variable, no more mask row variables than row
                  variables, and a mask code long enough for the table of the fold's fresh mask
                  (foldMaskColumns, OnBytes/Iop/Fold.lean). It also accepts where that test has no
                  first stage; then no table is sent along.

How it fits. FitsAtLots.lean beside this file reduces "the job fits" at these two jobs to the test
rideFits at the one table that each sends along. Here that test is proved at the opening, and
reduced to wStageB at the request's own table; RideFitsW.lean proves that wStageB accepts where F
passes its tests on the plan. Three of its six clauses come from the way the table is announced
(first_rideOwn, Johnson/Desc/ProofFile/Honest/K1/PlaceJobLinks.lean; w_rideOwn, PlaceW.lean beside
it).
At the opening the other three come from the definition that computes a segment's group (reqGroupAt,
OnBytes/Iop/Req.lean) and from a conjunct of the opening's own test on the plan (Own.reqFits,
Johnson/Desc/Own/Req.lean). Meant as steps toward index privacy (Johnson/WholeKey/Statement.lean);
nothing in this folder derives index privacy from them. Not one of the release's goal statements.

The other names.
  rideFits_of_own   for all public numbers P: if the message at a number is announced as a fold's
                    fresh mask (rideOwn), and that fold has 1 ≤ k, h ≤ k and enough columns, then
                    rideFits holds at the table that is sent along.
  group_sizes       every group that reqGroupAt computes has h ≤ k and 1 ≤ k.
  group_zero        the first of a request's groups is reqGroupAt's value at 0.
  first_columns     the opening's test on the plan bounds the first group's columns.
  ride_at_first     rideFits at the opening's table.

Limits. That wStageB accepts is not proved here (see wStage_of_plan, RideFitsW.lean). That F.planOk
holds at given public files is not shown here (see FitsAtLots.lean). Pointwise statements: no
distribution is named. For all other limits see AtDescLots.lean.
-/
import Johnson.SendSim.Seat.FitsAtLots
import Johnson.Desc.ProofFile.Honest.K1.PlaceJobLinks

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {X Xi : Type}

/-- If the message at the number n is announced as the fresh mask of the fold Fd, and Fd has 1 ≤ k,
h ≤ k and enough columns in its mask code, the table that is sent along fits its message's shape. -/
theorem rideFits_of_own {P : K1.Par} {n : Nat} {Fd : FoldShape}
    (ho : rideOwn P (some (n, Fd)) = true) (h1 : 1 ≤ Fd.layout.k)
    (h2 : Fd.layout.h ≤ Fd.layout.k)
    (h3 : foldMaskColumns Fd.layout.k Fd.layout.h ≤ (P.codes.mask.getD Fd.maskCode default).ell) :
    ∀ k R, rideOf (some (n, Fd)) k = some R → rideFits P.codes (shapeAt P k) R = true := by
  intro k R hk
  have hk' : (if k == n then some (⟨Fd.layout.k, Fd.layout.h⟩ : Ride) else none) = some R := hk
  split at hk'
  · rename_i hkn
    obtain rfl := Option.some.inj hk'
    obtain rfl : k = n := by simpa using hkn
    have hs : P.sent[k]? = some (foldMaskNotice Fd) := by
      have ho' : (P.sent[k]? == some (foldMaskNotice Fd)) = true := ho
      exact eq_of_beq ho'
    have hshape : shapeAt P k = (foldMaskNotice Fd).shape := by
      obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hs
      unfold shapeAt Array.getD
      split
      · exact congrArg OracleNotice.shape he
      · rename_i h
        exact absurd hlt h
    rw [hshape]
    unfold foldMaskColumns at h3
    have h4 : 2 * Fd.layout.k - Fd.layout.h + 1 ≤
        (P.codes.mask.getD Fd.maskCode default).ell := by omega
    unfold rideFits
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, h2⟩, h1⟩, h4⟩
  · cases hk'

/-- Every group that reqGroupAt computes has h ≤ k and 1 ≤ k. -/
theorem group_sizes (s : ReqShape) (l : Nat) (alive : List ReqAlive) :
    (reqGroupAt s l alive).1.h ≤ (reqGroupAt s l alive).1.k ∧ 1 ≤ (reqGroupAt s l alive).1.k := by
  unfold reqGroupAt
  exact ⟨le_max_of_le_left (le_max_right _ _), le_max_right _ _⟩

/-- The first of a request's groups is reqGroupAt's value at 0. -/
theorem group_zero (s : ReqShape) : (reqGroups s).getD 0 {} = (reqGroupAt s 0 []).1 := by
  simp [reqGroups_eq, reqGroupsFrom]

/-- The opening's test on the plan bounds the columns of the first group's fresh mask. -/
theorem first_columns {q : Params.First} {samples : Nat} (h : K1.firstPlanOk q samples = true) :
    foldMaskColumns ((reqGroups q.shape).getD 0 {}).k ((reqGroups q.shape).getD 0 {}).h ≤
      (q.codes.mask.getD q.shape.maskCode default).ell := by
  unfold K1.firstPlanOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hr⟩, -⟩, -⟩ := h
  unfold Own.reqFits at hr
  dsimp only at hr
  rw [Bool.and_eq_true] at hr
  obtain ⟨hs, hm⟩ := hr
  have hne : 0 < q.shape.link.length := by
    simp only [Own.reqShapeFits, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
    cases hL : q.shape.link with
    | nil => rw [hL] at h1; cases h1
    | cons a t => exact Nat.succ_pos _
  split at hm
  · rename_i c zk hc hz
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩ := hm
    have h0 := List.all_eq_true.1 hall 0 (List.mem_range.2 hne)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
    have hz' : q.codes.mask.getD q.shape.maskCode default = zk := by
      obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hz
      unfold Array.getD
      split
      · exact he
      · rename_i h
        exact absurd hlt h
    rw [hz']
    exact h0.1
  · cases hm

/-- The table that the opening sends along fits its message's shape, where the opening's test on the
plan accepts. -/
theorem ride_at_first {q : Params.First} {gp : _root_.Desc.Plain.GPar} {samples : Nat}
    (h : K1.firstPlanOk q samples = true) :
    ∀ k R, rideOf (firstFold q) k = some R →
      rideFits (K1.firstPar q gp).codes (shapeAt (K1.firstPar q gp) k) R = true := by
  have hg := group_sizes q.shape 0 []
  rw [← group_zero] at hg
  exact rideFits_of_own (first_rideOwn q gp) hg.2 hg.1 (first_columns h)

/-- The public test on the first stage of the proximity test on the request's own group. It also
accepts where that test has no first stage; then no table is sent along. -/
def wStageB (codes : Codes) (S : LinShape) : Bool :=
  S.testOwn.head?.all fun s => decide (1 ≤ s.k) && decide (s.h ≤ s.k) &&
    decide (foldMaskColumns s.k s.h ≤ (codes.mask.getD s.maskCode default).ell)

/-- The table that is sent along with the request's own table fits its message's shape, where
wStageB accepts. -/
theorem ride_at_w {q : Params.First} {gp : _root_.Desc.Plain.GPar} {piece : Nat}
    {msg : Array OracleNotice} (hm : linMessageW q.lin = some msg)
    (h : wStageB q.codes q.lin = true) :
    ∀ k R, rideOf (wFold q.lin) k = some R →
      rideFits (K1.parW q gp piece msg).codes (shapeAt (K1.parW q gp piece msg) k) R = true := by
  have ho := w_rideOwn q gp piece msg hm
  rcases w_says q.lin msg hm with ⟨-, e⟩ | ⟨s, -, hs, e, -⟩
  · intro k R hk
    rw [e] at hk
    cases hk
  · rw [e] at ho ⊢
    unfold wStageB at h
    rw [hs] at h
    simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at h
    exact rideFits_of_own ho h.1.1 h.1.2 h.2

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Where the description's maker returns and the description passes its tests on the plan, the
opening's job fits its place.** -/
theorem fits_at_first (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (first : Nat) (D : RowDataOf Xi) :
    sendFits (openJob (X := X) Z Bs.G₀ first D).P (openJob (X := X) Z Bs.G₀ first D).ride =
      true := by
  have h : (K1.planOkOwn (K1.firstPar Bs.G₀.first (K1.gpOf Z)) &&
      K1.firstPlanOk Bs.G₀.first (K1.gpOf Z).samples) = true :=
    plan_at_own O hp (own_first Z Bs.G₀)
  rw [Bool.and_eq_true] at h
  exact sendFits_of_plan (lengths_at O hp) h.1 fun k R _ hk => ride_at_first h.2 k R hk

/-- **Where the description's maker returns and the description passes its tests on the plan, every
job of the two lots fits its place, if wStageB accepts.** -/
theorem fits_at_lots (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (hw : wStageB Z.first.codes Z.first.lin = true) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) : sendFits J.P J.ride = true := by
  rcases List.mem_append.1 hJ with h | h
  · have h' : J ∈ openJob Z Bs.G₀ (no ⟨1, some 0, 1, .K1⟩) (D Z Bs.G₀) ::
        (lotJobs no D Z Bs.G₀).tail := h
    rcases List.mem_cons.1 h' with rfl | ht
    · exact fits_at_first O hp _ _
    · exact fits_at_later O hp no D ht
  · obtain ⟨msg, hm, rfl⟩ := w_of_job no D Z Bs.G₀ h
    exact fits_at_job O hp no D hJ fun k R _ hk => ride_at_w hm hw k R hk

/-- Where the description's maker returns and the description passes its tests on the plan, the job
at the request's own table fits its place, if wStageB accepts. -/
theorem fits_at_w (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    (hw : wStageB Z.first.codes Z.first.lin = true) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ wJobs no D Z Bs.G₀) : sendFits J.P J.ride = true :=
  fits_at_lots O hp hw no D (List.mem_append_right _ hJ)

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.rideFits_of_own
#print axioms OnBytes.SendSim.Seat.ride_at_first
#print axioms OnBytes.SendSim.Seat.fits_at_first
#print axioms OnBytes.SendSim.Seat.fits_at_lots
#print axioms OnBytes.SendSim.Seat.fits_at_w
