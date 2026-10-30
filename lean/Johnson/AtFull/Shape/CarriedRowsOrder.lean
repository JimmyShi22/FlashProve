-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/CarriedRowsOrder.lean: UNDER THE HEAD `P5J.AtMgA`: AT EVERY STATE THAT THE
PROOF FILE's OWN FIRST CHAIN REACHES FROM ITS OWN START, WHOEVER PLAYS, IN EVERY COPY OF THE LINKS'
FRAME THAT THE STATE HOLDS, THE ROWS THAT THE FRAME CARRIES FROM A CLOSING TO THE NEXT CODE SWITCH
ARE IN ORDER (`OrderForm`, OnBytes/Slice/BlkProxOrder.lean: in each tensor of the form on the main
row and of each separate form every written-out variable is named once and has the pair (1, 1)). A
joining of laws; nothing is evaluated.

Why it holds. One maker alone lays new carried rows: a segment's closing. In front of the fold it
tests the batched row's sizes ("K10.rowfits": `Own.foldRowFits`, Johnson/Desc/Own/Fold.lean, which
is the program's `foldRowOk`: Johnson/Desc/Own/FoldAgree.lean), and that test asks `Form.fits` of
the form on the main row and of each separate form. What the fold returns of a row that has passed
it is in order (`order_foldOutput`, BlkProxOrder.lean; the separate forms are scaled alone). So the
new rows are in order off the closing's own yes: nothing is asked of the state in front. Every other
maker hands each copy behind the carried rows of a copy in front.

By what. The library has that last sentence as a relation, general in a property that reads a
frame's carried rows alone: `FR`, with `Carr`, `EachF` and `framesIn` (Johnson/IMR/FrAll.lean,
Johnson/IMR/FrK2.lean, Johnson/Goal/Meaning/RecAll.lean), at every maker of the proof file's seat
but the closing (and but the proximity test's finish behind the last link, which has no such law by
name and is opened here as in RowsSent.lean). Johnson/IMR/RowsSent.lean lays it into the two
structures of Johnson/IMR/SeatKeeps.lean at another property (the carried rows name messages that
are sent); this file goes beside it, proof for proof. From there to every member and every fold:
`open_flat`, `open_fold_all` (Johnson/IMR/OpenFlat.lean) with `plans_at` (PlansAtHead.lean).

Main names.
* `CarrOrd R`: R's form on the main row and each of its separate forms are in order. `OrdF f`:
  CarrOrd f.rows. `CarrStays s t`: OrdF at every copy in s gives OrdF at every copy in t.
* `carr_ord`, `carrStays_up`, `whole_carr`, `fn_carr`: from the library's relation to this one.
* `closing_order`, `closeFrame_order`, `closing_carr`, `closeOf_carr`: the closing.
* `batch_carr`; `seatKeeps_carr`, `seatBack_carr`: all makers.
* `carrOrd_none`, `start_ord`: the first state's carried rows hold nothing.
* `carried_kept_at`: under the head, at every n: every yes of the step of the member number n keeps
  it.
* `carried_order_reached`: under the head, at every k, ft, instance, rounds and columns: where the
  fold over the first k members returns from the chain's own start: CarrOrd f.rows at every copy f
  of the frame in the state that it returns.

What it is for. The code switch's test on values asks, in its first two clauses, the pair (1, 1) at
each written-out variable of the carried form and of the kept forms.

Limits. "In order" is less than `Tensor.ok`: nothing on the number of variables or on the slice. In
front of the first closing the carried rows hold nothing, and the sentence holds for nothing.
Nothing on the vectors on the mask rows. Whoever holds a reached state in another form owes the
fold. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.RowsSent
import Johnson.Desc.AtSeats.StatementSeat
import Johnson.Desc.Own.FoldAgree
import OnBytes.Slice.BlkProxOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Slice.ProxRun (OrderForm orderForm_scale order_foldOutput fits_tensors)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9 (atS batch adds drawAlone)
open Meaning.K2
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile (Cl)

/-! ## 1 The sentence -/

/-- The carried rows' form on the main row and each of their separate forms are in order. -/
def CarrOrd (R : SingleRows) : Prop := OrderForm R.c ∧ ∀ f ∈ R.kept.toList, OrderForm f.c

/-- The frame's carried rows are so. -/
def OrdF (f : ReqFrame) : Prop := CarrOrd f.rows

/-- It reads the carried rows alone. -/
theorem carr_ord : Carr OrdF := fun f f' h e => by
  unfold OrdF
  rw [e]
  exact h

/-- **THE RELATION**: if it holds at every copy of the frame in front, it holds at every copy
behind. -/
def CarrStays (s t : S) : Prop := EachF OrdF s → EachF OrdF t

/-- The library's relation gives this one. -/
theorem carrStays_up {s t : S} (h : FR s t) : CarrStays s t := h _ carr_ord

/-- So of a block's decision and runs. -/
theorem whole_carr {C : Type} {b : Block S C} (W : Whole FR b) : Whole CarrStays b :=
  whole_mono (fun _ _ h => carrStays_up h) W

/-- So of a quiet step. -/
theorem fn_carr {f : S → Except String S} (h : Fn FR f) : Fn CarrStays f :=
  fun s t k => carrStays_up (h s t k)

/-! ## 2 The closing: by its own test -/

/-- **THE ROWS THAT A CLOSING RETURNS ARE IN ORDER, OFF THE CLOSING's OWN YES.** -/
theorem closing_order {P : Close.Plan} {T T' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : Close.closing P T g mask rs = .ok (out, T')) :
    CarrOrd out := by
  obtain ⟨eB, es, rB, rs', -, -, m, -, row, L, S1, -, -, hF⟩ :=
    (Close.closing_iff P T g mask rs out T').1 h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, d2, -, sum, eps, -, hrow, gamma, claim, -, rfl, -⟩ := hF
  rw [← Own.foldRowFits_agrees] at hrow
  refine ⟨order_foldOutput _ _ _ _ _ _ _ hrow, fun k hk => ?_⟩
  rw [foldOutput_kept, Array.toList_map] at hk
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hk
  unfold foldRowOk at hrow
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hrow
  exact orderForm_scale (fun v hv =>
    (fits_tensors f.c _ (hrow.2 f (Array.mem_toList_iff.1 hf)).2 v hv).2) _

/-- At a yes of the frame's closing of a link. -/
theorem closeFrame_order {owed : Option Nat} {f : ReqFrame} {T : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : Close.closeFrame owed f T es rs = .ok x) :
    OrdF x.1 := by
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (Close.closeFrame_iff owed f T es rs x.1 x.2).1 h
  unfold OrdF
  rw [e]
  exact closing_order ((Close.closing_iff _ _ _ _ _ _ _).2 hc)

/-- The closing's block lays the new rows into the copy in use. -/
theorem closing_carr (P : Close.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K9.closing (Cl := Unit) P).decide s rs gs = .ok s') (R : EachF OrdF s) :
    EachF OrdF s' := by
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact ef_putLive (c := { s.live with frame := x.1 }) R (closeFrame_order hx)

/-- The three blocks of a closing. -/
theorem closeOf_carr (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Unit) p P, Whole CarrStays b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact whole_carr (oneEquation_fr p)
  · exact ⟨fun s rs gs s' h R => closing_carr P h R, (fun _ hc => nomatch hc),
      (fun _ hc => nomatch hc)⟩
  · exact whole_carr (shut_fr p _)

/-! ## 3 The other makers -/

/-- The batching, at every gatherer that keeps it. -/
theorem batch_carr (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl CarrStays claims) : Whole CarrStays (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have R1 : EachF OrdF t₁ := drawAlone_fr p s rs gs t₁ h1 _ carr_ord R
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, hx, h⟩ := bindE h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨F, _, h⟩ := bindE h
  cases h
  obtain ⟨g1, g2⟩ := atS_get (there_some hq)
  have R2 : EachF OrdF x.2 := hcl t₁ x hx R1
  exact atS_set_fr R2 (link_fr R2 g1)

/-- **Every maker of the proof file's seat keeps it.** -/
theorem seatKeeps_carr : SeatKeeps CarrStays where
  refl := fun _ h => h
  trans := fun _ _ _ h k x => k (h x)
  frames := fun _ h f hf =>
    ⟨fn_carr (framesOf_fr h f hf).1, fn_carr (framesOf_fr h f hf).2.1,
      fn_carr (framesOf_fr h f hf).2.2⟩
  k1First := fun q gp _ => whole_carr (firstAtS_fr q gp)
  k1Later := fun q gp l p m a _ => whole_carr (laterAt_fr q gp l p m a)
  reads := fun h => whole_carr (whole_fr (readsQuietAt_quiet h))
  k3 := fun c r X cs' sh' a _ h => whole_carr (whole_fr (theStated_quiet c r X cs' sh' a h))
  k4 := fun p => whole_carr (whole_fr (blockAtC_quiet p))
  k5 := fun W l g bf _ h => whole_carr (whole_fr (k5AtN_quiet W l g bf h))
  k6 := fun h => whole_carr (whole_fr (seatedClaims_quiet h))
  k7 := fun W l => whole_carr (whole_fr (k7Of_quiet W l))
  k8 := fun p => whole_carr (whole_fr (k8Whole_quiet p))
  k11 := fun P => whole_carr (whole_fr (headMerge11_quiet P))
  closeOf := closeOf_carr
  batch := fun p _ hf => batch_carr p hf
  k2 := fun p _ => whole_carr (K2.k2_rf p)
  front := fun tl => fn_carr (K2.headFrontQ_rf tl)
  openQ := fun P _ => fn_carr (K2.headOpenQ_rf P)
  finFront := fn_carr K2.finishFrontQ_rf
  finBehind := fn_carr K2.finishBehindQ_rf

/-- The makers behind the last link. -/
theorem seatBack_carr : SeatBack CarrStays where
  k12 := fun m _ => ⟨fun s rs gs s' h R => by
      obtain ⟨o, t', -, -, -, -, rfl⟩ := K12.Seat.atFinish_ok _ s s' rs gs h
      exact ef_same R fun _ hm => hm,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => whole_carr ⟨atM3_fr p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p P _ => whole_carr
    ⟨atM4_fr p _ (sendAtS_fr P).1, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## 4 The start, and the tops -/

/-- Rows without a tensor and without a separate form. -/
theorem carrOrd_none {R : SingleRows} (h1 : R.c.tensors = []) (h2 : R.kept = #[]) : CarrOrd R := by
  refine ⟨fun v hv => ?_, fun f hf => ?_⟩
  · rw [h1] at hv
    cases hv
  · rw [h2] at hf
    cases hf

/-- **The first state's carried rows hold nothing.** -/
theorem start_ord {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    EachF OrdF (ProofFile.startS Z p) := by
  have e : EachF OrdF Z.s₀ := by
    rw [s0_first hZ]
    intro f hf
    have e : f = (S.firstRecord Z.first.codes Z.first.shape Z.first.layout).check.frame := by
      simpa [framesIn, S.firstRecord] using hf
    rw [e]
    exact carrOrd_none rfl rfl
  unfold ProofFile.startS
  dsimp only
  split
  · exact ef_same e fun _ h => h
  · intro f hf
    have e' : f = S.blank.check.frame := by simpa [framesIn, S.blank, S.start] using hf
    rw [e']
    exact carrOrd_none rfl rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **EVERY MEMBER KEEPS IT.** -/
theorem carried_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      EachF OrdF s → EachF OrdF s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro blk hb ft s rs cols s' k hs
  have hm := List.mem_of_getElem? hb
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols k).1 hs
  exact open_flat seatKeeps_carr seatBack_carr O trivial (fun _ _ _ => trivial) blk hm
    (plans_at h blk hm) s _ _ s' hd

/-- **AT EVERY STATE THAT A FOLD OVER THE FIRST k MEMBERS REACHES FROM THE CHAIN's OWN START: AT
EVERY COPY OF THE FRAME.** -/
theorem carried_order_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (y : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y) :
    ∀ f ∈ framesIn y.1, CarrOrd f.rows := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact open_fold_all seatKeeps_carr seatBack_carr O trivial (fun _ _ _ => trivial) (plans_at h) k
    hf (start_ord O.pub p)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.carr_ord
#print axioms Johnson.AtFull.Shape.carrStays_up
#print axioms Johnson.AtFull.Shape.whole_carr
#print axioms Johnson.AtFull.Shape.fn_carr
#print axioms Johnson.AtFull.Shape.closing_order
#print axioms Johnson.AtFull.Shape.closeFrame_order
#print axioms Johnson.AtFull.Shape.closing_carr
#print axioms Johnson.AtFull.Shape.closeOf_carr
#print axioms Johnson.AtFull.Shape.batch_carr
#print axioms Johnson.AtFull.Shape.seatKeeps_carr
#print axioms Johnson.AtFull.Shape.seatBack_carr
#print axioms Johnson.AtFull.Shape.carrOrd_none
#print axioms Johnson.AtFull.Shape.start_ord
#print axioms Johnson.AtFull.Shape.carried_kept_at
#print axioms Johnson.AtFull.Shape.carried_order_reached
