-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/K6StateAtHead.lean: THREE FACTS ON THE VERIFIER's STATE THAT IS REACHED AT
BORDER 341 OF THE FIRST CHAIN, AT THE ONE HEAD OF A COUNTED STATEMENT (P5J.AtMg | AtMgA,
Johnson/P5J/AtMg.lean | MgAtAll.lean), at the second hash function OnBytes.secondHashFunction: three of the
fields of K6LeftMg (Johnson/Desc/Kinds/Law/K6DueSplit.lean): reach · bare · start; AND SIX MORE OF
ITS FIELDS, on the runs of the first chain's link number 24: runs3 · back3 · runs2 · back2 · runsObj
· back. STATED AND PROVED: CALLS AND TIES: no new mathematics.
The payers (Johnson/P4R/K6AtRchAt.lean · BareAt341.lean · LeavesFilledAt341.lean) stand at four
premises: the goals' scope · the files are read · the maker's value opened (IM.Open) · the test on
the list of rounds accepts: and at the family RchAt (FD Z A B c). The head holds all four: scope ·
reads · laid.opened · laid.planOk.
  fd_is          THE FIRST TIE: FD Zp (seatZ Zp Np) (secondAt Zp Np) cF is F0T OnBytes.secondHashFunction Zp Np
                 cF: rfl: both are ProofFile.fileDescBy at one list of arguments, by abbreviations alone.
  w_at_mg        THE SECOND TIE, for the field tokSmall's payer when it is ported: in the opening
                 that the head holds, the base's public parameters are the head's own At.X Zp.
  k6_reach_at_mg · k6_bare_at_mg · k6_start_at_mg       at h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF.
  **k6_reach_at_head · k6_bare_at_head · k6_start_at_head**  at h : AtMgA … x: by h.toAtMg.
Each at the bare family RchAt (F0T OnBytes.secondHashFunction Zp Np cF), at every type Str beside the state.
k6_start_… ends in OnPublicFiles.LeavesFilled a.1.2: the field's own letter in K6DueSplit.lean.
  reads_is · work_is   THE FIFTH TIE: readsOf W is the number iU3 that the payer names, where the
                 public parameters have one; workOf W is workAtW W (rfl: one text twice).
  SixAt W Lk     the six fields' texts, at the public parameters W, piece6 := 4 and the link Lk.
  six_at_mg      there is Lk with cF.links[24]? = some Lk and SixAt (At.X Zp) Lk: the payer
                 P4.six_at_seat (Johnson/P4SR/SixClosed.lean) at the head's opening, carried from
                 the base's public parameters to At.X Zp by the second tie.
  six_of_link_at_mg    so at EVERY Lk with cF.links[24]? = some Lk: for whoever has its Lk already.
  **link24_at_head · six_at_head · six_of_link_at_head**  at h : AtMgA … x.
Limits. NOT HERE: the field tokSmall: its payer stands over another copy of the structure Open.
"No mark" stands in the binders and is spent by none. The fields bare and start have the table's
promise at 341 in front besides: idle for these payers: whoever fills the fields drops it. At
OnBytes.secondHashFunction alone. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side
library AtFullSide/Top/). Nothing on soundness or on hiding.

-/
import Johnson.P4R.BareAt341
import Johnson.P4R.LeavesFilledAt341
import Johnson.P4SR.SixClosed
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Chain Link)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW readsOf workOf K6States K6Back PlanesStates
  PlanesBack)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates ObjectsBack)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (K6Reached)
open VerifiableInference.OnPublicFiles (LeavesFilled)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (seatZ secondAt)
open OnBytes.Maker (WholeD)

/-- **The first tie**: the payers' term is the head's. -/
theorem fd_is (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) :
    FD Zp (seatZ Zp Np) (secondAt Zp Np) cF = P5J.F0T OnBytes.secondHashFunction Zp Np cF := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Str : Type}

/-! ## At AtMg -/

/-- **The second tie**: the opening that the head holds, with its base's public parameters. -/
theorem w_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ Bs base, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base
      cF (seatZ Zp Np) (secondAt Zp Np) ∧ Bs.G₀.W = P5J.At.X Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨Bs, base, O, O.W⟩

/-- The field reach. -/
theorem k6_reach_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → K6Reached a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact reached_rchAt h.scope h.reads O h.laid.planOk

/-- The field bare, without the table's promise in front. -/
theorem k6_bare_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact bare_rchAt h.scope h.reads O h.laid.planOk

/-- The field start, without the table's promise in front. -/
theorem k6_start_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → LeavesFilled a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact leavesFilled_rchAt h.scope h.reads O h.laid.planOk

/-! ## Link 24 and the six -/

/-- **The fifth tie, first half**: the number of the reads' array. -/
theorem reads_is {W : OnBytes.Model.Verify.Public} {iU3 : Nat}
    (h : W.H.tl.ix.U.getD 2 none = some iU3) : readsOf W = iU3 := by
  unfold readsOf
  rw [h]
  rfl

/-- **The fifth tie, second half**: the bits of work: one text twice. -/
theorem work_is (W : OnBytes.Model.Verify.Public) : workOf W = workAtW W := rfl

/-- The six fields' texts, at piece6 := 4. -/
def SixAt (W : OnBytes.Model.Verify.Public) (Lk : Link S ProofFile.Cl) : Prop :=
  K6States W.hS (readsOf W) (parOf W.hS (workOf W)) 24 4
      (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
    K6Back W.hS (readsOf W) (parOf W.hS (workOf W)) 24 4
      (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
    PlanesStates (readsOf W) W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
    PlanesBack (readsOf W) W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
    ObjectsStates (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
    ObjectsBack (VerifiableInference.Desc.K9.statesOfLink Lk) 2

/-- The payer's conclusion, in the fields' letters, at any public parameters. -/
theorem sixAt_of {W : OnBytes.Model.Verify.Public} {Lk : Link S ProofFile.Cl} {iU3 : Nat}
    (hi : W.H.tl.ix.U.getD 2 none = some iU3)
    (a1 : K6States W.hS iU3 (parOf W.hS (workAtW W)) 24 4
      (VerifiableInference.Desc.K9.statesOfLink Lk) 3)
    (a2 : K6Back W.hS iU3 (parOf W.hS (workAtW W)) 24 4
      (VerifiableInference.Desc.K9.statesOfLink Lk) 3)
    (a3 : PlanesStates iU3 W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2)
    (a4 : PlanesBack iU3 W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2)
    (a5 : ObjectsStates (VerifiableInference.Desc.K9.statesOfLink Lk) 2)
    (a6 : ObjectsBack (VerifiableInference.Desc.K9.statesOfLink Lk) 2) : SixAt W Lk := by
  unfold SixAt
  rw [reads_is hi]
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **The six, at the link that is there.** -/
theorem six_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[24]? = some Lk ∧ SixAt (P5J.At.X Zp) Lk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, iU3, hl, hi, a1, a2, a3, a4, a5, a6⟩ := six_at_seat h.scope h.reads O
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  exact ⟨Lk, hl, eW ▸ sixAt_of hi a1 a2 a3 a4 a5 a6⟩

/-- Link number 24 of the first chain is there. -/
theorem link24_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[24]? = some Lk := by
  obtain ⟨Lk, hl, _⟩ := six_at_mg h
  exact ⟨Lk, hl⟩

/-- So at every Lk that is link number 24. -/
theorem six_of_link_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Lk : Link S ProofFile.Cl}
    (hl : cF.links[24]? = some Lk) : SixAt (P5J.At.X Zp) Lk := by
  obtain ⟨Lk', hl', s⟩ := six_at_mg h
  obtain rfl : Lk' = Lk := Option.some.inj (hl'.symm.trans hl)
  exact s

/-! ## At AtMgA -/

/-- **The field reach, at the head.** -/
theorem k6_reach_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → K6Reached a.1.2 := k6_reach_at_mg h.toAtMg

/-- **The field bare, at the head.** -/
theorem k6_bare_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[] :=
  k6_bare_at_mg h.toAtMg

/-- **The field start, at the head.** -/
theorem k6_start_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → LeavesFilled a.1.2 := k6_start_at_mg h.toAtMg

/-- **Link number 24 is there, at the head.** -/
theorem link24_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[24]? = some Lk := link24_at_mg h.toAtMg

/-- **The six, at the head.** -/
theorem six_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Lk : Link S ProofFile.Cl, cF.links[24]? = some Lk ∧ SixAt (P5J.At.X Zp) Lk := six_at_mg h.toAtMg

/-- **The six at every Lk that is link number 24, at the head.** -/
theorem six_of_link_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Lk : Link S ProofFile.Cl}
    (hl : cF.links[24]? = some Lk) : SixAt (P5J.At.X Zp) Lk := six_of_link_at_mg h.toAtMg hl

end P4

#print axioms P4.fd_is
#print axioms P4.w_at_mg
#print axioms P4.k6_reach_at_head
#print axioms P4.k6_bare_at_head
#print axioms P4.k6_start_at_head
#print axioms P4.link24_at_head
#print axioms P4.six_at_head
#print axioms P4.six_of_link_at_head
