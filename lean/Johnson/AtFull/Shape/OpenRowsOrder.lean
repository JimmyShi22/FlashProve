-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/OpenRowsOrder.lean: UNDER THE HEAD `P5J.AtMgA`: AT EVERY STATE THAT THE PROOF
FILE's OWN FIRST CHAIN REACHES FROM ITS OWN START, WHOEVER PLAYS, EVERY TENSOR OF EVERY OPEN ROW OF
EVERY GROUP OF THE STATEMENT PASSES THE LIBRARY's TEST `Tensor.ok` (at most 63 variables; the slice
lies inside its vector; each written-out variable is there, has the pair (1, 1) and is named once).
A joining of laws; nothing is evaluated.

Why it holds. A row comes into a group by one function alone, the ground's `addRowP`
(Johnson/Desc/First/Base/Ground.lean), and its own test `rowL` asks just this of every term and of
every tensor of every form (`VerifiableInference.Desc.K9L.rowL_clauses`,
Johnson/Desc/First/Batch/Law/DoorTests.lean, has the test as sentences). Of the ground's other
functions one adds a group without a row, one turns a group's members, the beginning of a proximity
test empties a group's rows, and the rest turn the messages alone.

By what. "If it holds in front, it holds behind" is a relation on the statement. The library asks
fourteen small things of such a relation (`StKeeps`, Johnson/Desc/K13/Law/StatementCalls.lean: that
it is reflexive and transitive, the ground's ten functions, the beginning of a test, the pending
row) and carries it to every maker of the proof file's seat (`Meaning.K2.seatKeeps_by`,
`seatBack_by`, Johnson/Desc/AtSeats/StatementSeat.lean) and from there to every member of the
chain's flat list (`Meaning.K2.open_flat`, `open_fold_all`, Johnson/IMR/OpenFlat.lean). Under the
head every member passes its test on the plan (`plans_at`, PlansAtHead.lean), and the start has no
group (`Meaning.K2.s0_first`, in StatementSeat.lean too).

Main names.
* `RowOrd r`: every tensor among the row's terms and in its forms passes `Tensor.ok`. `OpenOrd T`:
  every open row of every group of T is so. `OrdStays A B`: OpenOrd A gives OpenOrd B.
* `openOrd_none`, `ordStays_same`, `ordStays_modify`: three tools.
* `rowOrd_of_rowL`: a yes of the ground's test of a new open row gives RowOrd.
* `groundKeeps_ord`, `stKeeps_ord`: the fourteen.
* `openOrd_kept_at`: under the head, at every n: every yes of the step of the member number n keeps
  OpenOrd.
* `start_openOrd`: the chain's own start has it, at every instance.
* `openOrd_reached`: under the head, at every k, ft, instance, rounds and columns: where the fold
  over the first k members returns from the chain's own start, the state that it returns has it.

What it is for. One of the members' named tests on values asks that the tensors of rows be in order:
the closings' test on the rows that go into the batching (the group's open rows and its members'
stored sample rows). This file pays the part of it that reads the open rows. The code switch's test
on the pairs at the written-out variables reads no open row: nothing of it is paid here.

Limits. THE OPEN ROWS ALONE. NOT the messages' stored sample rows: the function that admits them
tests nothing of their tensors. NOT the rows that a frame carries from a closing to the next code
switch: they do not lie in the statement. So no named test on values is paid whole here. WHERE NO
GROUP HAS AN OPEN ROW (at the start; behind the beginning of each proximity test) THE SENTENCE HOLDS
FOR NOTHING: that any reached state has an open row is not shown here. Whoever holds a reached state
in another form owes the fold. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.OpenFlat
import Johnson.Desc.AtSeats.StatementSeat
import Johnson.Desc.First.Batch.Law.DoorTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks step_iff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundKeeps)
open VerifiableInference.Desc.K13.Law (StKeeps)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-! ## 1 The sentence, and the relation -/

/-- Every tensor among the row's terms and in its forms passes the library's test Tensor.ok. -/
def RowOrd (r : OnBytes.Row) : Prop :=
  (∀ t ∈ r.terms.toList, t.v.ok = true) ∧ ∀ f ∈ r.forms.toList, ∀ v ∈ f.c.tensors, v.ok = true

/-- **Every open row of every group is so.** -/
def OpenOrd (T : Statement) : Prop :=
  ∀ (g : Nat) (G : Group), T.groups[g]? = some G → ∀ r ∈ G.rows.toList, RowOrd r

/-- If it holds in front, it holds behind. -/
def OrdStays (A B : Statement) : Prop := OpenOrd A → OpenOrd B

/-- A statement without a group. -/
theorem openOrd_none {T : Statement} (h : T.groups = #[]) : OpenOrd T := by
  intro g G hG
  rw [h] at hG
  simp at hG

/-- An effect that leaves the groups. -/
theorem ordStays_same {A B : Statement} (h : B.groups = A.groups) : OrdStays A B := by
  intro hA g G hG
  rw [h] at hG
  exact hA g G hG

/-- An effect on one group. -/
theorem ordStays_modify {A B : Statement} (g : Nat) (f : Group → Group)
    (h : B.groups = A.groups.modify g f)
    (hf : ∀ G, A.groups[g]? = some G → (∀ r ∈ G.rows.toList, RowOrd r) →
      ∀ r ∈ (f G).rows.toList, RowOrd r) : OrdStays A B := by
  intro hA g' G' hG'
  rw [h, Array.getElem?_modify] at hG'
  by_cases c : g = g'
  · rw [if_pos c] at hG'
    obtain ⟨G, h1, rfl⟩ := Option.map_eq_some_iff.1 hG'
    subst c
    exact hf G h1 (hA g G h1)
  · rw [if_neg c] at hG'
    exact hA g' G' hG'

/-- **What the ground's own test of a new open row has asked of its tensors.** -/
theorem rowOrd_of_rowL {T : Statement} {g : Nat} {row : OnBytes.Row}
    (h : VerifiableInference.Desc.Ground.ok (VerifiableInference.Desc.Ground.rowL T g row) = true) :
    RowOrd row := by
  obtain ⟨G, -, C⟩ := VerifiableInference.Desc.K9L.rowL_clauses T g row h
  refine ⟨fun t ht => (C.terms t (Array.mem_toList_iff.1 ht)).1, fun f hf v hv => ?_⟩
  have h2 := (C.forms f (Array.mem_toList_iff.1 hf)).2
  unfold Form.fits at h2
  rw [Bool.and_eq_true, List.all_eq_true] at h2
  have h3 := h2.1 v hv
  rw [Bool.and_eq_true] at h3
  exact h3.2

/-! ## 2 The ground's ten functions, the beginning of a test, the pending row -/

/-- The ground's ten functions keep it: each arm opens its function's own text. -/
theorem groundKeeps_ord : GroundKeeps OrdStays where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := by
    intro L d d' code maskCode n h
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro hA g G hG
      have hG' : (d.st.groups.push { code := code, maskCode := maskCode })[g]? = some G := hG
      rw [Array.getElem?_push] at hG'
      split at hG'
      · obtain rfl := Option.some.inj hG'
        intro r hr
        cases hr
      · exact hA g G hG'
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact ordStays_same rfl
    · cases h
  admit := by
    intro L d d' o rows h
    unfold VerifiableInference.Desc.Ground.admitP at h
    split at h
    · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨pl, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      exact ordStays_same rfl
    · cases h
  join := by
    intro L d d' g o kept h
    unfold VerifiableInference.Desc.Ground.joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ordStays_modify g (fun G' => { G' with
        members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
        kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }) rfl
        fun _ _ hr => hr
    · cases h
  addRow := by
    intro L d d' g row h
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · rename_i hok
      obtain rfl := Option.some.inj h
      refine ordStays_modify g (fun G => { G with rows := G.rows.push row }) rfl
        fun G _ hr r hm => ?_
      have hm' : r ∈ (G.rows.push row).toList := hm
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | rfl
      · exact hr r hm'
      · exact rowOrd_of_rowL hok
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact ordStays_same rfl
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ordStays_same rfl
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.spendAsMaskP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ordStays_same rfl
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold VerifiableInference.Desc.Ground.adoptP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact ordStays_same rfl
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold VerifiableInference.Desc.Ground.elsewhereP at h
    split at h
    · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ordStays_same rfl
    · cases h

/-- **The relation meets all that the library asks of a relation on the statement.** -/
theorem stKeeps_ord : StKeeps OrdStays where
  ground := groundKeeps_ord
  begun := by
    intro T g G
    refine ordStays_modify g (fun G' => { G' with inRun := true, rows := #[] }) ?_
      fun _ _ _ r hr => ?_
    · have e : (begun T g G).groups = (closeLedgers T G.members.toList).groups.modify g
          (fun G' => { G' with inRun := true, rows := #[] }) := rfl
      rw [e, OnBytes.Means.closeLedgers_groups]
    · cases hr
  row := fun _ _ _ _ _ _ _ _ _ => ordStays_same rfl

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **EVERY MEMBER KEEPS IT.** -/
theorem openOrd_kept_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      OpenOrd s.st → OpenOrd s'.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro blk hb ft s rs cols s' k hs
  have hm := List.mem_of_getElem? hb
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols k).1 hs
  exact Meaning.K2.open_flat (Meaning.K2.seatKeeps_by stKeeps_ord)
    (Meaning.K2.seatBack_by stKeeps_ord) O trivial (fun _ _ _ => trivial) blk hm
    (plans_at h blk hm) s _ _ s' hd

/-- The chain's own start has no group. -/
theorem start_openOrd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p : ProofFile.InstPub) :
    OpenOrd (ProofFile.startS Zp p).st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine openOrd_none ?_
  unfold ProofFile.startS
  dsimp only
  split
  · show Zp.s₀.st.groups = #[]
    rw [Meaning.K2.s0_first O.pub]
    rfl
  · rfl

/-- **AT EVERY STATE THAT A FOLD OVER THE FIRST k MEMBERS REACHES FROM THE CHAIN's OWN START.** -/
theorem openOrd_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y) : OpenOrd y.1.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.open_fold_all (Meaning.K2.seatKeeps_by stKeeps_ord)
    (Meaning.K2.seatBack_by stKeeps_ord) O trivial (fun _ _ _ => trivial) (plans_at h) k hf
    (start_openOrd h p)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.openOrd_none
#print axioms Johnson.AtFull.Shape.ordStays_same
#print axioms Johnson.AtFull.Shape.ordStays_modify
#print axioms Johnson.AtFull.Shape.rowOrd_of_rowL
#print axioms Johnson.AtFull.Shape.groundKeeps_ord
#print axioms Johnson.AtFull.Shape.stKeeps_ord
#print axioms Johnson.AtFull.Shape.openOrd_kept_at
#print axioms Johnson.AtFull.Shape.start_openOrd
#print axioms Johnson.AtFull.Shape.openOrd_reached
