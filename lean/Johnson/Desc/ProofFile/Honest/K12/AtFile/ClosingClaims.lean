-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingClaims.lean: the front's named test on the open rows
(`claimsB`, Johnson/Desc/K12/Honest/Shape/TestDoor.lean) in front of the first chain's closing
proximity test, from the fold alone, under the library's head: whoever plays. A row comes into a
group through the adding, which tests it, and what the test reads of the statement only grows.

  `ClMark`, `ClStays`    every member is sampled, and every open row of every group passes the
                         mark `claimsAtB`; "if it holds in front, it holds behind"
  `sampled_of_members`   the first half, as the shape's test
  `begun_grown`, `pending_grown`   the beginning of a test and the pending row leave the shape grown
  `groundKeeps_cl`, `stKeeps_cl`   the relation meets what the library asks of one
  `start_cl`             the chain's start has it: no group
  `cl_reached`           at every state that a fold from the chain's start reaches
  `group_of_front`       the front's shape says that the group is there and no test of it has begun
  `claimsB_at_L`         so `claimsB` at the record, at a reached state behind a passing `frontFiveB`

By what. The laws `X_claims` (Johnson/Desc/Ground/Shape/Claims.lean) and `X_members`
(Johnson/Desc/Means/Entry.lean), one of each for each of the ground's functions; `notMember_of_sampled`,
`admit_unsampled`, `elsewhere_unsampled`; `open_fold_all` (Johnson/IMR/OpenFlat.lean) as
`openOrd_reached` (Johnson/AtFull/Shape/OpenRowsOrder.lean) has it; `claimsB_of_mark`
(Johnson/Desc/K12/Honest/Shape/TestClaims.lean).

Limits.
- Under the head, at the format's own hash (`OnBytes.secondHashFunction`), at the full size.
- The mark says nothing of the members' sample rows.
- The group's presence and "no test has begun" come from `frontFiveB`, which stays a premise.
- Where no group has an open row the mark holds for nothing.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.OpenFlat
import Johnson.IMR.GroupAt
import Johnson.Desc.AtSeats.StatementSeat
import Johnson.Desc.Ground.Shape.ClaimsMarks
import Johnson.Desc.K12.Honest.Shape.TestClaims
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Means OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 P12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundKeeps)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K13.Law (StKeeps)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile.Honest.Sh (testSh claimsB claimsB_of_mark frontOwesB frontLS_eq)
open P5J (AtMgA)

/-- Every member is sampled, and every open row passes the mark. -/
def ClMark (T : Statement) : Prop := SampledMembers T ∧ ∀ g, claimsAtB T g = true

/-- If it holds in front, it holds behind. -/
def ClStays (A B : Statement) : Prop := ClMark A → ClMark B

theorem sampled_of_members {T : Statement} (hm : SampledMembers T) (g : Nat) :
    membersSampledS (stSh T) g = true := by
  unfold membersSampledS
  rw [grp_get]
  cases hG : T.groups[g]? with
  | none => rfl
  | some G =>
    show (G.members.toList.all fun o => ((stSh T).oracles[o]?).any (·.sampled)) = true
    refine List.all_eq_true.2 fun o ho => ?_
    obtain ⟨x, hx, hs⟩ := hm g G hG o ho
    rw [orc_get, hx]
    exact hs

/-- The beginning of a test leaves the shape grown, at every group. -/
theorem begun_grown (T : Statement) (g g' : Nat) (G : Group) :
    Grown (stSh T) (stSh (begun T g G)) g' := by
  rw [stSh_eq (S := begun T g G) (closeLedgers_codes _ _) (closeLedgers_sh _ _)
    (g := modAt (stSh T).groups g fun G => { G with inRun := true, kinds := [] }) (by
      show ((closeLedgers T G.members.toList).groups.modify g _).toList.map grpSh = _
      rw [ProxRun.closeLedgers_groups]
      exact map_modify _ _ _ grpSh _ fun _ => rfl)]
  exact (shut_grown g' G.members.toList (stSh T)).trans (grp_grown _ g' g _ fun _ _ c => c)

/-- A change of a message's ledger leaves the shape grown. -/
theorem ledger_grown (T : Statement) (o : Nat) (l : Option Ledger) (g : Nat) :
    Grown (stSh T) (stSh { T with oracles := T.oracles.modify o fun x => { x with ledger := l } })
      g := by
  rw [stSh_eq (S := { T with oracles := T.oracles.modify o fun x => { x with ledger := l } }) rfl
    (map_modify _ _ _ orcSh (fun y => { y with ledger := l }) fun _ => rfl) rfl]
  exact orc_grown (stSh T) g o _ (fun _ => rfl) (Or.inl fun _ => rfl)

/-- **The ground's functions keep the relation.** -/
theorem groundKeeps_cl : GroundKeeps ClStays where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun d d' code maskCode n h c =>
    ⟨newGroupP_members h c.1, fun g => newGroup_claims d d' code maskCode n h g (c.2 g)⟩
  recv := fun ft d d' sent ids h c =>
    ⟨recvP_members h c.1, fun g => recv_claims ft d d' sent ids h g (c.2 g)⟩
  admit := fun d d' o rows h c =>
    ⟨admitP_members h c.1, fun g => admit_claims d d' o rows h g
      (notMember_of_sampled (sampled_of_members c.1 g) (admit_unsampled d d' o rows h)) (c.2 g)⟩
  join := fun d d' g' o kept h c =>
    ⟨joinP_members h c.1, fun g => join_claims d d' g' o kept h g (c.2 g)⟩
  addRow := fun d d' g' row h c =>
    ⟨addRowP_members h c.1, fun g => addRow_claims d d' g' row h g (c.2 g)⟩
  takeMask := fun d d' o n h c =>
    ⟨takeMaskP_members h c.1, fun g => takeMask_claims d d' o n h g (c.2 g)⟩
  closeLedger := fun d d' o h c =>
    ⟨closeLedgerP_members h c.1, fun g => closeLedger_claims d d' o h g (c.2 g)⟩
  spendAsMask := fun d d' o h c =>
    ⟨spendAsMaskP_members h c.1, fun g => spend_claims d d' o h g (c.2 g)⟩
  adopt := fun d d' sent given ids h c =>
    ⟨adoptP_members h c.1, fun g => adopt_claims d d' sent given ids h g (c.2 g)⟩
  elsewhere := fun d d' mine other theirs h c =>
    ⟨elsewhereP_members h c.1, fun g => elsewhere_claims d d' mine other theirs h g
      (notMember_of_sampled (sampled_of_members c.1 g)
        (elsewhere_unsampled d d' mine other theirs h)) (c.2 g)⟩

/-- **The relation meets all that the library asks of a relation on the statement.** -/
theorem stKeeps_cl : StKeeps ClStays where
  ground := groundKeeps_cl
  begun := fun T g G c => ⟨c.1.begun g G, fun g' => by
    refine claims_keep (begun_grown T g g' G)
      (old_rows_modify (f := fun G => { G with inRun := true, rows := #[] }) (g' := g) ?_
        fun _ _ h => by cases h) (c.2 g')
    show (begun T g G).groups = _
    unfold begun
    dsimp only
    rw [ProxRun.closeLedgers_groups]⟩
  row := fun lay im o n lin T r os' h c => by
    obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, _, -, _, l', -, -, rfl⟩ :=
      (VerifiableInference.Desc.First.Pend.pendingRowO_iff lay im o n lin T.oracles os' r).1 h
    exact ⟨c.1.onOracle im (fun x => { x with ledger := some l' }) rfl rfl fun _ h => h, fun g =>
      claims_keep (ledger_grown T im (some l') g) (old_rows rfl) (c.2 g)⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The chain's own start has no group. -/
theorem start_cl (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p : ProofFile.InstPub) :
    ClMark (ProofFile.startS Zp p).st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : (ProofFile.startS Zp p).st.groups = #[] := Meaning.K2.start_groups O.pub p
  refine ⟨fun g G hG => ?_, fun g => ?_⟩
  · rw [e] at hG
    simp at hG
  · unfold claimsAtB
    rw [e]
    simp

/-- **At every state that a fold over the first k members reaches from the chain's own start.** -/
theorem cl_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y) : ClMark y.1.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.open_fold_all (Meaning.K2.seatKeeps_by stKeeps_cl)
    (Meaning.K2.seatBack_by stKeeps_cl) O trivial (fun _ _ _ => trivial)
    (Johnson.AtFull.Shape.plans_at h) k hf (start_cl h p)

/-- The front's shape says that the group is there and that no test of it has begun. -/
theorem group_of_front {p : P12} {t : T12} (h : frontOwesB p (testSh t) = true) :
    ∃ G, t.st.groups[t.g]? = some G ∧ G.inRun = false := by
  unfold frontOwesB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, -⟩ := h
  have h2' : VerifiableInference.Desc.Ground.ok
      (ProofFile.Honest.Sh.frontLS (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask) = true := h2
  rw [frontLS_eq] at h2'
  have c0 := List.all_eq_true.1 h2' _ List.mem_cons_self
  have c1 := List.all_eq_true.1 h2' _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 c0
  refine ⟨G, hG, ?_⟩
  simpa [VerifiableInference.Desc.Ground.on, hG] using c1

/-- **The test on the open rows, at the record.** -/
theorem claimsB_at_L (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {T : T12}
    (he : enterFinish s = .ok T) {q : P12} {K : Codes}
    (h5 : frontFiveB q K (testSh T) = true) : claimsB T = true := by
  obtain ⟨-, rs, cols, hf⟩ := (reach_raw hr).fold
  have hm := (cl_reached h 354 0 p rs cols _ hf).2
  simp only [frontFiveB, Bool.and_eq_true] at h5
  obtain ⟨⟨⟨⟨⟨-, hd⟩, -⟩, -⟩, -⟩, -⟩ := h5
  unfold Sh.doorB at hd
  rw [Bool.and_eq_true, Bool.and_eq_true] at hd
  obtain ⟨G, hG, hrun⟩ := group_of_front hd.1.2
  obtain ⟨o, -, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T he
  exact claimsB_of_mark hG hrun (hm _)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.ClMark
#print axioms ProofFile.Honest.K12.sampled_of_members
#print axioms ProofFile.Honest.K12.begun_grown
#print axioms ProofFile.Honest.K12.ledger_grown
#print axioms ProofFile.Honest.K12.groundKeeps_cl
#print axioms ProofFile.Honest.K12.stKeeps_cl
#print axioms ProofFile.Honest.K12.start_cl
#print axioms ProofFile.Honest.K12.cl_reached
#print axioms ProofFile.Honest.K12.group_of_front
#print axioms ProofFile.Honest.K12.claimsB_at_L
