-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/TakenAtM3.lean: kind K13, the members' batching: THE GUARD "taken"
(`K13Guards.taken`, Debts.lean of this folder: the verifier's taking of 1 + 2 kCol mask entries off
the index masks' message returns) FROM THE THREAD's SENTENCE IN FRONT, AT THE LIBRARY's OWN
PARAMETERS (`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean), but for one inequality between
public numbers. Statements with their proofs: calls of the library's own fact on that message's
ledger. THE FULL SIZE ALONE, AT THE HASH `OnBytes.secondHashFunction` ALONE: 355 and 13 are that size's numbers.
The words thread and border are explained in the head of Honest/Thread/Thr.lean.

The road. The thread's clause on how the state was made gives: the state is reached by the
sub-protocols in front (`thr_reach_of`, Honest/Thread/ReachBack.lean). At every reached state from
border 3 to border 355 the library has: the index masks' ledger is there, is not closed, and has
just free0 entries less its count `takenAt` of that border; and that message is a member of no group
(`P1L20.room_at_reach`, `P1L20.room_out_of_groups` with `P1L20.roomOwes_paid`,
Johnson/P1L20R/RoomFold.lean, RoomKeepAll.lean). These are stated at `IM.Open`
(Johnson/IMR/SeatOpen.lean): the values that the making of the IOP as written in Lean returns at the
three public files; the hypothesis h holds one; by `IM.Open.first` its numbers are the public
part's. A ledger that is open and has n entries hands out any c ≤ n (`takeMasks_returns`,
Johnson/Desc/K13/Honest/Room.lean).
Main names:
  `taken_of_leftIs`: from the library's test `leftIsB n s`: the taking of c ≤ n entries returns.
  `m3_takenAt`: the library's count `takenAt` is 13 at 355: `takenAt_355` (PileLengthReach.lean of
    this folder: by Lean's kernel) under this file's name.
  `k13_reach_at`: under the thread at border 355 the state is reached from the first state.
  `k13_left_at`: **there the ledger is open and has just free0 - 13 entries left**, free0 :=
    `free0Of Zp.first (gpOf Zp)`: the free count of a fresh ledger at the shape of the last message
    that the first segment's opening sends.
  `k13_out_at`: **there the index masks' message is a member of no group.**
  `k13_taken_at`: **so the taking of c entries returns**, where c + 13 is at most that free0.
  `k13_guard_taken_at`: **the guard, as `K13Guards` states it.**

What is not claimed. THE INEQUALITY: it is a premise: both sides are numbers of the public files.
That the hypothesis under which the parameters are laid can be met. That the thread holds at any
run. Anything at a thread with other parameters. The other eight guards. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.Desc.ProofFile.Honest.K13.PileLengthReach
import Johnson.Desc.K13.Honest.Room
import Johnson.P1L20R.RoomKeepAll
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K1 (free0Of gpOf)
open VerifiableInference.Desc.K13.Law (dOf)
open VerifiableInference.Desc.K13.Honest (leftAtC leftAtC_iff takeMasks_returns)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach leftIsB leftIsB_iff)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

/-- From the library's test "the index masks' ledger is open and has just n entries left": the
taking of c ≤ n entries returns. -/
theorem taken_of_leftIs {s : S} {n c : Nat} (hl : leftIsB n s = true) (hc : c ≤ n) :
    ∃ t, takeMasksP (dOf s) s.out.indexMasks c = some t := by
  obtain ⟨l, h1, h2, h3⟩ := leftIsB_iff.1 hl
  have h1' : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l := h1
  refine takeMasks_returns (d := dOf s) ((leftAtC_iff _ _ _).1 ?_)
  show leftAtC s.st s.out.indexMasks c = true
  unfold leftAtC
  rw [h1']
  show (!l.closed && decide (c ≤ l.left)) = true
  rw [h2, h3]
  simpa using hc

/-- The library's count `takenAt` is 13 at 355: of the 25 written links thirteen are no attention
link and have their clearing in front of that number. It says nothing of a run. -/
theorem m3_takenAt : P1L20.takenAt 355 = 13 := takenAt_355

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- Under the thread at border 355 the state is reached by the sub-protocols in front, from the
proof file's own first state. -/
theorem k13_reach_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 355 (m.st.input.x.pub, s) := by
  have hlen : 355 ≤ cF.blocksInOrder.length := by
    cases hb : cF.blocksInOrder[355]? with
    | none =>
      have e : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[355]? = none := by
        show (cF.blocksInOrder.map (·.place))[355]? = none
        rw [List.getElem?_map, hb]
        rfl
      rw [P5J.At.places_paid h.scope h.reads h.laid, m3_place] at e
      cases e
    | some blk => exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1
  exact thr_reach_of (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
    (ProofFile.startS Zp) m.st.input.x.pub hlen (fun _ h0 => h0) hT

/-- **Under the thread at border 355 the index masks' ledger is open and has just free0 - 13 entries
left**, free0 the fresh ledger's free count by the public part's own numbers. -/
theorem k13_left_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    leftIsB (free0Of Zp.first (gpOf Zp) - 13) s = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have q := P1L20.room_at_reach h.scope h.reads O (P5J.flat_ok h.toAtMg)
    (P1L20.roomOwes_paid h.scope h.reads O)
    (k13_reach_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT) (by decide)
    (Nat.le_refl _)
  rw [m3_takenAt, O.first] at q
  exact q

/-- **There the index masks' message is a member of no group.** -/
theorem k13_out_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    P1L20.outOfGroupsB s = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P1L20.room_out_of_groups h.scope h.reads O (P5J.flat_ok h.toAtMg)
    (P1L20.roomOwes_paid h.scope h.reads O)
    (k13_reach_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT) (by decide)
    (Nat.le_refl _)

/-- **The taking of c entries returns at border 355.** hroom: the one inequality between public
numbers. -/
theorem k13_taken_at {c : Nat} (hroom : c + 13 ≤ free0Of Zp.first (gpOf Zp))
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    ∃ t, takeMasksP (dOf s) s.out.indexMasks c = some t :=
  taken_of_leftIs (k13_left_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
    (by omega)

/-- **THE GUARD "taken", as `K13Guards` states it**, at P := h.𝔇.P13: the numbers at which
SeatedAt.lean and ExchangeAtM3.lean of this folder lay the kind's structure and its sub-protocol. -/
theorem k13_guard_taken_at
    (hroom : Batt.masksOf h.𝔇.P13.lin.kCol + 13 ≤ free0Of Zp.first (gpOf Zp))
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    ∃ t, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf h.𝔇.P13.lin.kCol) = some t :=
  k13_taken_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hroom hT

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.taken_of_leftIs
#print axioms ProofFile.Honest.K13.m3_takenAt
#print axioms ProofFile.Honest.K13.k13_reach_at
#print axioms ProofFile.Honest.K13.k13_left_at
#print axioms ProofFile.Honest.K13.k13_out_at
#print axioms ProofFile.Honest.K13.k13_taken_at
#print axioms ProofFile.Honest.K13.k13_guard_taken_at
