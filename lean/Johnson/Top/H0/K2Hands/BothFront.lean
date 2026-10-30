-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/BothFront.lean: THE KEEPERS' TABLE AS ONE TERM: at the first chain of the
proof file's IOP as written in Lean (`ProofFile.onlineDescription`), every entry of the flat list in front of the
last code switch keeps both invariants on the messages' stored sample rows (SampleChain.lean's
`RowsInv Q`; AnsweredStored.lean's `AnsweredStored`). A law file; no running text imports it.
The walk: DriverKeeps.lean, FillKeeps.lean, PureKeeps.lean. The lots: LotsKeep.lean, LotsMore.lean,
LotsK9.lean.

  `thePure_keeps`  all fifteen lots of `onlineFirstChainBlockTables Z` have `LotKeeps R P`, at every P that SameRows
                   carries, from the two lots that write stored rows: K1's and K2's.
  `K1Share Q Z G`  THE ONE NAMED PREMISE: K1's lot has `LotKeeps` at both invariants: of a
                   sub-protocol inside a segment it asks `KeepsD` only where that sub-protocol
                   passes its own test on the plan. At QGoodS it is paid: LotsK1.lean.
  `both_front`     where `onlineDescription` returns F AND F PASSES ITS TESTS ON THE PLAN (F.planOk = true:
                   behind every yes of F's own decision: Johnson/Desc/PlanPasses.lean's
                   planOk_of_runEnd): F is `fileDescBy` at a chain c; at every cut
                   k ≤ (frontOf c).length every entry of `c.blocksInOrder.take k` has `KeepsInv Q` and
                   `KeepsAns`. General in Q; hk: the code switch's own decision keeps RowsInv Q
                   (at QGood: keepsGood_k2; at QGoodS: SampleChainS.lean's keepsS_k2).
                   (frontOf c).length = 14 · (the plan's segments) + 3: 353 at 25 segments.
Limits. K1's share is a premise here. That `onlineDescription` returns at any files, and that the plan at
hand has 25 segments, are not shown. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.LotsK9
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Keeps1
open Meaning.K2 (frontOf)

/-- **All fifteen lots**, from the two that write stored rows. -/
theorem thePure_keeps {R : Fmt.RoundView → Prop} {P : S → Prop} (hP : Rides P) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (h1 : LotKeeps R P (ProofFile.k1Pure Z) G) (h2 : LotKeeps R P (ProofFile.k2Pure Z) G) :
    ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotKeeps R P L G := by
  intro L hL
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    rfl | rfl
  · exact (lotRows_frames Z G).keeps hP
  · exact h1
  · exact h2
  · exact (lotRows_k3 Z G).keeps hP
  · exact (lotRows_k4 Z G).keeps hP
  · exact (lotRows_k5 Z G).keeps hP
  · exact (lotRows_k8 Z G).keeps hP
  · exact lotKeeps_k9 hP Z G
  · exact (lotRows_k11 Z G).keeps hP
  · exact free_k12 Z G
  · exact free_k13 Z G
  · exact free_k13At4 Z G
  · exact (lotRows_end Z G).keeps hP
  · exact (lotRows_k6 Z G).keeps hP
  · exact (lotRows_k7 _ G).keeps hP

/-- **The one named premise**: K1's lot keeps both invariants. -/
structure K1Share (Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) : Prop where
  good : LotKeeps OkDrawn (Inv Q) (ProofFile.k1Pure Z) G
  ans : LotKeeps (fun _ => True) Ans (ProofFile.k1Pure Z) G

/-- **The keepers' table as one term.** -/
theorem both_front {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop} {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F)
    (hpl : F.planOk = true) (hk : ∀ p : P2, KeepsInv Q (codeSwitchKind p : Block S Unit))
    (hK1 : ∀ Z G, ProofFile.pureRoad.pub o pol lay KL = .ok Z →
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G → K1Share Q Z G) :
    ∃ (Z : ProofFile.Pub) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧ (frontOf c).length = 14 * (ProofFile.subsOf Z).length + 3 ∧
      ∀ k, k ≤ (frontOf c).length →
        (∀ b ∈ c.blocksInOrder.take k, KeepsInv Q b) ∧ ∀ b ∈ c.blocksInOrder.take k, KeepsAns b := by
  obtain ⟨Z, hZ, hF⟩ := ProofFile.Law.descPure_made h
  obtain ⟨c, A, B', hE, h0, hlen, hall⟩ := pureZ_front hF
  subst hE
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := (VerifiableInference.Desc.Keeps.planOk_blocks _ hpl).1
  refine ⟨Z, c, A, B', hZ, rfl, h0, hlen, fun k hk' => ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · exact (hall OkDrawn (Inv Q) fun G hG =>
      thePure_keeps rides_inv Z G (hK1 Z G hZ hG).good (lotKeeps_k2_inv hk Z G)).2 k hk' b hb
        (hp b (List.mem_of_mem_take hb))
  · exact (hall (fun _ => True) Ans fun G hG =>
      thePure_keeps rides_ans Z G (hK1 Z G hZ hG).ans (lotKeeps_k2_ans Z G)).2 k hk' b hb
        (hp b (List.mem_of_mem_take hb))

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.thePure_keeps
#print axioms VerifiableInference.Desc.First.K2.both_front
