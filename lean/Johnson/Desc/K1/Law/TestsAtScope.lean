-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TestsAtScope.lean: the equations on letters that the ten statements of
TestsAtCounts.lean (this folder) ask, IN THE GOALS' SCOPE, at the terms that are meant: the core of
the table's numbers and the list of seats off the public part's own list of rounds
(`P5T.numbersOf (P5T.planSeats Z Z.D.1)`, `(P5T.planSeats Z Z.D.1).map (j, t)`: the text of
the closed letters N and seats), and the proximity test's data off the public part's own
list of sendings (`dkOf Z`, PlanThree.lean, this folder). Statements with their proofs; nothing is
evaluated; each equation is another file's, gathered.

  `dk_written`       where the proof file's lists of sendings are the written ones, `dkOf Z` holds
                     the written layout and shapes
  `letters_in_scope`   **five equations**: the core is `N0Full` · the list of seats is `seatsFull` ·
                     `dkOf Z`'s two lists · the first chain's codes and request's shape, in the
                     ground that K1's sub-protocols read, are the written ones (the law's own
                     premises hc and hs)
PREMISES: the scope · the opened IOP as written in Lean, AT THE PUBLIC FILES' OWN LAYOUT FILE
(`P.lay`: in the law on K1 that file is a free letter) · hy: the verifier's test `madePinnedAt`
accepts · hl: the value is laid (`LPFD.Full.proofDataAndDecisionOfPublicFiles`). Can they be met? Only where the public part
is made, the test accepts and the value is laid: the reference run's to show; no theorem.

What is not claimed. `CountsAre (toldOf c.blocksInOrder)`: TestsAtCounts.lean's premise hC stays. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.TestsAtCounts
import Johnson.P5T.PlanSeatsTie
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Desc.Ok.PlanWritten.SendsTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes Johnson.G
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (seatsFull LFull MFull)
open VerifiableInference.Desc.K12.Door (K12Data laidOfChain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open P5T (N0Full)
open ProofFile (Cl)
open IM (Open)

/-- Where the lists of sendings are the written ones, the data that are meant hold the written
layout and shapes. -/
theorem dk_written {Z : ProofFile.Pub} (hs : Z.made.proof = proofSendsFull) {dk : K12Data}
    (h : dkOf Z = some dk) : dk.L = LFull ∧ dk.M = MFull := by
  unfold dkOf dkOfChain at h
  rw [hs] at h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 h
  have hc : proofSendsFull.1.codes = codesFull2 :=
    (List.cons.inj (congrArg Prod.snd PlanWritten.written_codes)).1
  have e : laidOfChain proofSendsFull.1 = some LFull := by
    rw [K12.Door.laidOfChain_is, hc]
    exact K13.Law.laid_written
  rw [e] at hL
  obtain rfl := Option.some.inj hL
  exact ⟨rfl, K13.Law.msgs_written⟩

/-- **The letters, in scope.** -/
theorem letters_in_scope {o : ProofFile.SecondHashFunctionArgument} {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    (hS : VerifierAndGoals.InScope P = true) (O : Open o P.pol P.lay P.KL F Z Bs base₀ c A B)
    (hy : PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o P.pol P.lay P.KL = .ok (D, r)) :
    P5T.numbersOf (P5T.planSeats Z Z.D.1) = N0Full ∧
      ((P5T.planSeats Z Z.D.1).map fun p => (p.j, p.t)) = seatsFull ∧
      (∀ dk, dkOf Z = some dk → dk.L = LFull ∧ dk.M = MFull) ∧
      Bs.G₀.first.codes = codesFull2 ∧ Bs.G₀.first.shape = shapeFull := by
  have h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z := O.pub
  obtain ⟨e1, _, e3⟩ := P5T.seats_in_scope hS h hy hl
  have hF := K13.Law.likeFull_in_scope hS h hy
  refine ⟨e3, by rw [e1]; rfl,
    fun dk hd => dk_written (PlanWritten.Joined.sends_in_scope hS h hy) hd, ?_, ?_⟩
  · rw [O.first]
    exact hF.codes
  · rw [O.first, hF.shape]
    exact PlanWritten.request_shape_written

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.dk_written
#print axioms VerifiableInference.Desc.K1.letters_in_scope
