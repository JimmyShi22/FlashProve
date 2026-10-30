-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarksOwn.lean: CONDITIONAL: WHAT THE SILENCE OF THE TWO MARKS
AT THE OWN ROUNDS OF AN ATTENTION SEGMENT GIVES (MarksFit.lean beside this file), WITH THE FRAME's
TEST `drawsFit` AT THE MEMBER's OWN DECLARED ROUNDS: the field `rounds` of the very block that
stands at number 14 l + 4 of the first chain's flat list.

Why. MarksFit.lean's two laws take the test at `rounds` p for any parameters p of the kind whose
structure of rounds is the plan's. The space of challenges over the frame is cut by the test at the
members' own declared rounds. That the two lists of rounds are one was left open there.

How. It lay already: `k5_member` (Member.lean beside this file): under the head the block at that
number decides as the kind's own decision at the public numbers `parAt`, and the structure
`DecidesAs` has the field: its rounds are `rounds` (`parAt` …). Called. Member.lean stands over the
frame (it imports Seated.lean), as this file does.

Main names:
  `rounds_at_head`: the member's declared rounds are the kind's, at the public numbers.
  `mkLive_held_own`, `mkReads_liveV_own`: **the two laws, so.**

Limits. As MarksFit.lean's. No sentence on a measure stands here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksFit
import Johnson.Desc.ProofFile.Honest.K5.Law.Member

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (Chal Reads HeldLive Live2V)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **The member's declared rounds are the kind's, at the public numbers.** Conditional: the head;
hg; ea: the group's plan; f4: which member. -/
theorem rounds_at_head {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) : b4.rounds = Att.P.rounds (parAt Zp g a) := by
  obtain ⟨blk, a', hfl, hP, Dc⟩ := k5_member h hg
  obtain rfl : blk = b4 := Option.some.inj (hfl.symm.trans f4)
  obtain rfl : a' = a := Option.some.inj (hP.plan.symm.trans ea)
  exact Dc.rounds

/-- **WHAT THE SECOND MARK's SILENCE GIVES, UNDER THE TEST AT THE MEMBER's OWN DECLARED ROUNDS.**
Conditional: as `mkLive_held_fit`, with hf at the block's own field in the stead of p, ep and hf
there. -/
theorem mkLive_held_own {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) {att : AttOwn} (e4 : s4.here = .att att)
    (hz : OnBytes.Model.Road.Sized att.F) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4) (hf : drawsFit b4.rounds own = true)
    (hs : (mkLive (2 * g + 1) a.own).test fr own = none) : HeldLive a.own att.F.next s9 :=
  mkLive_held_fit h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 e4 hz zk hc (parAt Zp g a) rfl
    (by rw [← rounds_at_head h hg ea f4]; exact hf) hs

/-- **WHAT THE FIRST MARK's SILENCE GIVES, AT VALUES, UNDER THE TEST AT THE MEMBER's OWN DECLARED
ROUNDS.** Conditional: as `mkReads_liveV_fit`, with hf at the block's own field. -/
theorem mkReads_liveV_own {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4) (hf : drawsFit b4.rounds own = true)
    (hs : (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).test fr own = none) :
    Live2V (Att.P.parCOf a).geo a.mats s9 :=
  mkReads_liveV_fit h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 zk hc (parAt Zp g a) rfl
    (by rw [← rounds_at_head h hg ea f4]; exact hf) hs

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rounds_at_head
#print axioms ProofFile.Honest.K5.mkLive_held_own
#print axioms ProofFile.Honest.K5.mkReads_liveV_own
