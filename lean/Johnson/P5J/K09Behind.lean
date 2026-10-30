-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Behind.lean: THE TIE AT THE 25 PLACES OF THE FRAME's SUB-PROTOCOL BEHIND A BATCHING
(which bear the kind «frame»), FROM THE BATCHING KIND's ONE NAMED CONDITION AT THE CLOSED CONSTANT
(`AtMgA.K9Cond`, K09Kind.lean), AT THE PLACES' NUMBERS WRITTEN OUT: 14 l + 10; the head's 348: the
form in which the frame's files ask it. An evaluation and one theorem.

What is said.
  `behindNum_links`: the kernel's yes: at each of the 25 links the number behind the batching's is
    14 l + (if l = 24 then 9 else 7) + 3, and two more places stand behind the batching's.
    `k09_behindTies`: **from `h.K9Cond 𝔏`: at every l < 25, at the piece at that number: `TiedAtR`
    there**, at the closed constant's meaning, at the fence that the join spends, with the seated
    extractor laid over the piece.

Limits. BOOK-KEEPING: a call of `k09_behind_at` with the number written out. THE CONDITION IS THE
DEBT. Nothing on soundness.

-/
import Johnson.P5J.K09Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start flatPlacesOf)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (batchAt)

set_option maxRecDepth 1000000 in
/-- **THE NUMBERS, BY THE KERNEL.** -/
theorem behindNum_links : ((List.range 25).all fun l =>
    decide (batchAt fullLinks (flatPlacesOf fullLinks true) l + 1 =
      14 * l + (if l = 24 then 9 else 7) + 3) &&
    decide (batchAt fullLinks (flatPlacesOf fullLinks true) l + 1 + 1 <
      (flatPlacesOf fullLinks true).length)) = true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE 25 PLACES BEHIND THE BATCHINGS: TIED, FROM THE BATCHING KIND's OWN CONDITION.** -/
theorem k09_behindTies (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (C : h.K9Cond 𝔏) :
    ∀ l, l < 25 → ∀ q,
      (h.toAtMg.row 𝔏)[14 * l + (if l = 24 then 9 else 7) + 3]? = some q →
      TiedAtR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
        (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch
        (14 * l + (if l = 24 then 9 else 7) + 3)
        (q.withMap (h.toAtMg.ex 𝔏 (14 * l + (if l = 24 then 9 else 7) + 3))) := by
  intro l hl q hq
  have e := List.all_eq_true.1 behindNum_links l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at e
  have e1 : batchAt fullLinks At.ps l + 1 = 14 * l + (if l = 24 then 9 else 7) + 3 := e.1
  rw [← e1] at hq ⊢
  exact k09_behind_at h 𝔏 C l hl e.2 q hq

end P5J

#print axioms P5J.behindNum_links
#print axioms P5J.k09_behindTies
