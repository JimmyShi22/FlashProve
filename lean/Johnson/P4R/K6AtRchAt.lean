-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/K6AtRchAt.lean: WHAT THE LAW OF THE OUTPUT HEAD'S OWN ROUNDS TAKES "UNDER Rch 341 a", AT THE FAMILY THAT COUNTS:
Rch := RchAt (Johnson/Top/H0/Walk/ReachAt.lean) at the proof file's own IOP as written in Lean, in the goals'
scope. Statements and proofs: each is one call of a theorem along the fold, in the letters in which the law's premises stand.

THE LETTERS. P : VerifierAndGoals.PublicFiles (the law's Z) · lay : ByteArray (the law's lay is "some lay") · O : IM.Open …: what the maker of the
IOP returns, opened · FD Z A B c := ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c: O.desc
says F = FD Z A B c · the law's type P of public parts := ProofFile.InstPub · Str: whatever stands beside (the law's Fr.E.Str).
  reach_of_rchAt     RchAt (FD …) k a gives Reach 0 c.blocksInOrder (ProofFile.startS Z) k (a.1.1, a.1.2): by rchAt_raw; the rest by unfolding.
  **wp_is**          THE TIE OF THE PUBLIC PARAMETERS: where the law's hX holds at "some lay": Wp = Z.p.X, and Wp = Bs.G₀.W.
  **reached_rchAt**  K6Reached a.1.2 (the tables of the reads are not laid; the merge has not laid its end value).
  (tokSmall_rchAt: TokSmall Wp.hS.V a.1.2, in the law's own letter Wp: in P4R/K6TokAtRchAt.lean, which stands on one more file.)
  **free_rchAt**, **wellLaid_rchAt**   the open ledger is free above its next slot; it is well laid.
WHAT IS LEFT: hOk : F.planOk = true: the IOP's own test on the list of rounds accepts (in reached_rchAt, free_rchAt, wellLaid_rchAt):
it gives every sub-protocol's own test (P4.plan_at, off planOk_blocks); number 340's is what is spent.
Every letter under "there is": none. THE WITNESSES INSIDE RchAt ARE NOT THE RUN'S OWN: nothing is concluded of them.
What it does not say. "No mark" is asked by none of the three (it stands in the law's binders: idle). Nothing on soundness.

-/
import Johnson.P4R.K6ReachedAt341
import Johnson.P4R.FreeAt341N
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (K6Reached)
open VerifiableInference.OnPublicFiles (FreeAt)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- The proof file's own IOP as written in Lean, at the opened letters. -/
abbrev FD (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Str : Type}

/-- The family, in the letters of the theorems along the fold. -/
theorem reach_of_rchAt {k : Nat} {a : (ProofFile.InstPub × S) × Str} (h : RchAt (FD Z A B c) k a) :
    Reach 0 c.blocksInOrder (ProofFile.startS Z) k (a.1.1, a.1.2) := rchAt_raw h

/-- **The tie of the public parameters.** -/
theorem wp_is (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Wp : OnBytes.Model.Verify.Public}
    (hX : OnBytes.Model.Verify.publicOf P.pol P.KL (some lay) = .ok Wp) :
    Wp = Z.p.X ∧ Wp = Bs.G₀.W := by
  have e : Wp = Bs.G₀.W := Except.ok.inj (hX.symm.trans O.public)
  exact ⟨e.trans O.W, e⟩

/-- **What is taken from "reached" alone.** -/
theorem reached_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : F.planOk = true) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 341 a → a.1.2.failed = none →
      K6Reached a.1.2 :=
  fun _ h _ => k6Reached_341 hS hR O (plan_at O hOk 340) (reach_of_rchAt h)

/-- **The open ledger is free above its next slot.** -/
theorem free_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : F.planOk = true) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 341 a → a.1.2.failed = none →
      FreeAt (fun s : S => s.fork?) a.1.2 :=
  fun _ h _ => free_at_341 hS hR O (plan_at O hOk 340) (reach_of_rchAt h)

/-- **It is well laid.** -/
theorem wellLaid_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : F.planOk = true) (hh : OnBytes.Model.Head.Shape)
    (iU3 : Nat) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 341 a → a.1.2.failed = none →
      WellLaid ((seatAt hh iU3).ledger a.1.2) :=
  fun _ h _ => wellLaid_341 hS hR O (plan_at O hOk 340) (reach_of_rchAt h) hh iU3

end P4

#print axioms P4.wp_is
#print axioms P4.reached_rchAt
#print axioms P4.free_rchAt
#print axioms P4.wellLaid_rchAt
