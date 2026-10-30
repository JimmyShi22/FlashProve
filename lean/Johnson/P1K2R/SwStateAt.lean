-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SwStateAt.lean: the code switch: SwState
(Johnson/Top/H0/Tw/K2C/DebtsState.lean: what the debts on the table's numbers ask of the state at
the border in front of a switch) AT THE 25 BORDERS, IN SCOPE, FROM THE FOLD's RETURN: a join over
the integer-model's theorems.
  swState_of_rec   the six facts from the integer-model's RecAll (the statement's codes; the walk's
                   copy of the frame has the plan's shape and that shape's groups), the frame's link
                   and the two invariants on stored sample rows
  swState_link     at the state that the fold returns over the first 14 l + 2 sub-protocols, l < 25:
                   the link by the integer-model's laid_at («laid» l tests it and hands the state
                   on) swState_head over the first 339: the link by laid_at at 338 and h1_check (the
                   place «H:1» leaves the walk's state of the calls): as inside the integer-model's
                   own front_pin_head
  swState_finish   over the first 353, where the finish's way in lets the state in: the link out of
                   finishFrontQ_fr (Johnson/Top/H0/Tw/K2C/FinFront.lean): NO WALK IS WANTED FOR IT
swState_link_reach · swState_head_reach · swState_finish_reach  the same at a state that is reached
                   over the wrapped sub-protocols
THE PREMISES. hS hR O: in scope, the files read, IM.Open (Johnson/IMR/SeatOpen.lean). f₀: the fold's
return. hG, hA: the two invariants at that state: both_in_scope (BothInScope.lean): IT SPEAKS OF
«Reach» OVER THE WRAPPED SUB-PROTOCOLS (c.blocksInOrder.map below): so the three forms …_reach take just that
premise, and go to the fold by reach_raw and Reach.fold
(Johnson/Top/H0/Walk/Reach.lean: read). (From a bare fold's return one does NOT get back to the
wrapped «Reach».) both_in_scope IS NOT CALLED HERE: it does not stand in the set of files over which
this file is written. At the finish: hlen: 353 ≤ the front's length (front_len, in Johnson/IMR/,
which waits in that set of files) · h25: the plan's shape has 25 links: closed. (Today: front_len is declared in Johnson/IMR/FinPin.lean and in Johnson/IMR/RootsWhole.lean, each stating (frontOf c).length = 353 under hS, hR, O; both_in_scope is declared in Johnson/P1K2R/BothInScope.lean; the three paths are in this library, and this file's imports reach none of them.) SO «link», the one
fact of SwState that is no field of FoldFacts (Johnson/Desc/First/FoldFacts.lean), HAS ITS PAYER.
LIMITS. A join. The sh and codes are Z.first.shape | Z.first.codes: that the plan's numbers' n.codes
are these is not said here. No soundness is claimed.
-/
import Johnson.IMR.FrontPin
import Johnson.Top.H0.Tw.K2C.DebtsState
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The six facts from the integer-model's RecAll, the frame's link and the two invariants. -/
theorem swState_of_rec {cs : Codes} {sh : Params.ReqShape} {s : S} {m : Nat} (R : RecAll cs sh s)
    (hk : s.check.frame.link = m) (hG : VerifiableInference.Desc.First.K2.SampleGoodS s.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored s.st) :
    VerifiableInference.Desc.First.K2.SwState sh m cs s :=
  ⟨R.walk.shape, by rw [R.walk.groups, R.walk.shape], hk, R.codes, hG, hA⟩

/-- **AT THE BORDER IN FRONT OF A LINK's SWITCH** (14 l + 2). -/
theorem swState_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hG : VerifiableInference.Desc.First.K2.SampleGoodS t₀.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored t₀.st) :
    VerifiableInference.Desc.First.K2.SwState Z.first.shape l Z.first.codes t₀ := by
  have hlen : 14 * l + 2 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := l) (i := 0) hl (by decide)
    omega
  exact swState_of_rec (open_recAll hS hR O (by omega) hlen f₀) (laid_at hS hR O hl f₀).2 hG hA

/-- **AT THE BORDER IN FRONT OF THE HEAD's SWITCH** (339). -/
theorem swState_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hG : VerifiableInference.Desc.First.K2.SampleGoodS t₀.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored t₀.st) :
    VerifiableInference.Desc.First.K2.SwState Z.first.shape 24 Z.first.codes t₀ := by
  have ix : ∀ i, IM.flatIx c 24 i = 338 + i := fun i =>
    (IM.flatIx_scope hS hR O (by decide) i).trans (by omega)
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [ix 0] at k
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  have hk : t₀.check.frame.link = 24 := by
    rw [h1_check d0']
    exact (laid_at hS hR O (l := 24) (by decide) fm).2
  have hlen : 339 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide)
    omega
  exact swState_of_rec (open_recAll hS hR O (by decide) hlen f₀) hk hG hA

/-- **AT THE BORDER IN FRONT OF THE FINISH's SWITCH** (353), where the way in lets the state in. -/
theorem swState_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ t : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hlen : 353 ≤ (frontOf c).length) (h25 : Z.first.shape.link.length = 25)
    (he : VerifiableInference.Desc.First.K2.finishFrontQ t₀ = .ok t)
    (hG : VerifiableInference.Desc.First.K2.SampleGoodS t₀.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored t₀.st) :
    VerifiableInference.Desc.First.K2.SwState Z.first.shape 25 Z.first.codes t₀ := by
  have Rr := open_recAll hS hR O (by decide) hlen f₀
  obtain ⟨a, G, -, -, -, h4, h5, h6, -⟩ := VerifiableInference.Desc.First.K2.finishFrontQ_fr he
  have hk : t₀.check.frame.link = 25 := by
    rw [← h6, h4, h5, Rr.walk.shape, h25]
  exact swState_of_rec Rr hk hG hA

/-! ## The same at «reached», in the form in which the two invariants are had -/

section
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open VerifiableInference.Desc.Sound (below)

theorem swState_link_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s))
    (hG : VerifiableInference.Desc.First.K2.SampleGoodS s.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored s.st) :
    VerifiableInference.Desc.First.K2.SwState Z.first.shape l Z.first.codes s := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact swState_link hS hR O hl f hG hA

theorem swState_head_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (hG : VerifiableInference.Desc.First.K2.SampleGoodS s.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored s.st) :
    VerifiableInference.Desc.First.K2.SwState Z.first.shape 24 Z.first.codes s := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact swState_head hS hR O f hG hA

theorem swState_finish_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hlen : 353 ≤ (frontOf c).length) (h25 : Z.first.shape.link.length = 25)
    (he : VerifiableInference.Desc.First.K2.finishFrontQ s = .ok t)
    (hG : VerifiableInference.Desc.First.K2.SampleGoodS s.st)
    (hA : VerifiableInference.Desc.First.K2.AnsweredStored s.st) :
    VerifiableInference.Desc.First.K2.SwState Z.first.shape 25 Z.first.codes s := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact swState_finish hS hR O f hlen h25 he hG hA

end

end Meaning.K2

#print axioms Meaning.K2.swState_link_reach
#print axioms Meaning.K2.swState_head_reach
#print axioms Meaning.K2.swState_finish_reach

#print axioms Meaning.K2.swState_link
#print axioms Meaning.K2.swState_head
#print axioms Meaning.K2.swState_finish
