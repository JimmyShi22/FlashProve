-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MsgsScope.lean:
IN THE GOALS' SCOPE, FROM THE FOLD's RETURN ALONE: THE NUMBER OF ORACLE MESSAGES THAT THE
VERIFIER's
STATE HAS RECEIVED IS WHAT THE BLOCKS IN FRONT TELL, AT EVERY CUT IN FRONT OF THE BLOCKS BEHIND THE
LAST LINK. UNDER TWO NAMED PREMISES ON THE PLAN ALONE, EACH PROVED IN
ITS OWN KIND's FILES, NEITHER JOINED HERE.

  hM_scope: Johnson/IMR/MsgsCut.lean's msgs_at_cut_but's premise, by Johnson/IMR/MsgsPlaces.lean's
    adds_at_marked.
  msgs_at_cut_scope: **InScope P · readFiles P = .ok pp · O : Open OnBytes.secondHashFunction … · K1Told ·
      K2Told · k ≤ 353 · every block of c.blocksInOrder.take k passes its test on the plan · foldBlocks 0
      (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r ⇒ r.1.st.oracles.size = ((c.blocksInOrder.take k).map
      toldMsgs).sum.**
  bookAt_scope stands in BookAtWhole.lean, and this file does not
      import BookAtCut.lean: so it does not stand over Johnson/Desc/First/Borders.lean.
THE TWO PREMISES. K1Told (MsgsSeat.lean): K1.told_tenants_own (Johnson/Desc/K1/Law/
ToldCounts.lean) says it (k1Told_paid, Johnson/IMR/ToldPaid.lean); it is not
imported beside Johnson/Desc/Book/BookFits.lean. K2Told (MsgsSwitch.lean):
P1K2.told_tenants (Johnson/Top/H0/Tw/K2C/ToldTenants.lean) says it (k2Told_paid, ToldPaid.lean);
not imported here either. Both speak of the plan's texts alone; no state, no run.

OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription OnBytes.secondHashFunction's value, in scope;
not verify(). User: Johnson/IMR/MsgsBehind.lean; Johnson/IMR/N0AtCut.lean. Letters: none.
Compiled with the whole library.
Limits. Nothing behind the last link (k ≤ 353). ft = 0 and the first state ProofFile.startS Z p alone. No
member: that a fold returns is shown of no proof. Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.MsgsPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- msgs_at_cut_but's premise on the blocks set apart, in scope. -/
theorem hM_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : K2Told) {k : Nat}
    (hk : k ≤ 353) (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (p : ProofFile.InstPub)
    (R : List Fmt.RoundView) (C : List OpenedColumn) :
    ∀ (j : Nat) (b : Block S Cl), j < k → c.blocksInOrder[j]? = some b → Marked drawsPos b →
      ∀ r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn,
        foldBlocks 0 (c.blocksInOrder.take j) (ProofFile.startS Z p) R C = .ok r₀ →
        foldBlocks 0 (c.blocksInOrder.take (j + 1)) (ProofFile.startS Z p) R C = .ok r₁ →
        r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b :=
  fun j b hj hb hm _ _ f₀ f₁ =>
    adds_at_marked hS hR O hT (by omega) hb
      (hp b (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hb))) hm f₀ f₁

/-- **IN THE GOALS' SCOPE: THE NUMBER OF ORACLE MESSAGES THAT THE VERIFIER's STATE HAS RECEIVED, AT
EVERY CUT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, IS WHAT THE BLOCKS IN FRONT TELL.** -/
theorem msgs_at_cut_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    {k : Nat} (hk : k ≤ 353) (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (p : ProofFile.InstPub)
    (R : List Fmt.RoundView) (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    r.1.st.oracles.size = ((c.blocksInOrder.take k).map toldMsgs).sum := by
  have e := msgs_at_cut_but O h1 k (by rw [front_len hS hR O]; exact hk) hp 0 _ R C
    (hM_scope hS hR O hT hk hp p R C) r h
  rwa [Meaning.K2.start_none O.pub p, Nat.zero_add] at e

#print axioms hM_scope
#print axioms msgs_at_cut_scope

end Meaning.Carry
