-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/OmegaMemberAtSh.lean: THREE OF THE EIGHTEEN PREMISES OF THE LAW ON
ROW 0 OF THE LAST TABLE (rowZeroOwed_atZ_sh, Johnson/Flat/Last/RowZeroAtShX.lean): hm · hent · hten:
AT THE SHARED TABLE's CONSTANT's OWN LETTERS (Johnson/Desc/K14/Law/SharedConst.lean): mem := Sh.mem
A, x := Omega's member memSh … .oOmega. Statements and proofs; no definition.


  sentU_pos        where withU returns, "send o_u" has a message: so Omega's number is not 0.
  omega_member_at  at every A : ShPlan Xi: hm (Sh.mem A at the number (Sh.sentU A).size is Omega's
                   member) · hent (its shape is the first shape of "send o_omega") · hten (its seat,
                   in the law's own spelling), FROM: withU A.Q.S returns · Sh.t₁ A = t₁.
IS IT EMPTY? withU returns wherever the shared chain's sub-protocols pass their tests on the plan
(Johnson/Desc/Book/ToldShared.lean: can_of_back). Sh.t₁ A is the number of trees of which A.G's
first chain tells: at t₁ := D.t₁ it is toldCount, from A.G's data and blocksOk.
WHAT IS NOT HERE. That the seat is (D.t₁ + 1, 0): for the first half see ToldShared.lean's
shapes_one_u and LayOmega.lean's tree_omega, where the two layouts are returned. Nothing on
soundness.
-/
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.K14.Law.OmegaHasMsg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Sound (Mem)
open VerifiableInference.Desc.Shared (Msg2)
open VerifiableInference.Desc.K1 (shapeAt)
open _root_.Desc.K14 (withU)
open _root_.Desc.K14.Law (ShPlan parO omegaShapes_pos shape_omega memK)
open _root_.Desc.K14.Law (Sh.mem Sh.sentU Sh.layU Sh.layO Sh.t₁)
open _root_.Desc.K14.Law.Fence (memSh memSh_seat tenantSh)

/-- Where withU returns, "send o_u" has a message. -/
theorem sentU_pos {Xi : Type} (A : ShPlan Xi) {u : Array OracleNotice}
    (hU : withU A.Q.S = some u) : 0 < (Sh.sentU A).size := by
  have e : Sh.sentU A = u := by
    unfold Sh.sentU
    rw [hU]
    rfl
  rw [e]
  unfold _root_.Desc.K14.withU at hU
  obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.1 hU
  simp

/-- **hm, hent and hten at the shared table's constant's own letters.** -/
theorem omega_member_at {Xi : Type} (A : ShPlan Xi) (t₁ : ℕ) (ht : Sh.t₁ A = t₁)
    {u : Array OracleNotice} (hU : withU A.Q.S = some u) (x : Mem)
    (hx : x = memSh A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (Sh.t₁ A) (Sh.layU A) (Sh.layO A)
      .oOmega) :
    Sh.mem A (Sh.sentU A).size = some x ∧
      (x.1.l.get x.2).1 = shapeAt (parO A.Q) ⟨0, omegaShapes_pos A.Q⟩ ∧
      x.1.seat x.2 =
        (t₁ + (A.Q.par.toGPar.firstTree + ((Sh.layU A).shapes.size + (Sh.layO A).tree.getD 0 0)),
          (Sh.layO A).part.getD 0 0) := by
  subst hx
  have hpos := sentU_pos A hU
  refine ⟨?_, ?_, ?_⟩
  · unfold Sh.mem memK
    rw [if_neg (by omega), if_pos rfl]
  · rw [shape_omega]
    rfl
  · rw [memSh_seat]
    have f0 : A.Q.par.toGPar.firstTree = 0 := rfl
    rw [f0, ← ht, Nat.zero_add, ← Nat.add_assoc]
    rfl

end P2Law

#print axioms P2Law.sentU_pos
#print axioms P2Law.omega_member_at
