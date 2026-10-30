-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/TenantAtHead.lean: kind K14: at the full size, in the soundness
side's table of numbers, no two of the shared chain's three sampled messages have one tenant.

The shared chain sends three messages that are sampled later: o_u, o_omega and o_sp (Msg2,
Johnson/Desc/Shared/BordersShared.lean). A tenant is a pair: the number of a tree, counted through
the proof file, and the message's number in that tree. The table of the shared chain's numbers
(NumbersS, the same file) names a tenant for each of the three. The kind's statements on the honest
prover ask that the three tenants differ (the field "tenant" of K14Asks, Honest/K14/Asks.lean:
Function.Injective L.N.tenant). This file proves it of the numbers that the soundness side lays at
the full size (IM.Seats.nsA, Johnson/IMR/SeatsAtHead.lean).

  tenants_written         the three tenants at the written sizes: (83, 0), (84, 0), (85, 0): an
                          evaluation in Lean's kernel. It can fail: the two written layouts of trees
                          end in a fall-back value, at which two of the three would coincide. Its
                          second clause is P5J.omega_written (Johnson/P5J/NumbersAtHead.lean)
  tenants_written_apart   so they differ
  tenant_at_head          at the full size: at every table N whose tenants are nsA's
  tenant_nsA, tenant_tied   that at nsA itself, and at nsA with the first chain's two tenants laid
                          in (tiedNumbers, Johnson/Desc/Sound/TieEnd.lean). By a reading, stated
                          neither in this file nor in any file that it imports: at the first chain's
                          table P5J.At.N Zp cF that is the table that
                          the soundness side's statements name (P5J.row0B_at_left,
                          Johnson/P2LawR/RowZeroBAtLeft.lean)

Limits.
  * THE PREMISE h IS A HYPOTHESIS. P5J.AtMg (Johnson/P5J/AtMg.lean) gathers conditions on the public
    files at the full size. This file does not show them to be met, and the verifier does not ask
    them. A member is proved at the hash OnBytes.secondHashFunction at two written sets of public files
    (AtFullSide/Top/: headMember_zFull, headMember_zGap), and at no others. A caller who holds the
    wider premise P5J.AtMgA (Johnson/P5J/MgAtAll.lean), which extends AtMg, passes h.toAtMg.
  * WHICH TABLE A THREAD OF THE HONEST PROVER LAYS IS ITS AUTHOR'S CHOICE: N is a free argument of
    lettersShared (Honest/Thread/SharedHead.lean). The field is paid where the author lays a table
    with nsA's tenants, and nothing is said of another table.
  * The general law from which the same follows at any sizes, under premises on the two layouts of
    trees, is tenants_apart (Johnson/Desc/Sound/SharedMembers.lean).

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.IMR.SeatsAtHead
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Shared (Msg2 NumbersS)
open VerifiableInference.Desc.Sound (tiedNumbers)
open _root_.Desc.K14.Law.Fence (tenantSh)
open _root_.Desc.K14.Law (layUFull layOFull)
open IM.Seats (nsA tenants_written_at_head)

/-- The three tenants at the written sizes. -/
theorem tenants_written : tenantSh 83 layUFull layOFull .oU = (83, 0) ∧
    tenantSh 83 layUFull layOFull .oOmega = (84, 0) ∧
    tenantSh 83 layUFull layOFull .oSp = (85, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- They differ. -/
theorem tenants_written_apart : Function.Injective (tenantSh 83 layUFull layOFull) := by
  obtain ⟨a, b, c⟩ := tenants_written
  intro m m' e
  cases m <;> cases m' <;> first
    | rfl
    | (exfalso
       simp only [a, b, c] at e
       exact absurd e (by decide))

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **At the full size: at every table whose tenants are those that the soundness side lays, no two
of the three messages have one tenant.** -/
theorem tenant_at_head (h : P5J.AtMg o Z D r Zp Np cF) {N : NumbersS}
    (hN : N.tenant = (nsA o Zp Np cF).tenant) : Function.Injective N.tenant := by
  rw [hN]
  show Function.Injective (tenantSh _ _ _)
  rw [tenants_written_at_head h]
  exact tenants_written_apart

/-- At the soundness side's own table. -/
theorem tenant_nsA (h : P5J.AtMg o Z D r Zp Np cF) :
    Function.Injective (nsA o Zp Np cF).tenant := tenant_at_head h rfl

/-- At that table with the first chain's two tenants laid in. -/
theorem tenant_tied (h : P5J.AtMg o Z D r Zp Np cF)
    (N₁ : VerifiableInference.Desc.First.Numbers) :
    Function.Injective (tiedNumbers N₁ (nsA o Zp Np cF)).tenant := tenant_at_head h rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.tenants_written
#print axioms ProofFile.Honest.K14.tenants_written_apart
#print axioms ProofFile.Honest.K14.tenant_at_head
#print axioms ProofFile.Honest.K14.tenant_nsA
#print axioms ProofFile.Honest.K14.tenant_tied
