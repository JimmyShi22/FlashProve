-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/SlotsAtHead.lean: "THE OPEN LEDGER's TWO NUMBERS" AT THE CLOSED CONSTANT, FROM THE HEAD
ALONE: TWO TIES THAT K9's inSeg, inRun AND inTot WANT (Link/Law/InsideOfPromise.lean:
its hSl and hn). Statements and proofs: calls.

  `AtMgA.headSpots`: `HeadSpots Zp Zp.p.X.H.ns` (`headSpots_of_fit`, at the three facts that
    `headSpots_at` (LPFE1R/HeadSpotsConst.lean) lays in; there the number stands under "there is").
  `AtMgA.slots_at`: **k ≤ 353; h.toAtMg.rch k a ⊢ SlotsInv (nsZ Zp Zp.p.X.H.ns) a.1.2.** The chain
    under "there is" in `slots_at_reached` (LPFK9R/SlotsSeat.lean) is the constant's own: by the
    crossing of `ls_at_const` (LPFK9R/HtinAtConstantSlots.lean): the two descriptions
    are one, so their first chains are.
  `AtMgA.ns_is`: **m < 25 ⊢ nsZ Zp Zp.p.X.H.ns m = (At.nsAt Zp m, At.nsAt Zp m)** (`ns_in_scope`,
    LPFK9R/NsInScope.lean).
Limits. No soundness statement.

-/
import Johnson.LPFE1R.HeadSpotsConst
import Johnson.LPFK9R.HtinAtConstantSlots
import Johnson.LPFK9R.NsInScope
import Johnson.P5J.FoldMoreAt
import Johnson.P5J.FourAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (HeadSpots headSpots_of_fit SlotsInv nsZ slots_at_reached
  ns_in_scope)
open Johnson.Desc.First.Walk.Tied (rchAt_raw)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem AtMgA.headSpots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    HeadSpots Zp Zp.p.X.H.ns :=
  headSpots_of_fit (H2K12.spots_atAll h (pins_of_laid h.scope h.laid).2)
    (P1K2.links25_atAll h) h.toAtMg.kind24

/-- **(G1).** -/
theorem AtMgA.slots_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ} (hk : k ≤ 353)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (VerifiableInference.Desc.Sound.EAll (D.at OnBytes.Slice.frS.P.T.a)
        (VerifiableInference.Desc.Sound.allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) : SlotsInv (nsZ Zp Zp.p.X.H.ns) a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨A, B, c, e, _, hs⟩ := slots_at_reached _ h.laid.pub h.headSpots h.laid.value
  have he : HEq cF c :=
    congr_arg_heq (fun X : VerifiableInference.Desc.FileDescription ProofFile.Inst => X.first) e
  obtain rfl : cF = c := eq_of_heq he
  exact hs k a.1 (rchAt_raw hr.1)
    (by rw [Meaning.Carry.front_len h.scope h.reads O]; exact hk)

/-- **(G2).** -/
theorem AtMgA.ns_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) :
    nsZ Zp Zp.p.X.H.ns m = (At.nsAt Zp m, At.nsAt Zp m) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ns_in_scope h.scope h.reads O.pub O.blank hm

end P5J

#print axioms P5J.AtMgA.headSpots
#print axioms P5J.AtMgA.slots_at
#print axioms P5J.AtMgA.ns_is
