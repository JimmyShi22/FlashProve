-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/HtinAtConstantSlots.lean: `htin_at_const` (HtinAtConstant.lean) WITH ITS PREMISE «THE
OPEN LEDGER OF A STATE REACHED THERE HAS A COEFFICIENT FOR EACH SLOT» PAID by
`slots_at_reached` and `lsSize_of_slots` (Johnson/LPFK9R/SlotsSeat.lean, SlotsSize.lean), under the
first's one premise on the public part, `HeadSpots Zp nH`. A call. It changes no other file.

  `ls_at_const`: at every state reached at a number k ≤ 353 of the constant's first chain: the open
    ledger has a coefficient for each slot. (`slots_at_reached` speaks of SOME chain c of the made
    description; the description's first chain is one: c is the constant's cF.)
  `htin_at_const_slots`: **htin at the constant's letters from: linkPlanB at the built link ·
    HeadSpots Zp nH · «reached» gives Reach.**
Limits. linkPlanB and HeadSpots (as headSpotsB) are closed tests: true at the full-size files by
evaluations: no theorems. No member. Nothing on soundness.
-/
import Johnson.LPFK9R.HtinAtConstant
import Johnson.LPFK9R.SlotsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Link Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.JoinAtBlocks
open VerifiableInference.Desc.LinkJoin
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (nAt)
open P5J (AtMg AtMgA F0T fullLinks)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

theorem ls_at_const (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nH : ℕ} (hH : HeadSpots Zp nH)
    {k : ℕ} (hk : k ≤ 353) {a : ProofFile.InstPub × S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) :
    ∀ G, a.2.fork? = some G → G.LS.size = G.ns := by
  intro G hG
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨A, B, c, e, _, hs⟩ := slots_at_reached nH h.laid.pub hH h.laid.value
  have he : HEq cF c :=
    congr_arg_heq (fun X : VerifiableInference.Desc.FileDescription ProofFile.Inst => X.first) e
  obtain rfl : cF = c := eq_of_heq he
  exact lsSize_of_slots (hs k a hr (by rw [Meaning.Carry.front_len h.scope h.reads O]; exact hk)) hG

variable {x : VerifiableInference.Desc.First.Look.Place}

/-- **htin AT THE CLOSED CONSTANT's LETTERS, THE SLOTS PAID.** -/
theorem htin_at_const_slots {α : Type} {Fr : Frame} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {m : ℕ} (hm : m < 25) {L : Link S Cl} (hlk : h.𝔇.lk m = some L)
    (hP : ∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) {nH : ℕ}
    (hH : HeadSpots Zp nH) (z : ProofFile.InstPub) (Rz : ℕ → S × Fr.E.Str → Prop)
    (hRz : ∀ a, Rz (batchAt fullLinks P5J.At.ps m + 1) a →
      Reach 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder (F0T OnBytes.secondHashFunction Zp Np cF).start₁
        (batchAt fullLinks P5J.At.ps m + 1) (z, a.1)) :
    ∀ a t, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks P5J.At.ps (fun s : S => (z, s)) Rz
        (batchAt fullLinks P5J.At.ps m + 1) a →
      MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      VerifiableInference.Desc.K9.totalIn (h.𝔇.N.group m) t = true :=
  htin_at_const h hm hlk hP z Rz hRz fun s hr =>
    ls_at_const h.toAtMg hH (by
      rw [batch_nAt m hm]
      unfold nAt
      split <;> omega) hr

end LPFK9

#print axioms LPFK9.ls_at_const
#print axioms LPFK9.htin_at_const_slots
