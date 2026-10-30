-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TabsAtReachAll.lean: CONDITIONAL: `tabs_at_reach`
(Johnson/Desc/K5/Honest/Law/TabsAtReach.lean) IN THE FORM OF THE PREMISE t of the library's law on
the smallness test's draw at an attention segment (`ready_of_fold_att`, `ready_at_att`,
Johnson/Desc/First/K8/LawReadyAtt.lean): "for every tl that the state bears, the closed list's
shapes are the place's". One theorem, a corollary: the other form says that the state bears one.

Limits. As in TabsAtReach.lean. The library's premise speaks of the end of a fold over blocks; this
theorem of a state under `Reach`: that joint is the caller's.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.TabsAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA TS)

/-- **The closed list's shapes at every state reached in front of the draw, in the form of the
library's premise.** Conditional: the head; hg; M; hr: as `tabs_at_reach`. -/
theorem tabs_at_reach_all {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {G₀ : ProofFile.Ground}
    {Xl : Stages.LinkH} {pd : ℕ} {reads digits : Option (List ℕ)} {b : Block S ProofFile.Cl}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 6) (π, s)) :
    ∀ tl, s.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
        K8.tabs (ProofFile.k8Par Zp G₀ Xl (2 * g + 1)) := by
  obtain ⟨tl0, e, _, ht⟩ := tabs_at_reach h hg M hr
  intro tl e'
  obtain rfl : tl0 = tl := Option.some.inj (e.symm.trans e')
  exact ht

end H2K5.Honest

#print axioms H2K5.Honest.tabs_at_reach_all
