-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OutTrue.lean: OUT, BY THE CALL, AT THE BLOCK's ONE HEARING, WITH THE READS READ AS THE STATED SUMS OF THE CELLS: STATED
AND PROVED: Law/OutBlock.lean's outBlock_at at the reads "in truth" (HeadLaw.lean: readsAt; HeadNormLaw.lean:
normReadsAtCells: each entry of a read is the constant form of its weighted sum of cells).
WHY. The reads' array is committed BEHIND the head's rounds. At the border behind the head's block the table of joints
judges the block's forms with each entry of that later array READ AS THE STATED FUNCTION OF THE CELLS; the exchange for
the committed array, and that the reads are true, stand at later blocks (the sending; the smallness test). In that
reading the four premises on reads of outBlock_at hold by the reads' own definition: HERE THEY ARE GONE.
WHAT IS LEFT AS PREMISES, beside public tests and the hearing: no bad draw under the block's rule by name; the run
"logits" and normedForms worth 0; the claim on the weights true.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OutBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)
open Came (val)

/-- No entry of a sent read is looked at. -/
def noEnt : Nat → Nat → Nat → E := fun _ _ _ => 0

/-- **OUT, BY THE CALL, AT TRUE READS.** -/
def OutTrueStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork),
    planOk sT = true → Request.ok = true → y < V → WellLaid F → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∀ (rs : List Fmt.RoundView) (H : HeardAll) (F1 G : Fork),
      Canonical rs → hear F rs = some (H, F1, []) → Later F1 G → NoBad (Came.blockRule c mask F) rs →
      let _ : Norm.Heard := H.1
      let _ : FinalNorm.Heard := H.2.1
      let _ : Heard := H.2.2
      let _ : FinalNorm.Reads := normReadsAtCells c
      let _ : Reads := readsAt c.toCells
      WeightTrue c.toCells G mask noEnt →
      (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) →
      (∀ f, f ∈ FinalNorm.normedForms → atWorld G mask noEnt f = 0) →
      (∀ call, call < 6 →
        rd (atWorld G mask noEnt
            (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
          = (Finset.range (2 ^ (zk call).size)).sum fun i =>
              rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
      atWorld G mask noEnt clip = (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) ∧
      atWorld G mask noEnt table = (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t))

namespace Came

theorem atWorld_coe (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) (x : E) :
    atWorld F mask ent ((x : E) : Form) = x := rfl

theorem outTrue : OutTrueStatement := by
  intro _ _ _ _ nI hI sT floor zx zk c mask F hplan hreq hy hWL hP hn hh rs H F1 G hcan hhear hL hnb
    _ _ _ _ _ hwt hlog hnf
  exact outBlock_at sT floor zx zk c mask F hplan hreq hy hWL hP hn hh rs H F1 G noEnt hcan hhear hL
    hnb (fun _ _ _ => rfl) hwt
    ⟨fun _ _ => val_coe _ _, fun _ _ => val_coe _ _, fun _ _ => val_coe _ _⟩
    ⟨fun _ _ => val_coe _ _, fun _ _ => val_coe _ _⟩ hlog hnf

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outTrue
