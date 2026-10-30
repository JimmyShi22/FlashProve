-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K8MsgsOn.lean: the list ProofFile.k8Msgs Z look
(Johnson/Desc/ProofFile/Lot/K8.lean: the numbers, in the first chain's order of sending, of the
oracle messages that one step of the plan's table sends) AS A FUNCTION OF THE TABLE OF STEPS AND THE
DECLARED ROUNDS' ENTRIES ALONE. A definition with code, and the law that the two are one list at
every public part. So that Lean's kernel can evaluate the twin at written values of these two lists.
A tool for every lot whose blocks' lists "before" go by k8Msgs.

Main names (namespace Johnson.AtFull.Lots).
  k8MsgsOn cuts es look: the twin. rootsTake_eq: the count of roots in front reads the entries
      alone.
  k8Msgs_eq: ProofFile.k8Msgs Z look = k8MsgsOn Z.cuts (Z.D.1.map (·.entry)) look.

Over rootsOf, rootsFrom_eq and beforeAt (Johnson/Road/K4/K4SentAt.lean): called.
What it does not say. An equation of two lists: no list is evaluated here. Nothing on soundness.

-/
import Johnson.Road.K4.K4SentAt
import Johnson.Desc.ProofFile.Lot.K8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots

open OnBytes.Road.K4 (rootsOf rootsFrom_eq beforeAt)
open VerifiableInference.Desc.First (Cut)

/-- ProofFile.k8Msgs, from the table of steps and the declared rounds' entries alone. -/
def k8MsgsOn (cuts : List Cut) (es : List Fmt.Entry) (look : String) : List Nat :=
  match cuts.find? (·.look == look) with
  | some c =>
    (List.range (rootsOf (es.take (beforeAt cuts look + c.take)) -
      rootsOf (es.take (beforeAt cuts look)))).map (· + rootsOf (es.take (beforeAt cuts look)))
  | none => []

/-- The count of roots in front of a round reads the entries alone. -/
theorem rootsTake_eq (l : List Fmt.DeclaredRound) (k : Nat) :
    (l.take k).foldl (fun a r => a + r.entry.roots) 0 = rootsOf ((l.map (·.entry)).take k) := by
  unfold rootsOf
  rw [rootsFrom_eq, ← List.map_take, List.foldl_map]

/-- **The two are one list**, at every public part and every name. -/
theorem k8Msgs_eq (Z : ProofFile.Pub) (look : String) :
    ProofFile.k8Msgs Z look = k8MsgsOn Z.cuts (Z.D.1.map (·.entry)) look := by
  unfold ProofFile.k8Msgs k8MsgsOn
  cases hf : Z.cuts.find? (·.look == look) with
  | none => cases Z.roundsBefore? look <;> rfl
  | some c =>
    have hc : (c.look == look) = true :=
      List.find?_some (p := fun x : Cut => x.look == look) hf
    have hany : (Z.cuts.any fun c => c.look == look) = true :=
      List.any_eq_true.2 ⟨c, List.mem_of_find?_eq_some hf, hc⟩
    have hr : Z.roundsBefore? look = some (beforeAt Z.cuts look) := by
      unfold ProofFile.Pub.roundsBefore?
      rw [if_pos hany]
      rfl
    rw [hr]
    show (List.range ((Z.D.1.take (beforeAt Z.cuts look + c.take)).foldl
        (fun a r => a + r.entry.roots) 0 -
      (Z.D.1.take (beforeAt Z.cuts look)).foldl (fun a r => a + r.entry.roots) 0)).map
        (· + (Z.D.1.take (beforeAt Z.cuts look)).foldl (fun a r => a + r.entry.roots) 0) = _
    rw [rootsTake_eq, rootsTake_eq]

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.rootsTake_eq
#print axioms Johnson.AtFull.Lots.k8Msgs_eq
