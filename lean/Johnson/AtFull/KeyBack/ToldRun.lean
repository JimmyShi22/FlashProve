-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldRun.lean: `toldVal` (ToldValue.lean) AS A TERM WITHOUT `List.mergeSort`.
General laws. Statements with proofs. Nothing is evaluated.

`toldVal` holds two sorts: the outer one, by rounds, and one inside `Key.rootsWithGroups`
(Johnson/Desc/Key/Source.lean), which lays a tree's tenants in the order of their parts. Here each
is written as the bounded text `sortF` (Johnson/Unfolds/MergeSort.lean), by its law
`mergeSort_eq`.
  `rootsRun`, `rootsWithGroups_eq`: `rootsWithGroups`' text with `sortF`; the two are one.
  `toldAtR`, `toldsR`, `toldsG_eq`: the same at a sending and along a chain's sendings.
  `toldRun`, `toldVal_eq`: the same at the value.
Limits. Nothing on whether `Key.toldOfChain` returns. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ToldValue
import Johnson.Unfolds.MergeSort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- `Key.rootsWithGroups`' text, its sort written as `sortF`. -/
def rootsRun (codes : Codes) (sent : List OracleNotice) (gs : List (List Nat)) :
    Option (List ProofFile.Root) :=
  (layTrees codes sent.toArray).map fun L =>
    L.shapes.toList.zipIdx.map fun t =>
      let mine := (Johnson.Unfolds.sortF
        (fun (a b : OracleNotice × Nat) => decide (L.part.getD a.2 0 ≤ L.part.getD b.2 0))
        ((sent.zipIdx.filter fun y => L.tree.getD y.2 0 == t.2).length + 1)
        (sent.zipIdx.filter fun y => L.tree.getD y.2 0 == t.2)).getD []
      { logLength := t.1.logN, words := t.1.mainWidth + t.1.maskWidth
        tenants := mine.map fun y =>
          { ProofFile.tenantOf y.1 with
            groups := if y.1.shape.answers != 0 then gs.getD y.2 [] else [] } }

/-- The two are one. -/
theorem rootsWithGroups_eq (codes : Codes) (sent : List OracleNotice) (gs : List (List Nat)) :
    rootsWithGroups codes sent gs = rootsRun codes sent gs := by
  unfold rootsWithGroups rootsRun
  simp only [Johnson.Unfolds.mergeSort_eq]

/-- `toldAtG` over `rootsRun`. -/
def toldAtR (codes : Codes) (off : Nat) (x : Sending) (gs : List (List Nat)) :
    List (Nat × ProofFile.Root) :=
  ((rootsRun codes x.sent gs).map fun l => l.map fun r => (x.entry - 1 - off, r)).getD []

/-- `toldsG` over `toldAtR`. -/
def toldsR (codes : Codes) (off : Nat) :
    List Sending → List (List (List Nat)) → List (List (Nat × ProofFile.Root))
  | x :: xs, g :: gs => toldAtR codes off x g :: toldsR codes off xs gs
  | _, _ => []

/-- The two are one. -/
theorem toldsG_eq (codes : Codes) (off : Nat) :
    ∀ (xs : List Sending) (gss : List (List (List Nat))),
      toldsG codes off xs gss = toldsR codes off xs gss
  | [], _ => by simp only [toldsG, toldsR]
  | _ :: _, [] => by simp only [toldsG, toldsR]
  | x :: xs, g :: gs => by
    simp only [toldsG, toldsR, toldAtG, toldAtR, rootsWithGroups_eq]
    rw [toldsG_eq codes off xs gs]

/-- `toldVal`, with neither sort as `List.mergeSort`. -/
def toldRun (c : ChainSends) (gss : List (List (List Nat))) (off : Nat) (e : List Sent)
    (held : Option OracleNotice) : List ProofFile.Root :=
  ((Johnson.Unfolds.sortF (fun (a b : Nat × ProofFile.Root) => decide (a.1 ≤ b.1))
    (((toldsR c.codes off c.sends gss).flatten ++ toldMore e held).length + 1)
    ((toldsR c.codes off c.sends gss).flatten ++ toldMore e held)).getD []).map (·.2)

/-- **The value as a term without `List.mergeSort`.** -/
theorem toldVal_eq (c : ChainSends) (gss : List (List (List Nat))) (off : Nat) (e : List Sent)
    (held : Option OracleNotice) : toldVal c gss off e held = toldRun c gss off e held := by
  unfold toldVal toldRun
  rw [toldsG_eq, Johnson.Unfolds.mergeSort_eq]

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rootsWithGroups_eq
#print axioms Johnson.AtFull.KeyBack.toldsG_eq
#print axioms Johnson.AtFull.KeyBack.toldVal_eq
