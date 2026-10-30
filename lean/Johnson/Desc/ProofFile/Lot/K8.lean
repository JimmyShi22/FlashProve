-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K8.lean: THE LOT OF KIND K8, THE SMALLNESS TEST, WHOLE: at every place of
the kind ONE block (Johnson/Desc/First/K8/Whole.lean) that hears the draw of the matrix and STATES
THE KIND's THREE LISTS UNDER THE DRIVER's OWN NAMES, typed at VerifiableInference.Desc.Claim:
«K8.equations» in claims · «K8.lsTail», «K8.tests» in after.
So it stands in hearC; own is empty. The three runs' texts stand in
Johnson/Desc/First/TailClaims/K8Claims.lean.
NO WEAKENED OR PLANTED TEXT, NO TURNING. A place's numbers are made of the links' planned records,
of the public files' record (the families of tables; the lengths of the vectors of reads) and of the
plan's declared rounds alone.
still := [].
Limits: definitions with code, no theorem. No evaluation of this library runs the block as a whole
in a fold (foldBlocks, chainAt: Johnson/Desc/Block.lean).
`k8NU`, and at an attention link `k8Asks`, fall to an empty list or array where the public files'
record has no entry at the link's group (`.getD []`, `.getD #[]`): no error is raised there.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.K8.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First

/-- The numbers, in the first chain's order of sending, of the oracle messages that one step of the
plan's table of stretches sends; look: the step's name there. Where the table has no step of that
name the list is empty: then the kind's test on the plan is false at the place that names it. -/
def k8Msgs (Z : Pub) (look : String) : List Nat :=
  match Z.cuts.find? (·.look == look), Z.roundsBefore? look with
  | some c, some n =>
    let roots := fun (k : Nat) => (Z.D.1.take k).foldl (fun a r => a + r.entry.roots) 0
    (List.range (roots (n + c.take) - roots n)).map (· + roots n)
  | _, _ => []

/-- The families of tables at a link, off the public files' record. -/
def k8Asks (G : Ground) (X : OnBytes.Model.Stages.LinkH) : List (Nat × Nat × Nat) :=
  if X.kind == 2 then K8.Asks.head G.W.hS
  else if X.kind == 1 then ((G.W.A[X.g]?).map fun P => K8.Asks.attention P.S).getD []
  else K8.Asks.layers G.W.y G.W.layers.rd X.g

/-- The plan's lengths of the vectors of reads at a link, off the public files' record. -/
def k8NU (G : Ground) (X : OnBytes.Model.Stages.LinkH) : Array Nat :=
  if X.kind == 2 then G.W.H.nU
  else if X.kind == 1 then ((G.W.A[X.g]?).map (·.seam.nU)).getD #[]
  else ((G.W.G[X.g]?).map (·.nU)).getD #[]

/-- A place's numbers. -/
def k8Par (Z : Pub) (G : Ground) (X : OnBytes.Model.Stages.LinkH) (l : Nat) : K8.Par :=
  let head := X.kind == 2
  { link := l, piece := if head then 6 else 5, ks := X.tl.mats.toList.map (·.k), tau := X.tl.tau
    ms := X.tl.mats.toList.map (·.m), asks := k8Asks G X
    matsIn := k8Msgs Z (X.name ++ (if head then ".1.call" else ".0.call"))
    readsIn := k8Msgs Z (X.name ++ (if head then ".4.call" else ".3.call")) }

/-- A place's numbers, for both halves. -/
def k8ParW (Z : Pub) (G : Ground) (X : OnBytes.Model.Stages.LinkH) (l : Nat) : K8.ParW :=
  { toPar := k8Par Z G X l, nU := k8NU G X }

/-- The kind's block, whole, at every place. -/
def k8Whole (Z : Pub) (G : Ground) : List (Block S Cl) :=
  G.built.toList.zipIdx.map fun (X, l) => K8.whole (k8ParW Z G X l)

def P1K8.lot (Z : Pub) : Lot :=
  { name := "the smallness test", letters := false, own := fun _ => [], hearC := k8Whole Z,
    controls := [] }

end ProofFile
