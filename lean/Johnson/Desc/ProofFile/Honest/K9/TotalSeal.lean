-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalSeal.lean: FOR THE ITEM "totalB": `SealLaw` (Honest/K9/TotalFront.lean) IS PAID
BY THE SEALED LIBRARY's OWN STRUCTURES, ONE FOR EACH SORT OF SEGMENT: THE FIRST LAYER OF THE FILLING. Statements and
proofs over the library's laws; no goal is stated. THE FILLING, the same at the three sorts but for the sort's own
letters: φ := `phiAll u ψ` · π := `pi8` · Ok := the sort's named promise and a letter Kx · the state behind is full:
`FullAt nU` · the terms and numbers: the sort's own tables at `entUnit`, `tmFour` and the lookups' letters t3, l3:
  **`sealLaw_layers`**   from `LayersOwesC m p4 Kx t3 l3 L u ψ nU p tlD`
      (Johnson/Desc/First/Link/Law/LinkRestAtSort4C.lean): `SealLaw .layers m L p (phiAll u ψ) (fun q => OkLayers p4
      nU tlD q ∧ Kx q) nU u pi8 (tmL p4 entUnit tmFour t3) (lenL p4 l3)`
  **`sealLaw_att`**      from `AttOwesC m rd c Kx t3 l3 L u ψ nU p tlD`: the like at `OkAtt rd c nU tlD`, `tmA rd c
      …`, `lenA rd c l3`
  **`sealLaw_head`**     from `HeadOwesC m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD`: the like at `OkHead hS iU3
      p6 kap nU tlD`, `tmH hS iU3 p6 kap …`, `lenH hS iU3 p6 kap l3`
Each is five calls (the library's `runs_‹sort›`, `full_‹sort›`, `share_of_‹sort›OwesC`, `moveNum_‹sort›`, and
`run_‹sort›` at `rests_num u`, its first half, for the field numRun; at `take_of_‹sort›OwesC`), the structure's own
field on the two orders, and an equation by definition ("what φ shows"). THESE THREE LEAVE Kx, t3, l3, u, ψ, tlD AND
THE SORT's OWN LETTERS FREE, AND THAT IS TOO FREE FOR A SENTENCE OF Honest/K9/TotalFront.lean TO BE ASKED AT: the
structure says of t3 no more than the library's law on a run, which sees a run's terms through their polynomial alone
(so terms that cancel could be appended, and `ItemBack` would fail); at a Kx that nothing meets the structure's laws
hold for nothing, and `OkFront` fails. THE SENTENCES ARE TO BE PROVED AT THE SECOND LAYER, Honest/K9/TotalFill.lean:
the library's own constants. No member: the three structures are shown here at no link. Called by
Honest/K9/TotalFill.lean's three theorems.
WHAT IS NOT CLAIMED. The three structures at any link. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Link.Law.LinkRestAtSort4C
import Johnson.Desc.First.Link.Law.LinkLawAt
import Johnson.Desc.First.Link.Law.FullAtSort
import Johnson.Desc.First.Link.Law.NumRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {β : Type} {m : ℕ} {Kx : Phi β × Option Pub9 → Prop}
  {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {l3 : ℕ × String → Phi β × Option Pub9 → ℕ} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ}
  {p : Desc.K9.Where} {tlD : HTailF2}

/-- **At a feed-forward segment.** -/
theorem sealLaw_layers {p4 : OnBytes.Desc.First.K4.Par} (O : LayersOwesC m p4 Kx t3 l3 L u ψ nU p tlD) :
    SealLaw .layers m L p (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU u pi8
      (tmL p4 entUnit tmFour t3) (lenL p4 l3) :=
  ⟨O.seg, runs_layers (take_of_layersOwesC O), full_layers O.seg (take_of_layersOwesC O) O.k3g,
    share_of_layersOwesC O, fun _ => rfl, moveNum_layers u O.seg (take_of_layersOwesC O) O.k3f _,
    (run_layers (rests_num u) O.seg (take_of_layersOwesC O) O.k3f).1⟩

/-- **At an attention segment.** -/
theorem sealLaw_att {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (O : AttOwesC m rd c Kx t3 l3 L u ψ nU p tlD) :
    SealLaw .attention m L p (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU u pi8
      (tmA rd c entUnit tmFour t3) (lenA rd c l3) :=
  ⟨O.seg, runs_attention (take_of_attOwesC O), full_attention O.seg (take_of_attOwesC O) O.k3g,
    share_of_attOwesC O, fun _ => rfl, moveNum_attention u O.seg (take_of_attOwesC O) O.k3f _,
    (run_attention (rests_num u) O.seg (take_of_attOwesC O) O.k3f).1⟩

/-- **At the head's segment.** -/
theorem sealLaw_head {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p6 : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen}
    (O : HeadOwesC m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD) :
    SealLaw .head m L p (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) nU u pi8
      (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) :=
  ⟨O.seg, runs_head (take_of_headOwesC O), full_head O.seg (take_of_headOwesC O) O.k3g,
    share_of_headOwesC O, fun _ => rfl, moveNum_head u O.seg (take_of_headOwesC O) O.k3f _,
    (run_head (rests_num u) O.seg (take_of_headOwesC O) O.k3f).1⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.sealLaw_layers
#print axioms ProofFile.Honest.K9.sealLaw_att
#print axioms ProofFile.Honest.K9.sealLaw_head
