-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/WorthOverMerge.lean: THE TWO ITEMS worth "planes" AND worth "keys" OF THE
LOOKUP ON THE DIGITS GO FORWARD OVER THE ACCEPTING STEP OF THE MERGE OF THE CLAIMS ON THE COMMITTED
TABLE (kind K11): from the state in front to the state behind. General in the meaning Mg, under
`K3At`. The mirror of the library's `worth_at_merge` (Johnson/Top/H0/MergeLaw/WorthAtMerge.lean),
which goes back. It stands over the library and two files of Johnson/Desc/ProofFile/Honest/K3/Law/
(WorthOn.lean, Earlier.lean). Two theorems; no definition; none of the library's goals.

  **`worth_planes_over_merge`**, **`worth_keys_over_merge`**   K3At X D L Mg · what `digAt` returns
                   at m · the merge's yes from s to s' · N: whatever the digits' seat has heard at
                   s, its forms are named at the ledger of s (`Fo.Tp.PadNames`) ⊢ the item at
                   (z, s), y, w gives the item at (z', s'), y', w
HOW. That a ledger is open in front comes off the yes (`merge_sizes`,
Johnson/Desc/First/Link/Law/SizesBack.lean) · the ledger behind, that it is later, and that the
test's data stay: `merge_forks` (Johnson/Top/H0/MergeLaw/KeepAtMerge.lean) · then
`worth_planes_on`, `worth_keys_on` (Johnson/Desc/ProofFile/Honest/K3/Law/WorthOn.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: `simp` on one line of each proof, with three named facts, on the reader of the
ledger.
Limits. AN IMPLICATION. N IS A PREMISE: Johnson/Desc/ProofFile/Honest/K3/Law/NamedAt346.lean has it
at a reached state. The witness w stands under "for all": the item is handed on. That the item
holds at any state is not said.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.WorthOn
import Johnson.Top.H0.MergeLaw.KeepAtMerge
import Johnson.Desc.First.Link.Law.SizesBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (digAt)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

variable {Pp Cells Tok : Type} {X : Verify.Public} {D : Desc.First.Look.Sent}
  {L : K3Letters Cells Tok} {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)}

/-- **worth "planes" goes forward over the merge's accepting step.** -/
theorem worth_planes_over_merge (hK : K3At X D L Mg) {Cl : Type} (claim : Aff → Cl) (m : ℕ)
    {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X m = some (x, tl)) (P : HeadMergeP)
    {s s' : S} {rs : List Fmt.RoundView} (hy : headMergeDecide P s rs = .ok s')
    (N : ∀ g F, s.fork? = some F → (Desc.K3.seatDigits claim).heard s = some g →
      _root_.Fo.Tp.PadNames g F)
    (z z' : Pp) (y y' : Strs) (w : Desc.Wit Cells Tok MsgT) :
    Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z, s) y w →
      Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z', s') y' w := by
  intro H
  obtain ⟨a, _, ha, -, ho, -, -⟩ := LinkJoin.merge_sizes P hy
  have hF : s.fork? = some a.F := by simp [S.fork?, ha, ho]
  obtain ⟨_, _, -, -, -, hG, hL, htl, -⟩ := MergeLaw.merge_forks P hy hF
  have hh : (Desc.K3.seatDigits claim).heard s' = (Desc.K3.seatDigits claim).heard s := by
    show s'.tl?.bind (·.heard) = s.tl?.bind (·.heard)
    rw [htl]
  exact ProofFile.Honest.K3.Law.worth_planes_on hK claim m hx z z' s s' y y' w hh hF hG
    ⟨hL.next, hL.ns, hL.keep⟩ (fun g hg => N g a.F hF hg) H

/-- **And "keys".** -/
theorem worth_keys_over_merge (hK : K3At X D L Mg) {Cl : Type} (claim : Aff → Cl) (m : ℕ)
    {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X m = some (x, tl)) (P : HeadMergeP)
    {s s' : S} {rs : List Fmt.RoundView} (hy : headMergeDecide P s rs = .ok s')
    (N : ∀ g F, s.fork? = some F → (Desc.K3.seatDigits claim).heard s = some g →
      _root_.Fo.Tp.PadNames g F)
    (z z' : Pp) (y y' : Strs) (w : Desc.Wit Cells Tok MsgT) :
    Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z, s) y w →
      Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z', s') y' w := by
  intro H
  obtain ⟨a, _, ha, -, ho, -, -⟩ := LinkJoin.merge_sizes P hy
  have hF : s.fork? = some a.F := by simp [S.fork?, ha, ho]
  obtain ⟨_, _, -, -, -, hG, hL, htl, -⟩ := MergeLaw.merge_forks P hy hF
  have hh : (Desc.K3.seatDigits claim).heard s' = (Desc.K3.seatDigits claim).heard s := by
    show s'.tl?.bind (·.heard) = s.tl?.bind (·.heard)
    rw [htl]
  exact ProofFile.Honest.K3.Law.worth_keys_on hK claim m hx z z' s s' y y' w hh hF hG
    ⟨hL.next, hL.ns, hL.keep⟩ (fun g hg => N g a.F hF hg) H

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.worth_planes_over_merge
#print axioms VerifiableInference.Desc.First.K8.Honest.worth_keys_over_merge
