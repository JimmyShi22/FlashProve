-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowSkel.lean: **KIND K5's LOT IN THE FORM
"THE LOT's SKELETON IS THE WRITTEN ONE"** (ProofFile.Sk.lotSk,
Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean; ProofFile.Sk.Skel · skel,
Johnson/Desc/ProofFile/Law/Skel/Skel.lean: a sub-protocol less its functions: name · place · how
many rounds · the length of its list of oracle messages · the rounds that tell a tree · before · the
test on the plan · the names of its runs of claims and of its runs behind the batching). Under the
four premises of k5_row_plans (Johnson/Desc/First/Att/Row/K5RowPlans.lean). Calls and unfoldings.
NOTHING IS EVALUATED.
HERE THE NAME IS THE LOT's OWN (the text of attentionKind, Johnson/Desc/First/Att/K5AttentionKind.lean), not the name under
which the seat lays the sub-protocol.

Main names (namespace H2K5.Row):
  k5SkelW g: the written skeleton at group g. told_the_block: none of its rounds tells a tree, in
    the form ProofFile.Sk.toldFrom (by ProofFile.Sk.toldFrom_zip, Johnson/Desc/ProofFile/Law/Skel/SkelEnd.lean).
  skel_the_block: the skeleton of the lot's sub-protocol at g is k5SkelW g.
  **k5_lot_skel**: the lot's skeleton: its name · letters := false · still := [] · the twelve
    written skeletons · no batching, no test behind a run of claims, no test behind the adding.
IS IT EMPTY HERE? IMPLICATIONS: k5_row_plans' premises are shown at no public files.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowPlans
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (toldRounds)

/-- The written skeleton of the kind's sub-protocol at group g. -/
def k5SkelW (g : ℕ) : ProofFile.Sk.Skel :=
  { name := s!"an attention segment's own rounds, segment {2 * g + 1}", place := ⟨1, some (2 * g + 1), 3, .K5⟩, nRounds := 162, nOracles := 162, told := []
    before := [(1, 4 + 6 * g)], planOk := true, claims := ["first", "keys", "join", "second"], after := [] }

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : ℕ → Attention.Plan}

/-- None of its rounds tells a tree, in the form ProofFile.Sk.toldFrom. -/
theorem told_the_block (g : ℕ) : ProofFile.Sk.toldFrom 0 (the_block Z G P g).oracles = [] :=
  (ProofFile.Sk.toldFrom_zip (the_block Z G P g).oracles 0).symm.trans
    (blockAt_told (W := G.W) (l := 2 * g + 1) (p := P g) (before := (H2K5.k5Before? Z ("A" ++ toString g)).getD []))

/-- **The skeleton of the lot's sub-protocol at a group.** -/
theorem skel_the_block (places : H2K5.k5Places G = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g))
    (plan : ∀ g, g < 12 → G.W.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hb : ∀ g, g < 12 → H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)]) (g : ℕ) (hg : g < 12) :
    ProofFile.Sk.skel (the_block Z G P g) = k5SkelW g := by
  obtain ⟨-, h2, h3⟩ := k5_row_plans places plan hB hb
  obtain ⟨-, r, o, -, bf⟩ := h2 g hg
  unfold ProofFile.Sk.skel
  rw [r, o, told_the_block, bf, h3 g hg]
  rfl

/-- **THE LOT's SKELETON IS THE WRITTEN ONE.** -/
theorem k5_lot_skel (places : H2K5.k5Places G = (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g))
    (plan : ∀ g, g < 12 → G.W.A[g]? = some (P g)) (hB : ∀ g, g < 12 → k5LotB (P g) = true)
    (hb : ∀ g, g < 12 → H2K5.k5Before? Z ("A" ++ toString g) = some [(1, 4 + 6 * g)]) :
    ProofFile.Sk.lotSk G (H2K5.lotN Z) =
      { name := "K5: the attention segments' own rounds", letters := false, still := [], blocks := (List.range 12).map k5SkelW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } := by
  have hbl : ((H2K5.lotN Z).blocks G).map ProofFile.Sk.skel = (List.range 12).map k5SkelW := by
    show (([] : List (Block S ProofFile.Cl)) ++ H2K5.k5OwnN Z G).map ProofFile.Sk.skel = _
    rw [List.nil_append, (k5_row_plans places plan hB hb).1, List.map_map]
    exact List.map_congr_left fun g hg => skel_the_block places plan hB hb g (List.mem_range.1 hg)
  unfold ProofFile.Sk.lotSk
  rw [hbl]
  rfl

end H2K5.Row

#print axioms H2K5.Row.told_the_block
#print axioms H2K5.Row.skel_the_block
#print axioms H2K5.Row.k5_lot_skel
