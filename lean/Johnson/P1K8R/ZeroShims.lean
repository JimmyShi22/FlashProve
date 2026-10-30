-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroShims.lean: THREE TOOLS FOR `KeepsZero` (Johnson/P1K8R/ZeroFrame.lean) IN THE
SHAPES OF THE LIBRARY's TOOLS FOR KeepsLooks (keeps_of_cases, keeps_same, keeps_puts:
Johnson/Desc/First/Link/Law/LooksWalk.lean), SO THAT A PROOF WRITTEN FOR THE ARRAYS' LOOKS PASSES TO
THE ROWS' FIRST COLUMNS UNTURNED. Lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding.

  `kzL_of_cases`   `kz_of_cases` with the link's context handed along: where a ledger is open a link
      is (link_of_fork, Johnson/LPFK9R/SlotsSize.lean)
  `kzL_same`, `kzL_puts`   `kz_same`, `kz_puts` (Johnson/P1K8R/ZeroWalk.lean) with the premises on
      the link's number that the library's tools take; THESE PREMISES ARE NOT USED
Why. `KeepsZero` does not read the link's number; the library's walk for the looks does.
Limits. Nothing on any sub-protocol.

-/
import Johnson.P1K8R.ZeroWalk
import Johnson.LPFK9R.SlotsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- The library's keeps_of_cases' shape: the link's context is handed to h and not used. -/
theorem kzL_of_cases {s s' : S}
    (h : ∀ G' L', s'.fork? = some G' → s'.link? = some L' → AllZero G' ∨
      ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ L.link = L'.link ∧
        G'.trees.map l0s = G.trees.map l0s) : KeepsZero s s' := by
  refine kz_of_cases fun G' hG => ?_
  obtain ⟨L', hL'⟩ := link_of_fork hG
  rcases h G' L' hG hL' with h1 | ⟨G, _, e1, _, _, e4⟩
  · exact Or.inl h1
  · exact Or.inr ⟨G, e1, e4⟩

/-- The library's keeps_same's shape. -/
theorem kzL_same {s s' : S} (hf : s'.fork? = s.fork?)
    (_hl : s'.link?.map (·.link) = s.link?.map (·.link)) : KeepsZero s s' := kz_same hf

/-- The library's keeps_puts' shape. -/
theorem kzL_puts {s u : S} {L0 L : LinkCtx} {F0 F : Fork} (_hL : s.link? = some L0)
    (hF : s.fork? = some F0) (uL : u.link? = some L0) (uF : u.fork? = some F0)
    (_el : L.link = L0.link) (ef : F.trees.map l0s = F0.trees.map l0s) :
    KeepsZero s ((u.putLink L).putFork F) := kz_puts hF uL uF ef

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kzL_of_cases
#print axioms VerifiableInference.Desc.LinkJoin.kzL_same
#print axioms VerifiableInference.Desc.LinkJoin.kzL_puts
