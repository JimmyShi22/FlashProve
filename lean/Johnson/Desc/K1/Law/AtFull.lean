-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/AtFull.lean: the two tests of Links.lean and Opens.lean hold at the written shape of
a request at the full size (Johnson/Desc/ReqLit/Full.lean: shapeFull), by evaluation in Lean's kernel;
so eighty-one places of a proof file's first chain stand on their written records.
  links_full, opens_full     decide +kernel
  full_links                 shapeFull has 25 links
  full_switches              the last group's test has five switches; the chain has 82 records
  k01_sits_first_chain       for every parameters q with the written codes and the written shape:
      the first segment's opening is PlaceOk at record 0; the later moment m (1 or 2) of link l < 25
      at record 3 l + m; every place with the written codes that announces the code switch into
      group l (1 to 25) at record 3 l; every such place that announces the j-th switch of the last
      group's test at record 76 + j.

What is not claimed. That the description's own parameters have the written codes and the written
shape: a run says so (in a file that is not in this library; the written shape's own guard). That the
description's block
at a place IS the kind's block at these parameters. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.Opens
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc.ReqLit (shapeFull)

theorem links_full : linksTest shapeFull = true := by decide +kernel

theorem opens_full : opensTest shapeFull = true := by decide +kernel

theorem full_links : shapeFull.link.length = 25 := by decide +kernel

/-- The last group's test has five code switches; and the first chain has 82 written records: 76 of the
links and the last group's opening, these five, and W's. -/
theorem full_switches : (switchesOf shapeFull.answers shapeFull.last).length = 5 ∧
    (sentOf 2 0).length = 82 := by decide +kernel

/-- **Eighty-one places of a proof file's first chain on their written records.** -/
theorem k01_sits_first_chain (q : Params.First) (gp : GPar) (hc : q.codes = codesFull2)
    (hs : q.shape = shapeFull) :
    PlaceOk 2 0 0 (firstPar q gp) ∧
      (∀ l piece m, l < 25 → (m = 1 ∨ m = 2) → PlaceOk 2 0 (3 * l + m) (parLater q gp l piece m)) ∧
      (∀ (P : Par) (l : Nat), P.codes = codesFull2 → P.sent.toList = openSent shapeFull l → 1 ≤ l →
        l ≤ 25 → PlaceOk 2 0 (3 * l) P) ∧
      ∀ (P : Par) (j : Nat) (s : List OracleNotice), P.codes = codesFull2 → P.sent.toList = s →
        (switchesOf shapeFull.answers shapeFull.last)[j]? = some s → PlaceOk 2 0 (76 + j) P := by
  refine ⟨k01_first links_full q gp hc hs, fun l piece m hl hm => ?_, fun P l h1 h2 h3 h4 => ?_,
    fun P j s h1 h2 h3 => ?_⟩
  · exact k01_later links_full q gp hc hs l piece m (by rw [full_links]; exact hl) hm
  · exact k01_open opens_full P l h1 h2 h3 (by rw [full_links]; exact h4)
  · have := k01_last links_full P j s h1 h2 h3
    rw [full_links] at this
    exact this

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.links_full
#print axioms VerifiableInference.Desc.K1.opens_full
#print axioms VerifiableInference.Desc.K1.full_switches
#print axioms VerifiableInference.Desc.K1.k01_sits_first_chain
