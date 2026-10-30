-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumGood.lean: the sumcheck of Cb/Ld/LdSum.lean as one step of a composed protocol. In this
library's terms: the zero-knowledge sumcheck as a block of a chain. `Spec.ld_sum_good_of_know`
states, under the hypotheses of its statement, all items of the record `IOR.GoodT` but knowledge
soundness. Knowledge soundness enters as a hypothesis here. It is, under its own hypotheses, stated
in Cb/Ld/LdSumKnow.lean (`Spec.ld_sum_know`) and proved in Cb/Ld/LdSumKnowProofs.lean.
Cb/Ld/LdSumMain.lean puts the two together.

Notation: `e`: a radius, counted in long positions (`LdCode.Near`, Cb/Ld/LdRel.lean); `t`: the
number in `Y.Cw.Zk t` and `Y.nums t ..`; `Lst`, `mC`, `mS`, `mW`: functions ℕ → ℕ, the arguments of
`Y.err` and `Y.nums` (Cb/Ld/LdSum.lean); `ext`: a function from input, transcript and output witness
to an input witness.

The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
`C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native words
to long words, are linear over E; the encoder sends only the zero message with zero randomness to
zero; and, for every long position x, any two native words that agree at the native positions
`C.src x` have the same long symbol at x. Here they are premises of `Spec.ld_sum_good_of_know`, of
`Y.C`, `Y.Z` and `Y.Zw`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec

/-- Under the hypotheses below, from knowledge soundness to the record: strings (`point`), locality
(`isLocal`), perfect completeness, honest-verifier exact zero knowledge (`GoodT.exact`:
`Honest.Exact`, Ior/Honest.lean) are proved; nothing is withheld (`Honest.withheld`,
Ior/Honest.lean). -/
def ld_sum_good_of_know : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (Y : SumPar E P) (e t : ℕ) (Lst mC mS mW : ℕ → ℕ)
      (ext : Y.Xi × Y.Cin.ext.Str → Tr Y.ior.shape → Y.Cout.N.Wit → Y.Cin.N.Wit),
    2 ≤ Y.n → Y.PackOK → Y.C.Laws → Y.Z.Laws → Y.Zw.Laws → Y.Cw.Zk t →
    Y.ior.red.Know (fun _ => True) (ConL Y.Cin.N e Y.slIn.Holds) (ConL Y.Cout.N e Y.slOut.Holds)
      ext (Y.err Lst mC mS mW) →
    IOR.GoodT Y.ior Y.hon (Y.Cin.rels Y.slIn e fun _ => ()) (Y.Cout.rels Y.slOut e fun _ => ())
      ext (Y.nums t Lst mC mS mW)

/-- The counts: k + 1 rounds; the verifier reads nothing; a symbol of the new oracles is computed
from one symbol of the input and from the native symbols of the fresh mask behind its position. -/
def ld_sum_counts : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P),
    Y.ior.shape.length = Y.k + 1 ∧
    (∀ ρ, Y.ior.extReads ρ = ∅ ∧ Y.ior.reads ρ = ∅) ∧
    ∀ ρ x, (Y.ior.srcE ρ x).card = 1 ∧ (Y.ior.srcO ρ x).card = (Y.srcW x).card

end Spec

theorem ld_sum_good_of_know : Spec.ld_sum_good_of_know := by
  intro E P _ _ _ Y e t Lst mC mS mW ext hn hP hC hZ hW hZk hK
  exact
    { point := ld_sum_point E P Y
      isLocal := ld_sum_local E P Y hC hZ hW
      acc := ld_sum_acc E P Y hn hP hC hZ hW
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun _ _ _ _ => rfl
      prBad := prRho_empty _ fun _ h => h
      cover := fun _ _ _ h => h
      prCov := fun _ => prRho_empty _ fun _ h => h
      know := hK
      exact := ld_sum_exact E P Y t hn hZk }

theorem ld_sum_counts : Spec.ld_sum_counts := by
  intro E P _ Y
  refine ⟨?_, fun _ => ⟨rfl, rfl⟩, fun _ x => ⟨Finset.card_singleton x, Finset.card_map _⟩⟩
  show (Y.round0 :: List.replicate Y.k (sRound E Y.Ch Y.n)).length = _
  simp

end Cb
