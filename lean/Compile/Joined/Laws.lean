-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Joined/Laws.lean: the annotation of a file with three joined hash chains has the properties
that the compiler's soundness theorem asks of an annotation.

A twin beside the library's construction: a second form of the compiler's verifier side, beside the
library's own. It is made for a key file's and a proof file's three hash chains,
joined by seals; that it writes what is hashed as the prover's files have it is not shown in this
folder.


Compile/Joined/Types.lean lays three chains in a row as one batch protocol, with the annotation
`Chains.ann`: front and chain 1 local, the joining round, chain 2 shared, seam and chain 3 local.

Main names:
  `Chains.ann_coherent`   the annotation is coherent, if the joining round's is
  `Chains.ann_localTo`    the front and chain 1 are local: every round up to number n, for every n
                          up to the number of chain 1's rounds behind the front
  `coherent_app`, `coherent_const`   the same for two annotations in a row, and for one rule of
                          annotation in every round

Limits: nothing on the verifier of a file (`Desc`): that its decision depends on the oracles only
where it reads is a property of the description.

Terms: lean/GLOSSARY.md.

-/
import Compile.Joined.Types

set_option autoImplicit false

namespace Compile.Joined
open Iop

/-- two coherent annotations in a row -/
theorem coherent_app : ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t},
    A.Coherent → B.Coherent → (RoundSplits.app A B).Coherent
  | [], _, _, _, _, hB => hB
  | _ :: _, _, (_, _), _, hA, hB => ⟨hA.1, coherent_app hA.2 hB⟩

/-- one rule of annotation in every round -/
theorem coherent_const (f : ∀ r : Round, RAnn r) (hf : ∀ r, (f r).Coherent) :
    ∀ s : Shape, (RoundSplits.const f s).Coherent
  | [] => trivial
  | r :: s => ⟨hf r, coherent_const f hf s⟩

/-- local rounds before what follows: every round up to number n, for n below their number -/
theorem localTo_app {t : Shape} (B : RoundSplits t) :
    ∀ (s : Shape) (n : ℕ), n < s.length → RoundSplits.LocalTo n (s ++ t) (RoundSplits.app (RoundSplits.allLocal s) B)
  | _ :: _, 0, _ => rfl
  | _ :: s, n + 1, h => ⟨rfl, localTo_app B s n (Nat.lt_of_succ_lt_succ h)⟩

namespace Chains
variable (G : Chains)

theorem ann₃_coherent : G.ann₃.Coherent :=
  coherent_const _ (fun r => RAnn.ofSlot_coherent _ r) G.sh₃

theorem annJ_coherent (h : G.Laws) : G.annJ.Coherent :=
  ⟨h.cohJ, coherent_app (coherent_const _ (fun r => RAnn.ofShared_coherent _ r) G.s₂)
    G.ann₃_coherent⟩

/-- The annotation of a file is coherent, if the joining round's is. -/
theorem ann_coherent (h : G.Laws) : G.ann.Coherent :=
  ⟨RAnn.ofSlot_coherent _ _,
    coherent_app (coherent_const _ (fun r => RAnn.ofSlot_coherent _ r) G.s₁) (G.annJ_coherent h)⟩

/-- The front and chain 1 are local rounds. -/
theorem ann_localTo : ∀ n, n ≤ G.s₁.length → RoundSplits.LocalTo n G.sh G.ann
  | 0, _ => rfl
  | n + 1, h => ⟨rfl, localTo_app G.annJ G.s₁ n h⟩

end Chains

end Compile.Joined
