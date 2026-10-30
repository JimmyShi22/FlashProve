-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Peel.lean: the soundness of a written protocol is proved block by block, each block
from the library's theorem on the block that it follows.

The library proves round-by-round knowledge soundness of a reduction K from statements A to
statements B (`Iop.Reduction.Know`). A written protocol has rounds s, which follow K's rounds in
other types, and then rounds t. This file has the step that takes the first rounds off.

`peel`. Let a be a statement of K, in the set `on` for which K's theorem holds, without a witness.
Let F carry the rounds s to K's rounds (OnBytes/Slice/Carry.lean). To show that the prover has lost
in s ++ t towards a goal, it is enough to show that it has lost in t alone, after every transcript
of s
 - that has no image, or
 - whose image leads K's verifier to refuse, or to a statement b that has no witness either.
So the claim "no witness" passes from block to block. What the user of `peel` has to show of the
written verifier is that the values which it holds after s are K's output statement. The error
counts are K's, each times its round's number w (OnBytes/Slice/Carry.lean), and then those of t.
`peel_last` is the same step where nothing follows.

Main theorems: `peel`, `peel_last`.
Not claimed. Nothing on any one protocol: block, maps and the rounds that follow are variables.
-/
import OnBytes.Slice.Carry
import Ior.Know

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob

variable {A B WA WB : Type}

/-- **One block is taken off the front.** -/
theorem peel (K : Reduction A B) {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape} (hK : K.Know on RA RB ext ε)
    (a : A) (ha : on a) (hno : ∀ w, ¬ RA a w)
    {s t : Shape} (F : Carry s K.shape) (ws : Err s) (hF : F.Fib ws) (ε₂ : Err t)
    (bad : Tr (s ++ t) → Prop)
    (h0 : ∀ τ, F.tr τ = none → Doomed t ε₂ fun b => bad (Tr.app τ b))
    (hT : ∀ τ τ', F.tr τ = some τ' → (∀ b w, K.out a τ' = some b → ¬ RB b w) →
      Doomed t ε₂ fun b => bad (Tr.app τ b)) :
    Doomed (s ++ t) (Err.app (mulErr s K.shape ws ε) ε₂) bad :=
  Doomed.append s t _ ε₂ bad
    (Carry.doomed F ws hF ε _
      (fun τ' => ∀ b w, K.out a τ' = some b → RB b w → RA a (ext a τ' w)) h0
      (fun τ τ' hτ hb => hT τ τ' hτ fun b w hout hw => hno _ (hb b w hout hw)) (hK a ha))

/-- **The last block.** -/
theorem peel_last (K : Reduction A B) {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape} (hK : K.Know on RA RB ext ε)
    (a : A) (ha : on a) (hno : ∀ w, ¬ RA a w)
    {s : Shape} (F : Carry s K.shape) (ws : Err s) (hF : F.Fib ws) (bad : Tr s → Prop)
    (h0 : ∀ τ, F.tr τ = none → bad τ)
    (hT : ∀ τ τ', F.tr τ = some τ' → (∀ b w, K.out a τ' = some b → ¬ RB b w) → bad τ) :
    Doomed s (mulErr s K.shape ws ε) bad :=
  Carry.doomed F ws hF ε _
    (fun τ' => ∀ b w, K.out a τ' = some b → RB b w → RA a (ext a τ' w)) h0
    (fun τ τ' hτ hb => hT τ τ' hτ fun b w hout hw => hno _ (hb b w hout hw)) (hK a ha)

end OnBytes.Slice

#print axioms OnBytes.Slice.peel
#print axioms OnBytes.Slice.peel_last
