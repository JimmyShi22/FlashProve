-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/KeysTie.lean: the honest side of the kind "lookup" (K3). The
keys of the specification's data, at what `askOf` yields on the calls of a group's layers, are the
joint vector of `keysG`. Theorems.

Terms. Honest/K3/GLOSSARY.md ("ask", "seated filling", "specification"). In this file: the
specification's data at a run (`dataAt`, Honest/K3/JobsSpec.lean) take their keys off the structure
w that the row is given: key x := up (w.key p.theta 0 x). `keysG` is defined in
Honest/K3/Law/KeysAreKvG.lean.

What is shown.
  `up_is_inE`, `up_is_gl`: the reading `up` (JobsSpec.lean) is `inE` (Honest/K3/Wit.lean), and it is
    the library's `Reading.gl`.
  `dataAt_key_layers`: the key number x of `dataAt N w p`, where w is what `askOf` yields at
    `.layers g` over `tiedOwnSources`, the seated filling, is
    `jointKey fo (keysG ...) (up p.theta) x`.
  `dataAt_key_own`: the same over `ownSources`.
All four are without hypotheses: they hold for all public numbers N, points p, inputs t, challenges
heard and shapes.

How the proof goes. The two theorems on keys are `askLayers_tied` and `askLayers_key`
(KeysAreKvG.lean).

Users. `left_at_layers` (Honest/K3/Law/Thread/LeftAtCalls.lean) calls `dataAt_key_layers`.

Limits. The keys alone: nothing is said on the data's bits, numbers or alpha. The layers' calls
alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.KeysAreKvG
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)
open OnBytes.Ends (jointKey)

/-- The two readings of the program's elements are one. -/
theorem up_is_inE (x : E) : ProofFile.Honest.K3.up x = inE x := rfl

/-- It is the library's `Reading.gl`. -/
theorem up_is_gl (x : E) : ProofFile.Honest.K3.up x = OnBytes.Model.Reading.gl.val x := rfl

section
variable {P W₀ Rc Xi Tr' : Type}

/-- **The keys of the specification's data at the seated filling's structure on the calls of group
g's layers.** -/
theorem dataAt_key_layers (N : KE → TwV.Nums P KE) (X : OnBytes.Model.Verify.Public)
    (cells : Tr' → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) (g : ℕ) (t : Local W₀ Rc Xi Tr')
    (heard : List Fmt.Drawn) (p : Pts) (x : ℕ) :
    (dataAt N (askOf (tiedOwnSources X cells weights req) (.layers g) t heard) p).key x =
      jointKey X.layers.y.fo (keysG X (cells t.trace) (weights t.w₀) g)
        (ProofFile.Honest.K3.up p.theta) x :=
  askLayers_tied X cells weights req g t heard p.theta 0 x

/-- The same over `ownSources`. -/
theorem dataAt_key_own (N : KE → TwV.Nums P KE) (X : OnBytes.Model.Verify.Public)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (g : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) (p : Pts) (x : ℕ) :
    (dataAt N (askOf (ownSources X cells weights pubH) (.layers g) t heard) p).key x =
      jointKey X.layers.y.fo (keysG X (cells t.trace) (weights t.w₀) g)
        (ProofFile.Honest.K3.up p.theta) x :=
  askLayers_key X cells weights pubH g t heard p.theta 0 x

end

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.up_is_inE
#print axioms ProofFile.Honest.K3.up_is_gl
#print axioms ProofFile.Honest.K3.dataAt_key_layers
#print axioms ProofFile.Honest.K3.dataAt_key_own
