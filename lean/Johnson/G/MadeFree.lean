-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/MadeFree.lean: the four fields of what the planner configures
(`OnBytes.Params.Configured`, OnBytes/Params/Configure.lean) that do not hang on the digest of the
public files, as a record of their own, with a map back into `Configured`.

`Configured` has twelve fields. Eight are strings of bytes that hold the digest of the public files:
the digest itself and the parameter bytes of the seven chains. Four do not: the sizes, the proof
file's plans, the key file's plans, the entry file's plan. Where the plan is to stand as written
data, only the four can be written. A `Configured` with eight empty strings in the other places
could be misread, because texts of the library read these strings: a test that a chain's parameter
bytes are shorter than 2 ^ 64 (Johnson/Flat/PlanDepthZero.lean) would say yes idly, and the reading
back of the seven strings (`chainsOf_made`, Johnson/G/PlansPriced.lean) would refuse. A record that
lacks them cannot be misread. The public tests on the plans read the four alone, so at `W.at h` they
have one and the same value for every h, by unfolding.

All that is here are tools: definitions, and equations by unfolding. They name no file and no value.

Definitions.
  `Free`: the four fields. `Hung`: the eight. `Free.at W h`: the `Configured` of both.
  `freeOf c`, `hungOf c`: the two parts of a `Configured`. `Hung.none`: eight empty strings, for an
    evaluation.
Statements, all by unfolding.
  `at_free`, `free_at`, `hung_at`: the two parts make the whole, and back.
  `madeOk_at`, `fitOk_at`: `Desc.madeOk` (Johnson/Desc/MadeOk.lean) and `Desc.fitOk`
    (Johnson/Desc/FitOk.lean) at `W.at h` do not hang on h.
  `madeOk_free`, `fitOk_free`: so at a `Configured` c they have their values at `(freeOf c).at
    Hung.none`.

What of OnBytes/Model/ is used: nothing.

Limits. That the four fields do not hang on the digest is the reason for the record's name; of the
planner's routine it is shown by no theorem here. Of other tests on a `Configured` nothing is said
here: each wants its own line. Nothing on soundness.
-/
import Johnson.Desc.MadeOk
import Johnson.Desc.FitOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.MadeFree
open OnBytes.Params VerifiableInference

/-- The four fields of `Configured` that do not hang on the digest of the public files. -/
structure Free where
  sized : Sized
  /-- the plans of a proof's three chains -/
  proof : List Planned
  /-- the plans of a key's three chains -/
  key : List Planned
  /-- the plan of an entry's chain -/
  entry : Planned

/-- The eight that do: the digest, and the parameter bytes of the seven chains. -/
structure Hung where
  configuration : ByteArray
  keyOneTime : ByteArray
  keyShared : ByteArray
  keySecond : ByteArray
  entryLink : ByteArray
  first : ByteArray
  shared : ByteArray
  second : ByteArray

/-- The `Configured` of the two parts. -/
def Free.at (W : Free) (h : Hung) : Configured :=
  { sized := W.sized, configuration := h.configuration, proof := W.proof, key := W.key,
    entry := W.entry, keyOneTime := h.keyOneTime, keyShared := h.keyShared,
    keySecond := h.keySecond, entryLink := h.entryLink, first := h.first, shared := h.shared,
    second := h.second }

/-- The four fields of a `Configured`. -/
def freeOf (c : Configured) : Free := ⟨c.sized, c.proof, c.key, c.entry⟩

/-- The eight others. -/
def hungOf (c : Configured) : Hung :=
  ⟨c.configuration, c.keyOneTime, c.keyShared, c.keySecond, c.entryLink, c.first, c.shared,
    c.second⟩

/-- Eight empty strings: for an evaluation of a test that reads none of them. -/
def Hung.none : Hung := ⟨.empty, .empty, .empty, .empty, .empty, .empty, .empty, .empty⟩

theorem at_free (c : Configured) : (freeOf c).at (hungOf c) = c := rfl

theorem free_at (W : Free) (h : Hung) : freeOf (W.at h) = W := rfl

theorem hung_at (W : Free) (h : Hung) : hungOf (W.at h) = h := rfl

/-- The public test on the prices does not hang on the eight. -/
theorem madeOk_at (W : Free) (h h' : Hung) : Desc.madeOk (W.at h) = Desc.madeOk (W.at h') := rfl

/-- The public test on the format's words does not hang on the eight. -/
theorem fitOk_at (W : Free) (h h' : Hung) : Desc.fitOk (W.at h) = Desc.fitOk (W.at h') := rfl

theorem madeOk_free (c : Configured) : Desc.madeOk c = Desc.madeOk ((freeOf c).at Hung.none) :=
  madeOk_at (freeOf c) (hungOf c) Hung.none

theorem fitOk_free (c : Configured) : Desc.fitOk c = Desc.fitOk ((freeOf c).at Hung.none) :=
  fitOk_at (freeOf c) (hungOf c) Hung.none

end Johnson.G.MadeFree

#print axioms Johnson.G.MadeFree.at_free
#print axioms Johnson.G.MadeFree.free_at
#print axioms Johnson.G.MadeFree.hung_at
#print axioms Johnson.G.MadeFree.madeOk_at
#print axioms Johnson.G.MadeFree.fitOk_at
#print axioms Johnson.G.MadeFree.madeOk_free
#print axioms Johnson.G.MadeFree.fitOk_free
