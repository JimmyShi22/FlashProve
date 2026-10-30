-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/FileLaw.lean: the value of `Johnson.G.OfPlan.fileOf` (Johnson/G/RoundsOfPlan.lean)
from its seven steps' values: three calls of `treesSent`, three of `fill`, and the search for a tree
that is opened nowhere.

  **`fileOf_of`**: general in the file's name, the shape, the three plans, the three chains'
    sendings and the two functions `first` and `input`: so it is a law on `declKOf` and on
    `declPOf`, which are `fileOf` at other arguments. Calls alone.

Limits. THE SEVEN VALUES ARE PREMISES. No closed fact. Nothing on soundness.

-/
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Params Johnson.G Johnson.G.OfPlan

/-- **`fileOf`'s value, from its steps' values.** -/
theorem fileOf_of {file : String} {S : LinShape} {P0 P1 P2 : Fmt.Plan} {c0 c1 c2 : ChainSends}
    {first : List (Sent × Nat) → List Fmt.Entry → List (List Told)} {input : Sent → Bool}
    {t0 t1 t2 : List (Sent × Nat)} {d0 d1 d2 : List Fmt.DeclaredRound}
    (h0 : treesSent s!"{file}, first chain" c0 P0 [] = .ok t0)
    (h1 : treesSent s!"{file}, shared chain" c1 P1 (ownMasks c1.codes S P1.rounds) = .ok t1)
    (h2 : treesSent s!"{file}, second chain" c2 P2 [] = .ok t2)
    (f0 : fill s!"{file}, first chain" P0.rounds (noStored (first t0 P0.rounds)) = .ok d0)
    (f1 : fill s!"{file}, shared chain" P1.rounds (sharedOpens S t1) = .ok d1)
    (f2 : fill s!"{file}, second chain" P2.rounds (noStored (secondOpens S input t0 t1 t2)) =
      .ok d2)
    (hT : (([t0, t1, t2].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).find?
      fun x => !(toldIn (d0, d1, d2)).contains x) = none) :
    fileOf file S P0 P1 P2 c0 c1 c2 first input = .ok (d0, d1, d2) := by
  unfold fileOf
  simp only [h0, h1, h2, f0, f1, f2, bind, Except.bind, hT, pure, Except.pure]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.fileOf_of
