-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyShows.lean: which rounds of a chain of stages send a tree, and what it means that
a view shows these trees: definitions.

In the written link each code switch of a chain of stages (OnBytes/Slice/ManyDefs.lean: `Chain`)
sends one tree. Nothing in `Chain` says so: it is asked as `Chain.Trees`. The written protocol's
view holds a list of opened columns, each with a key and a position. The trees' keys are their
numbers in the order of sending.

Main definitions.
 `Chain.Trees`       the first round of each code switch sends a tree, and no other round of a fold
                     or a code switch does.
 `Chain.ShowsFrom`   every entry of a view's list under the key n, n + 1, ... holds the column of
                     the first, second, ... code switch's tree at the entry's position.
Not claimed. No theorem is in this file.

-/
import OnBytes.Slice.ManyDefs
import OnBytes.Slice.BlkSeat

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

namespace Chain

/-- Which rounds send a tree: the first round of each code switch, and no other round of a fold or
of a code switch (of the last switch's second round too, which `TreesOK` of
OnBytes/Slice/SemLib.lean does not ask). Nothing is asked of the base case's two rounds. -/
def Trees : {s : Sg} → Chain s → Prop
  | _, .last _ _ _ _ _ _ _ => True
  | _, .step _ _ _ _ _ dE dT dS dC _ _ _ _ _ next =>
    dE.tree.isSome = false ∧ dT.tree.isSome = false ∧ dS.tree.isSome = true ∧
      dC.tree.isSome = false ∧ next.Trees

/-- Every entry of the view's list under the key n holds the column of the first code switch's tree
at the entry's position, every entry under n + 1 that of the second, and so on. -/
def ShowsFrom (V : Fmt.View) : {s : Sg} → (c : Chain s) → ℕ → c.Bl → Prop
  | _, .last _ _ _ _ _ _ _ => fun _ _ => True
  | _, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun n b =>
    Shows V n (treeCol dS b.2.1.1) ∧ next.ShowsFrom V (n + 1) b.2.2

end Chain

end OnBytes.Slice
