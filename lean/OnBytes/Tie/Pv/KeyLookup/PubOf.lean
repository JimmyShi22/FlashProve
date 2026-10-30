-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/PubOf.lean: the map from the program's public inputs of a lookup
(Lkp.Public, OnBytes/Iop/Lkp.lean) to the record of public numbers and shapes of
Cb/Pv/KeyLookup/Letters.lean (Pub).

It is a file of its own, with two imports, so that every comparison with the program takes the same
map. Both functions can be evaluated.

Main definitions.
  runOf p    a run of padding without its row.
  pubOf S    the parts, d, mu, the number of real planes (S.planes), the runs of padding, the first
             run's row (0 if there is no run), and S.lastKeyLevelOrder.

Limits. Nothing is proved here. The map does not read readFrom, keys, tables, h, g, shifted, or the
rows of the later runs (whether all runs hold one row is not read here).

-/
import OnBytes.Iop.Lkp
import Cb.Pv.KeyLookup.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open OnBytes

/-- A run of padding without its row. -/
def runOf (p : Lkp.Padding) : Run := ⟨p.part, p.first, p.logStep, p.length⟩

/-- The record made of the program's public inputs. -/
def pubOf (S : Lkp.Public) : Pub where
  parts := S.parts
  d := S.d
  mu := S.mu
  pl := S.planes
  runs := S.padding.map runOf
  padRow := (S.padding.head?.map (·.row)).getD 0
  order := S.lastKeyLevelOrder

end Lk6
