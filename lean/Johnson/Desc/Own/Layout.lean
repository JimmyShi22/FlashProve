-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Layout.lean: the layout of a group of oracle messages, as a named part of the
description, for every block that begins a proximity test.

A proximity test reads the members of a group together: each member's main rows and mask rows get a
block of rows in the group's two tables. The layout says where each block begins and how many row
variables the tables have. Definitions with code; no theorem here.
Main names:
  `blockBits S G part`: for each member, in the order of sending: the number of bits that index its
    rows in the table `part`, if it has such rows; nothing if it has none, and nothing in the main
    table for a kept member, whose main rows have no place among the group's rows.
  `layoutOf S G`: the layout of the group G: the blocks of both tables laid by decreasing size from
    row 0 on; h the bits of the mask rows taken, k the bits of the main rows taken, at least h and
    at least 1; the message lengths' logarithms of the group's two codes; the members and their kept
    marks as the group has them. It always returns.
  `layoutCan S g`: the group number g is there.
  `layoutMade S g`: the layout of group number g, or nothing where `layoutCan` says no.
Every place at which layoutMade returns nothing, and what that refusal checks: one place: the
statement has no group number g. It checks that the number names a group of the statement, and
nothing else: nothing on the group's members, codes or rows is tested.
How far the text is its own: it is the hand-written program's Statement.layout
(OnBytes/Iop/Ground.lean) taken over token for token under new names, cut into three definitions,
but for the test whether a table is there, which is `tableThere` (Johnson/Desc/Own/Rows.lean) where
the program calls Statement.has. It adds no second, independent eye on what a layout should be.
Statement.layout is called nowhere.
What is taken from the hand-written program's files: the records Statement, Group, GroupLayout,
Codes and Code with their fields, the type Part, and five functions that always return:
Statement.rowBits, layBlocks, ceilLog2, Code.logEll and the number noId. No function of these files
that says yes or no, or that may return nothing, is called.
That `layoutMade` is the program's Statement.layout, at all arguments, is proved beside, in
Johnson/Desc/Own/LayoutAgree.lean, which no block imports.
Limits: Whether this layout is the right one for a test is not said here. No soundness is claimed,
and nothing is said on hiding.

-/
import Johnson.Desc.Own.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- For each member: the bits that index its rows in the table, if it has a block there. -/
def blockBits (S : OnBytes.Statement) (G : OnBytes.Group) (part : OnBytes.Part) :
    Array (Option Nat) :=
  (Array.range G.members.size).map fun i =>
    let o := G.members.getD i OnBytes.noId
    if tableThere S o part && !(part == .main && G.kept.getD i false) then
      some (S.rowBits o part)
    else none

/-- The layout of a group. -/
def layoutOf (S : OnBytes.Statement) (G : OnBytes.Group) : OnBytes.GroupLayout :=
  let mask := OnBytes.layBlocks (blockBits S G .mask)
  let main := OnBytes.layBlocks (blockBits S G .main)
  let h := OnBytes.ceilLog2 mask.2
  { k := max (max (OnBytes.ceilLog2 main.2) h) 1, h := h,
    logEll := (S.codes.base.getD G.code default).logEll,
    logEllZk := (S.codes.mask.getD G.maskCode default).logEll,
    members := G.members, kept := G.kept, mainFirst := main.1, maskFirst := mask.1 }

/-- The group is there. -/
def layoutCan (S : OnBytes.Statement) (g : Nat) : Bool := decide (g < S.groups.size)

/-- The layout of group number g, or nothing where the group is not there. -/
def layoutMade (S : OnBytes.Statement) (g : Nat) : Option OnBytes.GroupLayout :=
  (S.groups[g]?).map (layoutOf S)

end VerifiableInference.Desc.Own
