-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/MadeSpelled.lean: the eight strings of what the planner configures
(`OnBytes.Params.Configured`, OnBytes/Params/Configure.lean) as a function of its four other fields,
the shapes and the digest; and that `configure` spells just these.

What it is for. Johnson/G/MadeFree.lean parts a `Configured` into four fields that do not hang on
the digest of the public files (`Free`) and eight strings that do (`Hung`). Where the four stand as
written data, the eight are still to be made: the digest is known at a run alone, and the parameter
bytes of a proof's first chain hold three things of the run's shapes.
`spelled` makes them,
by the text of the last lines of `configure`.

All that is here are tools: they hold for all lines, shapes, digests and bits, and name no file and
no value.

Definitions.
  `spelled W x cfg`: the eight strings: the digest; and for each of the seven chains
    `Fmt.paramsBytes` of its plan, the digest and its items. It reads W's seven plans, W's sizes,
    and of the shapes x the layout, the links' identifiers and the number of pending rows. Where W
    has not three plans for the proof file and three for the key file it gives eight empty strings
    (`Hung.none`); that the readers of parameter bytes refuse these is not shown here.
Statements and proofs.
  `sized_lines`: what `sized` returns holds the lines that it was given. `sized_rows`: and the
    shapes' two numbers of rows of the matrix were the same.
  `configure_hung`: if `configure l x cfg bits` returns M, then M is `(freeOf M).at (spelled (freeOf
    M) x cfg)`.
  `configure_kept`: and four conditions on the shapes held: one identifier for each link, one notice
    at the start, a pending row, one plain scalar in the last link alone.

What of OnBytes/Model/ is used: nothing.

Limits. One way: from a `configure` that returns. Nothing says that `spelled` at a written W is what
any run hashes. The other tests of `configure` and of `sized` are not kept here. Nothing on
soundness.
-/
import Johnson.G.MadeFree
import OnBytes.Plan.PlanListsConfigure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.MadeFree
open OnBytes OnBytes.Params

/-- The eight strings, by the text of the last lines of `configure`. -/
def spelled (W : Free) (x : Shapes) (cfg : ByteArray) : Hung :=
  match W.proof, W.key with
  | [first, shared, second], [oneTime, keyShared, keySecond] =>
    let z := W.sized
    let lin := fun (codes : Codes) (S : LinShape) =>
      [("codes", spellCodes codes), ("the test on the table", spellLin S)]
    { configuration := cfg,
      keyOneTime := Fmt.paramsBytes oneTime.plan cfg (Plan.oneTimeItems z.key),
      keyShared := Fmt.paramsBytes keyShared.plan cfg (lin z.key.codes z.key.once.shape),
      keySecond := Fmt.paramsBytes keySecond.plan cfg [],
      entryLink := Fmt.paramsBytes W.entry.plan cfg
        [("codes", spellCodes z.entryCodes), ("the link", spellLink z.link.shape)],
      first := Fmt.paramsBytes first.plan cfg
        (lin z.proof.codes z.proof.batch.shape ++
         [("request's shape", spellReq z.proof.request), ("layout", spellLayout x.layout),
          ("links' identifiers", spellWords x.identifiers),
          ("pending rows", spellWord x.sub.pendingRows),
          ("binding tree", spellBinding ⟨clog2 z.lines.slots, z.set.saltBytes⟩)]),
      shared := Fmt.paramsBytes shared.plan cfg (lin z.proof.codes z.proof.batch.shape),
      second := Fmt.paramsBytes second.plan cfg [] }
  | _, _ => Hung.none

/-- What `sized` returns holds the lines that it was given. -/
theorem sized_lines {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    z.lines = l := by
  unfold sized at h
  extract_lets at h
  replace h := exc_guard h
  obtain ⟨proof, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨key, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  rfl

/-- Where `sized` returns, the shapes' two numbers of rows of the matrix are the same. -/
theorem sized_rows {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    ¬ (x.sub.matrixRows != x.ranges.matrixRows) = true := by
  unfold sized at h
  extract_lets at h
  exact exc_guard_not h

/-- **What `configure` returns is its four fields with the eight strings spelled of them.** -/
theorem configure_hung {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {M : Configured}
    (h : configure l x cfg bits = .ok M) : M = (freeOf M).at (spelled (freeOf M) x cfg) := by
  have hl : M.sized.lines = l := sized_lines (configure_plans h).1
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨P1, _, h⟩ := exc_bind h
  obtain ⟨P2, _, h⟩ := exc_bind h
  obtain ⟨P3, _, h⟩ := exc_bind h
  obtain ⟨entry, _, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    have hl' : z.lines = l := hl
    subst hl'
    rfl
  · cases h

/-- **Four conditions on the shapes that `configure` asked.** -/
theorem configure_kept {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {M : Configured}
    (h : configure l x cfg bits = .ok M) :
    ¬ (x.identifiers.length != M.sized.proof.request.link.length ||
        M.sized.proof.request.atStart.length != 1 || x.sub.pendingRows == 0 ||
        M.sized.proof.request.link.map (·.plain) !=
          List.replicate (M.sized.proof.request.link.length - 1) 0 ++ [1]) = true := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨P1, _, h⟩ := exc_bind h
  obtain ⟨P2, _, h⟩ := exc_bind h
  obtain ⟨P3, _, h⟩ := exc_bind h
  obtain ⟨entry, _, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    have hk := exc_guard_not h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    exact hk
  · cases h

end Johnson.G.MadeFree

#print axioms Johnson.G.MadeFree.sized_lines
#print axioms Johnson.G.MadeFree.sized_rows
#print axioms Johnson.G.MadeFree.configure_hung
#print axioms Johnson.G.MadeFree.configure_kept
