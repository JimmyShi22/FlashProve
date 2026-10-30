-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/FitFull.lean: from a yes of `configure`, `entrySized` on the same lines returns what
`configure` has made for the entry's chain; and the sizes of a key's test on the table.


OnBytes/Model/ReadBackMade.lean proves that the plan which a chain's reader returns is the plan that
`configure` has made, where the made plan fits the format's words (`Fmt.Plan.fit`); that file's head
says why that condition does not follow from a yes of `configure` alone. The entry's made plan
depends on the lines alone, so that at one set of lines the condition on it is a closed statement;
the other six plans depend on the shapes as well. OnBytes/Model/FitRecord.lean settles it for the
entry's chain at `recordLines`. From a yes of `configure`, `entrySized` on the same lines returns
the entry's made plan (`configure_entrySized`). The second part is for the second of a key's three
plans, which reads the setting and the key's test on the table alone: what `Plan.keySized` returns
has as that test what `keyOnce` returns (`keySized_once`). `keyOnce` is `Plan.keySized` up to the
proof of the ranges, without its refusal of no mask rows.









Main definitions: `keyMaskRows`, `keyOnce`.
Main theorems: `configure_entrySized`, `keySized_once`.

What is not claimed: that `configure` says yes at any lines: that is a hypothesis. Nothing on
whether any of the seven plans fits. `keyOnce` can answer where `Plan.keySized` refuses. Its codes
are not the key's, which come after the proof of the ranges, so that nothing is prepared for a
key's one-time and shared plans. `keySized_once` is used by no theorem here. For proofs only; the
program, that is the Lean port built from OnBytes/, does not import this file.






-/
import OnBytes.Model.ReadBackMade
import OnBytes.Params.EntrySizedLaws
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions

set_option autoImplicit false

namespace OnBytes.Params

/-- From `configure`'s yes: `entrySized` on the same lines returns the link's sizes, the entry's
codes and the entry's plan that `configure` has made. -/
theorem configure_entrySized {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    entrySized l = .ok (made.sized.link, made.sized.entryCodes, made.entry) := by
  obtain ⟨hz, _, _, _, _, _, _, _, _, he⟩ := configure_plans h
  obtain ⟨hs, T, hT, hl⟩ := sized_link hz
  rw [hs] at he
  unfold entrySized
  dsimp only
  rw [hT]
  show (orRefuse (linkSized (settingOf l) l T {}) >>= fun y =>
    finishHeld (settingOf l) .once (linkPlan y.1) >>= fun p =>
      (pure (y.1, y.2, p) : Except String (LinkSized × Codes × Planned))) = _
  rw [hl]
  show (finishHeld (settingOf l) .once (linkPlan made.sized.link) >>= fun p =>
    (pure (made.sized.link, made.sized.entryCodes, p) :
      Except String (LinkSized × Codes × Planned))) = _
  rw [he]
  rfl

/-! ## A key's second plan -/

/-- The mask rows of the index-mask message, in the words of `Plan.keySized`. -/
def keyMaskRows (l : Lines) (L : Plan.RangesLines) : Nat :=
  Send.maskRowsFor (Wf.indexMaskEntries
    { lookups := L.lookups, message := default, messageId := L.messageId, stages := [],
      choice := ⟨true⟩ } ⟨L.kCol, L.matrixRows⟩) (2 ^ l.onceOwn.maskLogL) l.answers

/-- The sizes of a key's test on the table, without the proof of the ranges: `Plan.keySized` up to
`Plan.rangesSized`, but for its refusal where there are no mask rows. -/
def keyOnce (l : Lines) (shape : Plan.Shape) : Option (LinSized × Codes) := do
  let T ← deriveTable (settingOf l) l
  let L ← Plan.rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart
  linSized (settingOf l) (linLines l L.matrixRows (keyMaskRows l L) true) T {}

/-- What `Plan.keySized` returns has the lines' setting, and its test on the table is `keyOnce`'s.
-/
theorem keySized_once {l : Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) :
    z.set = settingOf l ∧ ∃ codes, keyOnce l shape = some (z.once, codes) := by
  unfold Plan.keySized at h
  extract_lets s at h
  obtain ⟨T, hT, h⟩ := opt_bind h
  obtain ⟨L, hL, h⟩ := opt_bind h
  extract_lets count rows at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, _, h⟩ := opt_bind h
  cases h
  refine ⟨rfl, c1, ?_⟩
  unfold keyOnce
  rw [hT]
  show ((Plan.rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart).bind
    fun L => linSized (settingOf l) (linLines l L.matrixRows (keyMaskRows l L) true) T {}) = _
  rw [hL]
  exact ho

end OnBytes.Params

#print axioms OnBytes.Params.keySized_once
#print axioms OnBytes.Params.configure_entrySized
