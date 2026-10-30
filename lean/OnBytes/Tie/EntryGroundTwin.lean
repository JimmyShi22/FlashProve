-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryGroundTwin.lean: what OnBytes/Tie/EntryTwin.lean says from main, at any ground of
OnBytes/Tie/EntryGround.lean.

At any ground, from main's 0: the plain check with nothing pinned (`checkAskR`), and the twin of
`Entry.check`, asking, return at the oracle on bit strings made from the format's hash the table
that `Entry.check` returned.

Not claimed. Values alone; at the unpatched oracle; the entry's check alone; no part; nothing on
soundness. What the head of OnBytes/Tie/EntryTwin.lean says of the twin holds here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryGround
import OnBytes.Tie.EntryTwin

set_option autoImplicit false

namespace OnBytes.Tie.EntryGround

open OnBytes.Shell (World)
open OnBytes.TwoPort

variable (G : EntryGround)

/-- At any ground. Under `ZeroFacts` and `SaysLines`, at c := the digest of the three
configuration files as read: `checkAskR`, at the function that the oracle on bit strings made from
the format's hash induces, on the ground's bytes at c, the table that `Key.check` returned and the
entry file's bytes, returns the table that `Entry.check` returned. (`zero_record_ask`'s proof over
the ground.) -/
theorem zero_ask {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : G.SaysLines w.r.pol) :
    checkAskR (Run.oB (Run.oBits ()))
      (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table w.ent =
        some w.further := by
  have hc32 := Params.configurationDigest_size [w.r.pol, w.lay, w.r.KL]
  have eb := zero_entry_bytes h (G.saysLines_bytes hs w.lay w.r.KL)
  have hy : Entry.check (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = .ok w.further := by
    rw [← eb]
    exact h.entryYes
  rw [checkAskR_oBits]
  refine (entry_check_askR _ _ w.table w.further w.ent (G.read_at _ hc32) hc32
    (zero_table_root h) ?_).2 hy
  intro P hP hokP
  obtain ⟨_, ⟨rs2, h2, eP⟩, _⟩ := entryPlaceR_spec_any hP
  obtain rfl : G.rs = rs2 := Option.some.inj ((G.rounds_at _).symm.trans h2)
  rw [eP] at hokP ⊢
  exact smallFX_of_withinX _ hokP (G.within_at _ hc32 _ (specX_base _ hokP)) w.ent
    (zero_entry_small h)

/-- At any ground: the twin's `Entry.check`, asking, run at that oracle on the same three, returns
the table that `Entry.check` returned. One fixed oracle, unpatched. `SaysLines` is proved of no
file; no file is shown a yes. -/
theorem zero_twin_asks {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : G.SaysLines w.r.pol) :
    (M.Entry.check (Fmt.HM Run.askB)
      (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table w.ent).det
        (Run.oBits ()) = .ok w.further := by
  have e := (twin_check_det (Run.oBits ()) _ w.table w.ent).trans (G.zero_ask h hs)
  cases hx : (M.Entry.check (Fmt.HM Run.askB)
      (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table w.ent).det
        (Run.oBits ()) with
  | error r =>
    rw [hx] at e
    cases e
  | ok t =>
    rw [hx] at e
    exact congrArg Except.ok (Option.some.inj e)

end OnBytes.Tie.EntryGround
