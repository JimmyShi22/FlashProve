-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BatNoKept.lean: the row that the batching of a proximity test returns has no
form on a kept member, where the group's layout has no kept member. Statements and proofs.

No premise on the batched rows is needed. The counts on the batching's converse (`BadDraws`,
Johnson/Desc/K12/Law/BatJoint.lean) ask `row.kept = #[]` inside the counted set; the set that a user
of these counts has in hand (the batching returns a row that has a witness) does not hold that
conjunct. With `bat_noKept` the conjunct is proved, not asked.
Main names:
  `combine_noKept0`: `Bat.combine S g input x = some out`, and no member of `input.layout` is kept:
    then `out.kept = #[]`. `combine_noKept` (OnBytes/Slice/BlkNoKept.lean) says the same where every
    row meets `RowFits`; its own step `addToGroupRow_noKept` asks no such thing, so here the fold is
    walked directly.
  `bat_noKept`: `Good F a row D`, `Made p t a L D`, and the batching's plain text returns `(rowB, L,
    S')`: then `rowB.kept = #[]`. `Good`'s clause `kept` is of `D.L`; `Made`'s clause `lay` says
    `D.L = L`.
Limits: It speaks of a layout without kept members alone. No soundness is claimed, and nothing is
said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import OnBytes.Slice.BlkNoKept
import Johnson.Desc.K12.Law.BatMeans
import Johnson.Desc.K12.Law.FirstOkLaw

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.ClaimSays
open H2K.First (Plain Good Made)

theorem combine_noKept0 (S : Statement) (g : ℕ) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out)
    (hL : ∀ i, input.layout.kept.getD i false = false) : out.kept = #[] := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s, hs, h2⟩ := h
  have e1 := OnBytes.foldlM_keeps (fun s : GroupRow × Row × E => s.1.kept) _
    (fun r b b' hb => by
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hb
      obtain ⟨acc, ha, rfl⟩ := hb
      exact addToGroupRow_noKept S input.layout hL _ _ _ _ ha) _ _ _ hs
  rw [addToGroupRow_noKept S input.layout hL _ _ _ _ h2]
  exact e1

theorem bat_noKept {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S S' : Statement) (g : ℕ)
    (en : Fmt.Entry) (r : Fmt.RoundView) (rowB : GroupRow)
    (hb : First.Close.bat S g en r = .ok (rowB, L, S')) : rowB.kept = #[] := by
  obtain ⟨G, x, _, _, _, _, hc⟩ := bat_ok _ _ _ _ _ _ _ hb
  refine combine_noKept0 _ _ _ _ _ hc fun i => ?_
  show L.kept.getD i false = false
  rw [← hm.lay]
  exact h.kept i

end H2K.Pin

#print axioms H2K.Pin.combine_noKept0
#print axioms H2K.Pin.bat_noKept
