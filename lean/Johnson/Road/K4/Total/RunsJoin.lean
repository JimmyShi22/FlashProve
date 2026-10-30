-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RunsJoin.lean: THE JOINING: THE LAW "BEHIND K4's HEARING ITS TWO RUNS OF
CLAIMS RETURN" (`RunsReturn`, Total/Returns.lean) OUT OF ITS PARTS. One statement with its proof;
two small lemmas.

  `list_mapM_some`, `range_mapM_some`: a map in Option over a list | over the numbers below n
    returns where each member's value is there.
  **`runs_return_of`**: `FrontSkel`, `FrontPub` and `RunPub` give `RunsReturn`: the other parts are
    called as they are proved (`shown_part` · `readyV_part` · `apart_part`: WindowsFit.lean;
    `back_part`: BackReturns.lean). THE WALK: the end values are shown · the row products'
    sumcheck's own claim is made (marks; its window free) · that lays its window alone: the leaves'
    window, which lies below, is still free: the leaves' own claim is made · the listing `front`
    returns, by the skeleton and the member, and with it the three claims on the planes · "back"
    returns at the ledger in hand, and at the ledger that "front" leaves: the merge's window lies
    behind both others.

Limits. `FrontSkel`, `FrontPub`, `RunPub` ARE PREMISES HERE (their proofs: the files on the
listings). All premises of the law stand as in its statement: the member among them. K04_law, the
law of K4's block itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Total.WindowsFit
import Johnson.Desc.First.K4.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.PscRun (Sized Filled Later hideRun_keeps)
open OnBytes.Desc.First.K4.Slots (SameAt InWin win_same formsFront_same)

/-- A map in Option over a list returns where each member's value is there. -/
theorem list_mapM_some {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b) → ∃ r, l.mapM f = some r
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨r, hr⟩ := list_mapM_some f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: r, ?_⟩
    rw [List.mapM_cons, hb, hr]
    rfl

/-- The like over the numbers below n, as an array. -/
theorem range_mapM_some {β : Type} (f : ℕ → Option β) (n : ℕ) (h : ∀ i, i < n → ∃ b, f i = some b) :
    ∃ r, (Array.range n).mapM f = some r := by
  obtain ⟨r, hr⟩ := list_mapM_some f (Array.range n).toList fun a ha => h a (by simpa using ha)
  refine ⟨r.toArray, ?_⟩
  rw [Array.mapM_eq_mapM_toList, hr]
  rfl

/-- **The law, out of its parts.** -/
theorem runs_return_of (hK : FrontSkel) (hP : FrontPub) (hR : RunPub) : RunsReturn := by
  intro rows P Pr P₀ hp g fo F G Fb t u o o₀ h hy hr A L
  obtain ⟨efo, a1, a2⟩ := apart_part P hp g fo F G t u o A.sized h
  have below : o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next := by
    rw [efo]
    exact A.leavesBelow
  obtain ⟨sh, hsh⟩ := range_mapM_some (fun i => Fb.shown (o.H.tV.sEnd + i)) (4 * P.y.NI)
    (shown_part P hp g fo F G Fb t u o A.sized h L.later L.sized)
  obtain ⟨Ga, ha⟩ := ownClaim_returns (readyV_part P hp g fo F G t u o h)
    (rowsSummand P.y o.H sh) {} L.sized L.winV
  obtain ⟨_, _, ra⟩ := ownClaim_some ha
  obtain ⟨sa, _, qa⟩ := win_same L.sized ra
  obtain ⟨a₀, b₀, hm⟩ := A.member
  have hfr : ∀ a b, (front rows P g o a b).isSome = true := fun a b => by
    rw [hK rows P g o o₀ a b a₀ b₀ A.skel, ← hP rows P P₀ g o₀ a₀ b₀ A.y₀ A.rd₀]
    exact hm
  obtain ⟨l0, hl0⟩ := Option.isSome_iff_exists.mp (hfr {} {})
  obtain ⟨_, _, _, _, _, pp, _, _, _, _, _, _, hpp, _⟩ := front_some hl0
  have wl : WinFree o.H.fo.leaves Ga := fun i hi =>
    ⟨by rw [(hideRun_keeps ra).ns]; exact (L.winL i hi).1, fun hf =>
      (L.winL i hi).2 ((qa _ (by unfold InWin; omega)).1.mp hf)⟩
  obtain ⟨Gb, hb⟩ := ownClaim_returns (p := o.H.fo.leaves) (by rw [efo]; exact A.leavesReady) oneE
    pp.1 sa wl
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp
    (hfr (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {}) (o.H.fo.leaves.rowForm oneE pp.1))
  have hfront : formsFrontWith rows P g o Fb = some (l.toArray,
      (if rows then Gb.paid o.H.fo.owedObjects else Gb).paid o.H.fo.owedPlanes) := by
    unfold formsFrontWith
    simp only [hsh, ha, hpp, hb, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨s1, _, q1⟩ := formsFront_same L.sized hfront
  have hlat : Later Fb ((if rows then Gb.paid o.H.fo.owedObjects else Gb).paid o.H.fo.owedPlanes) :=
    formsFrontWith_later hfront
  have wm : WinFree o.wo.toWsMerged.p
      ((if rows then Gb.paid o.H.fo.owedObjects else Gb).paid o.H.fo.owedPlanes) := fun i hi =>
    ⟨by rw [hlat.ns]; exact (L.winM i hi).1, fun hf =>
      (L.winM i hi).2 ((q1 _ (by unfold InWin; omega) (by unfold InWin; omega)).1.mp hf)⟩
  rw [hR rows P Pr g o Fb hy hr]
  exact ⟨⟨_, _, hfront, back_part P hp g fo F G _ t u o h s1 wm⟩,
    back_part P hp g fo F G Fb t u o h L.sized L.winM⟩

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.runs_return_of
