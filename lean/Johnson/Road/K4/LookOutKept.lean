-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/LookOutKept.lean: THE LOOKUP's PROMISE BEHIND ITS PLACE RIDES OVER A YES OF K4's
BLOCK. `k3OnOut p s` (Johnson/Desc/First/Look/K3Borders.lean) is the table of joints' Bool
of thirteen tests that is promised behind a lookup's place "and at every border from there up to the
front of the link's batching". AND THE NEXT LOOKUP's PROMISE IN FRONT, `k3OnIn`, HOLDS BEHIND A YES
OF K4's BLOCK UNDER THREE NAMED PREMISES. Statements and proofs.

  **`k3OnOut_kept`**: where `(blockAtS q).decide s rs cols = .ok s'` and `k3OnOut p s = true`, there
    `k3OnOut p s' = true`: AT EVERY PLACE p OF A LOOKUP, on the calls or on the digits. NO FURTHER
    PREMISE.
How. Ten of the thirteen read the place and what was heard at the seat, which K4's yes leaves
(`Rest.lookHeard`, `Rest.tl`). "The ledger's count is at least behind the lookup's slots": the count
does not fall (`Later.next`). "The ledger's arrays have its size": `Later.sized`. "THE SLOTS OF THE
SUMCHECK OVER THE LEAVES ARE STILL FREE": `Fresh` (Slots/HearSpares.lean): the stretch ends at or
below the end of the lookup's own slots (the eleventh test), which lies at or below the ledger's
count in front of K4 (the seventh), and K4's hearing turns nothing below that count.

  **`k3OnIn_behind`**: `k3OnIn p s' = true` behind a yes of K4's block, at a place p with a shape h,
    IF (hd) nothing is heard at p's seat in front of K4; (hr) in front of K4 the ledger's arrays
    have its size and THE LOOKUP's `elems h` SLOTS FROM p.first ON ARE INSIDE ITS ROOM AND FREE;
    (hn) the ledger's count behind K4 is p.first. K4 MAKES NONE OF THE THREE: it keeps (hd) and
    hands (hr) on (`Fresh`: nothing turns from the count behind on); that no rows are owed behind
    its yes is its own (`KeptAtS`). (hn): `hear_next` (Slots/RunsSpare.lean) has the count behind
    as the merge's first slot + 2 lk + 3; that this is p.first is the plan's matter.

  `getD_any`: inside an array the default of `getD` is idle. `sized_iff`: `sizedB` says `Sized`.
  `freeB_fresh`: a stretch that is free in F, and ends at or below F.next or begins at G.next or
    behind it, is free in G, if `Fresh F G`, G has as many slots as F and both have arrays of the
    right sizes.

  `k3OnOut_of_kept`, `k3OnIn_of_kept`: the two from `KeptAtS q s s'` (KeptAtS.lean) in the place of
    the block's yes: for whoever has a yes in another form (`kept_of_yes`, KeptOfYes.lean).

Limits. ONE DIRECTION, FROM A YES OF THE BLOCK: on K4's runs of claims nothing here. AT THE CALLS
`k3OnOut` READS THE RECORD's FIELD lookHeard; K4's BLOCK AND ITS RUNS READ fo: that the two hold one
value is not said here; nor that the window which "front" lays is the stretch that the ninth test
keeps free. In the chain's order `k3OnOut_kept` has something to say at the calls' place,
`k3OnIn_behind` at the digits': at the other seat the premise is met by no run, by reading. That
`k3OnOut` holds in front of K4 is a premise. THE THREE PREMISES OF `k3OnIn_behind` ARE PAID NOWHERE
HERE (of hn `hear_count`, Johnson/Road/K4/HearCount.lean, has a part). Nothing on
soundness.
-/
import Johnson.Road.K4.KeptAtS
import Johnson.Desc.First.Look.K3Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled Later)
open OnBytes.Desc.First.K4 (Par blockAtS Rest)
open OnBytes.Desc.First.K4.Slots (Fresh)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (k3OnOut k3OnIn heardAt sizedB freeB)

/-- Inside an array the default is idle. -/
theorem getD_any {A : Array Bool} {x : ℕ} (h : x < A.size) (b c : Bool) :
    A.getD x b = A.getD x c := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- `sizedB` says `Sized`. -/
theorem sized_iff (G : Fork) : sizedB G = true ↔ PscRun.Sized G := by
  unfold sizedB PscRun.Sized
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- **A free stretch below the count in front, or from the count behind on, stays free.** -/
theorem freeB_fresh {F G : Fork} {first n : ℕ} (hF : PscRun.Sized F) (hG : PscRun.Sized G)
    (hn : G.ns = F.ns) (hf : Fresh F G) (hb : first + n ≤ F.next ∨ G.next ≤ first)
    (h : freeB F first n = true) : freeB G first n = true := by
  unfold freeB at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by omega, fun j hj => ?_⟩
  have xF : first + j < F.gotF.size := by
    rw [hF.2.2]
    omega
  have xG : first + j < G.gotF.size := by
    rw [hG.2.2]
    omega
  have a : ¬ Filled F (first + j) := by
    unfold Filled
    rw [getD_any xF false true, h2 j hj]
    exact Bool.false_ne_true
  have b : ¬ Filled G (first + j) := fun e => a ((hf.same (first + j) (by omega)).1.mp e)
  unfold Filled at b
  rw [getD_any xG true false]
  exact eq_false_of_ne_true b

/-- The lookup's promise rides from s to s' wherever `KeptAtS q s s'`. -/
theorem k3OnOut_of_kept {q : Par} {s s' : S} (K : KeptAtS q s s')
    (p : VerifiableInference.Desc.First.Look.P) (ho : k3OnOut p s = true) :
    k3OnOut p s' = true := by
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _, _, _, _, hR, _, hS, _⟩ := K
  have hf : s.fork? = some a.F := by simp [S.fork?, ha]
  have hh : heardAt p.digits s' = heardAt p.digits s := by
    unfold heardAt
    rw [hR.tl, hR.lookHeard]
  unfold k3OnOut at ho ⊢
  rw [hh, h3]
  rw [hf] at ho
  cases hs : p.shape with
  | none => simp [hs] at ho
  | some hp =>
    cases hg : heardAt p.digits s with
    | none => simp [hs, hg] at ho
    | some g =>
      simp only [hs, hg, Bool.and_eq_true] at ho ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ := ho
      have sF : PscRun.Sized a.F := (sized_iff _).mp c8
      have sG : PscRun.Sized G := hL.sized sF
      have n7 := of_decide_eq_true c7
      have n11 := of_decide_eq_true c11
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, ?_⟩, ?_⟩, ?_⟩, c10⟩, c11⟩, c12⟩, c13⟩
      · exact decide_eq_true (Nat.le_trans n7 hL.next)
      · exact (sized_iff _).mpr sG
      · exact freeB_fresh sF sG hL.ns (hS sF).2 (Or.inl (Nat.le_trans n11 n7)) c9

/-- **The lookup's promise rides over a yes of K4's block.** -/
theorem k3OnOut_kept {q : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS q).decide s rs cols = .ok s')
    (p : VerifiableInference.Desc.First.Look.P) (ho : k3OnOut p s = true) :
    k3OnOut p s' = true :=
  k3OnOut_of_kept (kept_atS h) p ho

/-- At a place with a shape (hs), under hd, hr, hn: the next lookup's promise in front holds at s'
wherever `KeptAtS q s s'`. -/
theorem k3OnIn_of_kept {q : Par} {s s' : S} (K : KeptAtS q s s')
    (p : VerifiableInference.Desc.First.Look.P) {hp : Forest.Shape} (hs : p.shape = some hp)
    (hd : heardAt p.digits s = none)
    (hr : ∀ F, s.fork? = some F → sizedB F = true ∧ freeB F p.first (Forest.elems hp) = true)
    (hn : ∀ G, s'.fork? = some G → G.next = p.first) : k3OnIn p s' = true := by
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _, _, h7, _, hR, _, hS, _⟩ := K
  have hf : s.fork? = some a.F := by simp [S.fork?, ha]
  have hh : heardAt p.digits s' = heardAt p.digits s := by
    unfold heardAt
    rw [hR.tl, hR.lookHeard]
  obtain ⟨r1, r2⟩ := hr a.F hf
  have sF : PscRun.Sized a.F := (sized_iff _).mp r1
  have sG : PscRun.Sized G := hL.sized sF
  have e : G.next = p.first := hn G h3
  have f : freeB G p.first (Forest.elems hp) = true :=
    freeB_fresh sF sG hL.ns (hS sF).2 (Or.inr (Nat.le_of_eq e)) r2
  unfold k3OnIn
  rw [hs, hh, hd, h7, h3]
  simp [VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits, e, (sized_iff G).mpr sG, f]

/-- **AT A PLACE WITH A SHAPE (hs), UNDER hd, hr, hn: the next lookup's promise in front holds
behind a yes of K4's block.** -/
theorem k3OnIn_behind {q : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS q).decide s rs cols = .ok s')
    (p : VerifiableInference.Desc.First.Look.P) {hp : Forest.Shape} (hs : p.shape = some hp)
    (hd : heardAt p.digits s = none)
    (hr : ∀ F, s.fork? = some F → sizedB F = true ∧ freeB F p.first (Forest.elems hp) = true)
    (hn : ∀ G, s'.fork? = some G → G.next = p.first) : k3OnIn p s' = true :=
  k3OnIn_of_kept (kept_atS h) p hs hd hr hn

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.freeB_fresh
#print axioms OnBytes.Road.K4.k3OnOut_kept
#print axioms OnBytes.Road.K4.k3OnIn_behind
