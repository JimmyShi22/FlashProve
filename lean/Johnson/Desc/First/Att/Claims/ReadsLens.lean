-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsLens.lean: kind K5: at the seven reads of ours among the ten at
which tablesP asks no length (theTen, Johnson/Desc/First/Att/Claims/ReadsReturn.lean): on which
lengths it hangs that the weights are as many as the cells, and which of these lengths the kind's
own tests already give.

Main names:
  `theSeven`, `fitSeven`: the ten without the lookup's three; the test at them.
  `Lens7 g lk p`: eight facts on lengths. `fitSeven_of`: Lens7 g lk p → fitSeven g p lk = true.
  `points_lens`: what pointsOf (Johnson/Desc/First/Att/Points.lean) gives by its own tests and text:
    ziW and ziX have lt coordinates, zcW has ldh; ti is a cut of the drawn point.
  `own_forces`: where pointsOf returns p and placeOk says yes: T = 2^lt; ziX has lt coordinates; the
    lookup's point has lt + ldh coordinates at least.
  `index_forced`: so the rows at the division's index point have T weights: by our own tests alone.
  `keys_forced`: the scores' planes at the lookup's point have 2^lmS weights, by our own tests and
    one fact of the plan: lmS ≤ lt + ldh.
What is left, and on what it hangs (no theorem here): the drawn point's, the key's and the bits'
sumchecks' points (Lens7.ti, key, cells) and the two value products' points (ptM, ptD) hang on the
lengths of what was heard: a law of the hearing, no test of the claims' text.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsRows
import Johnson.Desc.First.Att.Claims.ReadsReturn

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo LookIn Pts Read Heard Left)

/-- The seven of the ten that are not the lookup's. -/
def theSeven : List Read :=
  [.planesAtKeys, .planesAtBelow, .planesAtOn, .rowsAtIndex, .rowsAtDrawn, .rowsAtKey, .rowsAtBits]

/-- The test fit at these seven. -/
def fitSeven (g : Geo) (p : Pts) (lk : LookIn) : Bool :=
  theSeven.all fun r => ((r.of g lk p).2.array g).size == (r.of g lk p).2.len g

/-- The lengths on which the seven hang. -/
structure Lens7 (g : Geo) (lk : LookIn) (p : Pts) : Prop where
  T : g.T = 2 ^ g.lt
  zx : g.lmS ≤ lk.zx.size
  ptM : g.lmS ≤ (P.pointM g p.d).size
  ptD : g.lmS ≤ (P.pointD g p.d).size
  ziX : p.d.ziX.size = g.lt
  ti : p.x.ti.size = g.lt
  key : 2 * g.lt + g.lgk ≤ p.x.scd.r.size
  cells : g.lt ≤ p.x.scH.r.size

theorem lastN_size (z : Array E) (n : ℕ) (h : n ≤ z.size) : (P.lastN z n).size = 2 ^ n := by
  unfold P.lastN
  rw [eqTab_size, lastCoords_size _ _ h]

theorem fitSeven_of {g : Geo} {lk : LookIn} {p : Pts} (H : Lens7 g lk p) : fitSeven g p lk = true := by
  unfold fitSeven theSeven
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  refine ⟨lastN_size _ _ H.zx, lastN_size _ _ H.ptM, lastN_size _ _ H.ptD, ?_, ?_, ?_, ?_⟩
  · show (P.eqTab p.d.ziX).size = g.T
    rw [eqTab_size, H.ziX, H.T]
  · show (P.eqTab p.x.ti).size = g.T
    rw [eqTab_size, H.ti, H.T]
  · show (P.eqTab (p.x.pi g)).size = g.T
    have e : (p.x.pi g).size = g.lt := by
      unfold P.MaxP.pi
      rw [Array.size_extract]
      have := H.key
      omega
    rw [eqTab_size, e, H.T]
  · show (P.eqTab (p.x.ri2 g)).size = g.T
    have e : (p.x.ri2 g).size = g.lt := by
      unfold P.MaxP.ri2
      rw [Array.size_extract]
      have := H.cells
      omega
    rw [eqTab_size, e, H.T]

/-- What pointsOf gives by its own tests and text. -/
theorem points_lens {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) :
    p.d.ziW.size = g.lt ∧ p.d.ziX.size = g.lt ∧ p.d.zcW.size = g.ldh ∧
      p.x.ti = h.point.extract g.lgk (g.lgk + g.lt) := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, a, _, uW, _, uX, _, uH, _, _, _, _, hz, e⟩ := hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  subst e
  refine ⟨?_, ?_, ?_, rfl⟩
  · show (Array.extract _ _ _).size = _
    rw [Array.size_extract, hz.1.1]
    omega
  · show (Array.extract _ _ _).size = _
    rw [Array.size_extract, hz.1.2]
    omega
  · show (Array.extract _ _ _).size = _
    rw [Array.size_extract, hz.1.1]
    omega

/-- **What the kind's own tests give of the eight lengths.** -/
theorem own_forces {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {zk : Array (Array E)} {h : Heard}
    {L : Left} {p : Pts} (hp : P.pointsOf g zk h L = some p) (hok : placeOk g mats nW lk p = true) :
    g.T = 2 ^ g.lt ∧ p.d.ziX.size = g.lt ∧ g.lt + g.ldh ≤ lk.zx.size := by
  obtain ⟨zW, zX, zc, _⟩ := points_lens hp
  have f := forced hok .rowsAtDivide (by simp [P.reads]) (by simp [theTen])
  have f' : (P.eqTab p.d.ziW).size = g.T := f
  rw [eqTab_size, zW] at f'
  refine ⟨f'.symm, zX, ?_⟩
  unfold placeOk at hok
  simp only [Bool.and_eq_true] at hok
  have m := hok.1.1.1.1.2
  unfold P.mergedTokens at m
  simp only [Bool.and_eq_true] at m
  have e := congrArg Array.size (eq_of_beq m.2)
  unfold P.lastCoords at e
  rw [Array.size_append, Array.size_extract, zW, zc] at e
  omega

/-- **The rows at the division's index point: T weights, by our own tests alone.** -/
theorem index_forced {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {zk : Array (Array E)} {h : Heard}
    {L : Left} {p : Pts} (hp : P.pointsOf g zk h L = some p) (hok : placeOk g mats nW lk p = true) :
    (((Read.rowsAtIndex).of g lk p).2.array g).size = ((Read.rowsAtIndex).of g lk p).2.len g := by
  obtain ⟨hT, zX, _⟩ := own_forces hp hok
  show (P.eqTab p.d.ziX).size = g.T
  rw [eqTab_size, zX, hT]

/-- **The scores' planes at the lookup's point: 2^lmS weights, by our own tests and one fact of the plan.** -/
theorem keys_forced {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {zk : Array (Array E)} {h : Heard}
    {L : Left} {p : Pts} (hp : P.pointsOf g zk h L = some p) (hok : placeOk g mats nW lk p = true)
    (hplan : g.lmS ≤ g.lt + g.ldh) :
    (((Read.planesAtKeys).of g lk p).2.array g).size = ((Read.planesAtKeys).of g lk p).2.len g :=
  lastN_size _ _ (le_trans hplan (own_forces hp hok).2.2)

end K5Law
