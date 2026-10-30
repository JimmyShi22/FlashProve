-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Entry.lean: THE BATCHING IS HANDED THE ENTRY OF THE PLACE's OWN FIRST WRITTEN
ROUND. Statements and proofs.

`k12_step_accH` (Johnson/Desc/K12/Law/TopH.lean) has the entry at which `First.Close.bat` returned
under "there is". The batching's guard "the entry counts the batched rows" is the one tie between
the plan and the number of the group's rows: so which entry it is matters to whoever prices the
round.

  `batJ_entry`: a yes of the batching's part: `bat` returned at the first of the cut's entries.
  `layW_head`: the first written round has the first declared round's entry.
  `k12_bat_entry`: a yes of the block's decision: `bat` returned, on the first round shown, AT THE
    ENTRY OF THE FIRST OF `writtenOf π.nums`.
The proofs follow `batJ_ok` (Law/Top.lean) and `k12_guards` (Law/TopH.lean) line by line.
A tool.
-/
import Johnson.Desc.K12.Law.TopH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.FoldLaw (bind_ok)
open H2K.Pub (writtenOf WR layW)

theorem batJ_entry (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) :
    ∃ (e : Fmt.Entry) (es : List Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout)
      (S' : Statement), cut.map (·.entry) = e :: es ∧ rs = [r] ∧
      First.Close.bat t.st t.g e r = .ok (row, L, S') := by
  unfold batJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨⟨row, L⟩, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, hr0, _, _⟩ := back_ok h
    unfold H2K.batE at hx
    split at hx
    · rename_i e es r rs' he1 hr1
      obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨⟨row', L', S'⟩, hb, hx⟩ := bind_ok hx
      cases hx
      have hrs : rs = r :: rs' := hr1
      have hrs' : rs' = [] := hr0
      subst hrs'
      exact ⟨e, es, r, row', L', S', he1, hrs, mapError_ok hb⟩
    · cases hx
  · cases h

theorem layW_head : ∀ (ds : List Fmt.DeclaredRound) (sh : List Fmt.Shape) (w0 : WR) (l : List WR),
    layW ds sh = some (w0 :: l) → ∃ d0 ds', ds = d0 :: ds' ∧ w0.entry = d0.entry
  | [], [], _, _, h => by cases h
  | [], _ :: _, _, _, h => by cases h
  | d :: ds, sh, w0, l, h => by
    refine ⟨d, ds, rfl, ?_⟩
    unfold layW at h
    split at h
    · cases h
    · split at h
      · obtain ⟨x, _, hx⟩ := Option.map_eq_some_iff.1 h
        rw [← (List.cons.inj hx).1]
      · split at h
        · split at h
          · obtain ⟨x, _, hx⟩ := Option.map_eq_some_iff.1 h
            rw [← (List.cons.inj hx).1]
          · cases h
        · cases h

/-- **The batching returned at the place's own first written round's entry.** -/
theorem k12_bat_entry (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (w0 : WR) (l : List WR)
    (hw : writtenOf p.nums = some (w0 :: l)) :
    ∃ (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
      rs.take 1 = [r] ∧ First.Close.bat t0.st t0.g w0.entry r = .ok (row, L, S') := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, _, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨first', rest', ds', e1', e2', l1, _⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts p hp
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
  obtain ⟨hfr', _, _⟩ := frontK_ok p _ _ _ _ hfr
  have hF : tF = t0 := by
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  have nB : (batAt guardedProximityTestParts p (ds'.zip p.oracles) : Blk').rounds.length = 1 := by
    show (((ds'.zip p.oracles).take 1).map (·.1)).length = 1
    rw [List.length_map, l1]
  rw [nB] at hbat
  obtain ⟨hbat', _, _⟩ := batK_ok p _ _ _ _ _ hbat
  obtain ⟨e, es, r, row, L, S', hc, hr1, hb⟩ := batJ_entry p _ _ _ _ _ hbat'
  have hw' : layW ds' (p.nums.sent.zipIdx.map fun t => (p.nums.own t.1.1 t.1.2
      (p.nums.free + t.2)).1) = some (w0 :: l) := by
    unfold writtenOf at hw
    rw [e2] at hw
    exact hw
  obtain ⟨d0, ds'', rfl, hd0⟩ := layW_head _ _ _ _ hw'
  have he : e = d0.entry := by
    cases ho : p.oracles with
    | nil =>
      rw [ho] at l1
      simp at l1
    | cons o os =>
      rw [ho] at hc
      have hc' : [d0.entry] = e :: es := hc
      exact (List.cons.inj hc').1.symm
  rw [he, ← hd0] at hb
  exact ⟨r, row, L, S', hr1, hb⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_bat_entry
