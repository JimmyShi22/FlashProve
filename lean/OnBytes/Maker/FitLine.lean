-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/FitLine.lean: the data of a whole file, made from three lists of rounds
(OnBytes/Three/Data.lean, `Whole.of`; OnBytes/Maker/WholeOf.lean, `WholeD.of`), fit these rounds in
the sense of OnBytes/TypedOracleCompiler/Run/PageIsChain.lean (`FitL`), and the second chain's data end in a sealed
round in the sense of OnBytes/TypedOracleCompiler/Run/ChainF.lean (`SealLast`).

Why. OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean asks both of a file's data (`ReadL`: `fit₁`, `fit₂`,
`fit₃`, `seal₂`). Here they follow from how the data are made and from two properties of the rounds,
which the test `Whole.fits` tests.

  `RootsFit R`: in every round the entry counts the message's roots, and there are at most `maxRt`.
  `SealFit r`: a round of the kind "sealed" that draws a digest alone and asks for no work.
  `fitL_zip`, `fitL_rdsFromL`, `fitL_dropLast`: tools.
  `fit₁_of`, `fit₂_of`, `fit₃_of`: the three chains' data fit their rounds; the first chain's
    without its last round on both sides.
  `sealLast_of`: the second chain's data end in a sealed round, if its last round is one.
  `rootsFit_of_fits`: `Whole.fits` at two roots a message gives `RootsFit` of all three lists.
  `SealTested`, `sealTested_of`, `seals_of_fits`, `SealTested.fit`: what that test tests of the
    first and the second list's last round; it gives `SealFit`.
  `rounds_split`: a list of rounds is all but its last, and its last.

What is not claimed. That a list of rounds is not empty (OnBytes/Maker/Files.lean, `someFit`, tests
that).


-/
import OnBytes.Maker.WholeOf
import OnBytes.Maker.ReadSpecs
import OnBytes.TypedOracleCompiler.Run.ChainF

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run.PQ
open OnBytes.Params (Rounds)
open TypedOracleCompiler.Iop (maxRt)

/-- In every round the entry counts the message's roots, and there are at most `maxRt`. -/
def RootsFit (R : Rounds) : Prop :=
  ∀ r ∈ R, r.1.items.countP (· == .root) = r.1.entry.roots ∧ r.1.entry.roots ≤ maxRt

/-- A round of the kind "sealed" that draws a digest alone and asks for no work. -/
structure SealFit (r : Fmt.Round) : Prop where
  kind : r.kind = .sealed
  poss : r.entry.poss = 0
  trits : r.entry.trits = 0
  drawE : r.entry.drawE = 0
  drawNZ : r.entry.drawNZ = 0
  work : r.entry.work = 0

section
variable (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)

theorem fitL_zip : ∀ (R : Rounds) (l : List ℕ), l.length = R.length → RootsFit R →
    FitL (toRDs ((List.zipWith (Three.rdOf all t₁ t₂ here base first) R l).map rdtOf))
      (R.map (·.1))
  | [], _, _, _ => by
      rw [List.zipWith_nil_left]
      trivial
  | _ :: _, [], e, _ => by cases e
  | r :: R, n :: l, e, h => by
      obtain ⟨h1, h2⟩ := h r List.mem_cons_self
      refine ⟨rfl, rfl, rfl, ?_, ?_, h2,
        fitL_zip R l (Nat.succ.inj e) fun r' hr' => h r' (List.mem_cons_of_mem _ hr')⟩
      · show ((List.range (r.1.items.countP (· == .root))).map _).length = _
        rw [List.length_map, List.length_range, h1]
      · show (r.1.items.filter (· == .root)).length = _
        rw [← List.countP_eq_length_filter, h1]

theorem fitL_rdsFromL (R : Rounds) (h : RootsFit R) :
    FitL (toRDs ((Three.rdsFromL all t₁ t₂ here base first R).map rdtOf)) (R.map (·.1)) :=
  fitL_zip all t₁ t₂ here base first R _ (sentBefore_length R) h

end

theorem fitL_dropLast : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (rs : List Fmt.Round), FitL ds rs →
    FitL ds.dropLast rs.dropLast
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | [_], [_], _ => trivial
  | [_], _ :: _ :: _, h => h.2.2.2.2.2.2.elim
  | _ :: _ :: _, [_], h => h.2.2.2.2.2.2.elim
  | _ :: d' :: ds, _ :: r' :: rs, h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      fitL_dropLast (d' :: ds) (r' :: rs) h.2.2.2.2.2.2⟩

section
variable (a : ℕ) (R₁ R₂ R₃ : Rounds)

/-- **The first chain's data fit its rounds**, without the last round on both sides. -/
theorem fit₁_of (h : RootsFit R₁) :
    FitL (toRDs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁) (R₁.map (·.1)).dropLast := by
  have e := fitL_dropLast _ _ (fitL_rdsFromL
    (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂) 0 0 0 R₁ h)
  rw [← List.map_dropLast, ← List.map_dropLast] at e
  exact e

/-- **The second chain's.** -/
theorem fit₂_of (h : RootsFit R₂) :
    FitL (toRDs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂) (R₂.map (·.1)) :=
  fitL_rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂) 1
    (Three.rootsIn R₁) 0 R₂ h

/-- **The third chain's.** -/
theorem fit₃_of (h : RootsFit R₃) :
    FitL (toRDs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃) (R₃.map (·.1)) :=
  fitL_rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂) 2
    (Three.rootsIn R₁ + Three.rootsIn R₂) (Three.first₃ (Three.rootsIn R₁)) R₃ h

end

/-- Data that fit rounds whose last is a sealed round end in a sealed round. -/
theorem sealLast_of_fitL : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (rs : List Fmt.Round) (r : Fmt.Round),
    FitL ds rs → rs.getLast? = some r → SealFit r → SealLast ds
  | [], [], _, _, e, _ => by cases e
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | [d], [r'], r, h, e, s => by
      cases Option.some.inj (show some r' = some r from e)
      exact ⟨h.2.1.trans s.kind, by rw [h.1]; exact s.poss, by rw [h.1]; exact s.trits,
        by rw [h.1]; exact s.drawE, by rw [h.1]; exact s.drawNZ, by rw [h.1]; exact s.work⟩
  | [_], _ :: _ :: _, _, h, _, _ => h.2.2.2.2.2.2.elim
  | _ :: _ :: _, [_], _, h, _, _ => h.2.2.2.2.2.2.elim
  | _ :: d' :: ds, _ :: r' :: rs, r, h, e, s =>
    sealLast_of_fitL (d' :: ds) (r' :: rs) r h.2.2.2.2.2.2 (by
      rw [List.getLast?_cons_cons] at e
      exact e) s

/-- **The second chain's data end in a sealed round.** -/
theorem sealLast_of (a : ℕ) (R₁ R₂ R₃ : Rounds) (h : RootsFit R₂) (r : Fmt.Round)
    (e : (R₂.map (·.1)).getLast? = some r) (s : SealFit r) :
    SealLast (toRDs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂) :=
  sealLast_of_fitL _ _ r (fit₂_of a R₁ R₂ R₃ h) e s

/-- **The test gives the first property**, of all three lists. -/
theorem rootsFit_of_fits (R₁ R₂ R₃ : Rounds) (h : Three.Whole.fits R₁ R₂ R₃ 2 = true) :
    RootsFit R₁ ∧ RootsFit R₂ ∧ RootsFit R₃ := by
  simp only [Three.Whole.fits, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨a₁, a₂, a₃⟩ := h1
  exact ⟨fun r hr => ⟨(a₁ r hr).2, (a₁ r hr).2 ▸ (a₁ r hr).1⟩,
    fun r hr => ⟨(a₂ r hr).2, (a₂ r hr).2 ▸ (a₂ r hr).1⟩,
    fun r hr => ⟨(a₃ r hr).2, (a₃ r hr).2 ▸ (a₃ r hr).1⟩⟩

/-! ## The sealed rounds -/

/-- What `Whole.fits` tests of the last round of the first and of the second chain. -/
structure SealTested (r : Fmt.Round) : Prop where
  kind : r.kind = .sealed
  items : r.items = []
  roots : r.entry.roots = 0
  poss : r.entry.poss = 0
  trits : r.entry.trits = 0
  drawE : r.entry.drawE = 0
  drawNZ : r.entry.drawNZ = 0
  work : r.entry.work = 0

theorem SealTested.fit {r : Fmt.Round} (s : SealTested r) : SealFit r :=
  ⟨s.kind, s.poss, s.trits, s.drawE, s.drawNZ, s.work⟩

theorem sealTested_of {R : Rounds}
    (h : (match R.getLast? with
      | some r => r.1.kind == .sealed && r.1.opens.isEmpty && r.1.entry.roots == 0 &&
          r.2.isEmpty && r.1.items.isEmpty && r.1.entry.work == 0 && r.1.entry.drawE == 0 &&
          r.1.entry.drawNZ == 0 && r.1.entry.poss == 0 && r.1.entry.trits == 0
      | none => false) = true) : ∃ r, R.getLast? = some r ∧ SealTested r.1 := by
  cases e : R.getLast? with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k, _⟩, ro⟩, _⟩, it⟩, w⟩, de⟩, nz⟩, po⟩, tr⟩ := h
    exact ⟨r, rfl, k, it, ro, po, tr, de, nz, w⟩

/-- **The test gives the sealed rounds**: the first and the second list of rounds end in a round
that passes `SealTested`. The round is the list's last. -/
theorem seals_of_fits (R₁ R₂ R₃ : Rounds) (h : Three.Whole.fits R₁ R₂ R₃ 2 = true) :
    (∃ r, R₁.getLast? = some r ∧ SealTested r.1) ∧ ∃ r, R₂.getLast? = some r ∧ SealTested r.1 := by
  simp only [Three.Whole.fits, Bool.and_eq_true] at h
  obtain ⟨⟨_, h5⟩, _⟩ := h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h5
  exact ⟨sealTested_of h5.1, sealTested_of h5.2⟩

/-- A list of rounds is all but its last, and its last. -/
theorem rounds_split (R : Rounds) (r : Fmt.Round × List Fmt.Stored) (e : R.getLast? = some r) :
    R.map (·.1) = (R.map (·.1)).dropLast ++ [r.1] := by
  have e' : (R.map (·.1)).getLast? = some r.1 := by rw [List.getLast?_map, e]; rfl
  exact (List.dropLast_append_getLast? _ e').symm

end OnBytes.Maker
