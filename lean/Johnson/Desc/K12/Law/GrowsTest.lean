-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/GrowsTest.lean: a yes of the proximity test's decision leaves a statement that
has grown out of the one it was handed.

Of both texts: the kind's own parts (`proximityTestKind proximityTestParts p`, Johnson/Desc/K12/Join.lean) and the variant
that rides (`proximityTestKind guardedProximityTestParts p`, Johnson/Desc/K12/JoinGuarded.lean). There is no premise but the yes, not
even the place's two numbers early and answers: the switch is taken for every target.
  `batJ_grows`, `foldJ_grows`, `switchJ_grows`, `behindJ_grows`, `baseSt_grows`: part by part.
  `stages_grows`, `k12_grows_of`: by recursion along the stages; the top, for parts that are `Like`
    the kind's and whose base case leaves `BaseSt`.
  `k12_grows_joined`, `k12_grows`: of proximityTestKind proximityTestParts p; of proximityTestKind guardedProximityTestParts p.
A text of this project that is not in this repository has a theorem (k12_joined_keeps, not in this
library) that gives the first of the two from the five plain functions by a general law of its
frame; this file adds the variant, and stands over K12's files' laws on the frame alone.
It stands over Johnson/Desc/K12/Law/GrowsK.lean (the five plain functions), OutK.lean's `Like` (its
clause base is not spent here) and OutK2.lean's `BaseSt`.
Limits: `Grows` (Johnson/Desc/Grows.lean) says nothing on rows, pads, ledgers or the mark "spent as
a mask". A block that says no to all meets every statement here. No soundness is claimed, and
nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.GrowsK

set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)

theorem batJ_grows (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) : Grows t.st t1.st := by
  simp only [batJ] at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    exact batE_grows _ _ _ hx
  · cases h

theorem newGroupE_grows (a b : ℕ) (s : H2K.PS) (y : ℕ × H2K.PS) (h : H2K.newGroupE a b s = .ok y) :
    Grows s.d.st y.2.d.st := by
  unfold H2K.newGroupE at h
  cases hg : Ground.newGroupP s.d a b with
  | none => simp [hg, H2K.opt, Except.map] at h
  | some v =>
    simp only [hg, H2K.opt, Except.map] at h
    cases h
    exact Ground.newGroupP_grows _ _ _ _ _ hg

theorem foldJ_grows (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    Grows t.st t1.st := by
  simp only [foldJ] at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    exact (foldE_grows _ _ _ _ _ hx).trans (newGroupE_grows _ _ _ _ hy)
  · cases h

theorem switchJ_grows (p : P12) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (switchJ p j cur nxt last cut).decide t rs gs = .ok t1) : Grows t.st t1.st := by
  simp only [switchJ] at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    exact switchE_grows _ _ _ _ _ _ _ hx
  · cases h

theorem behindJ_grows (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (behindJ p j nxt cut).decide t rs gs = .ok t1) :
    Grows t.st t1.st := by
  simp only [behindJ] at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    exact behind_grows _ _ _ _ _ _ _ _ (H2K.Sw.named_ok hx)
  · cases h

theorem baseSt_grows (t tE : T12) (h : BaseSt t tE) : Grows t.st tE.st := by
  obtain ⟨star, _, _, e⟩ := h
  rw [e]
  exact grows_modOracle _ _ _ fun _ => ⟨rfl, id, fun _ h => h⟩

theorem stages_grows (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t') :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE →
      Grows t.st tE.st
  | [], j, cur, l, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    exact baseSt_grows _ _ (hB _ _ _ _ _ _ _ h)
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    exact (((foldJ_grows _ _ _ _ _ _ _ _ (hX.fold _ _ _ _ _ _ _ f1)).trans
      (switchJ_grows _ _ _ _ _ _ _ _ _ _ (hX.switch _ _ _ _ _ _ _ _ _ f2))).trans
      (behindJ_grows _ _ _ _ _ _ _ _ (hX.behind _ _ _ _ _ f3))).trans
      (stages_grows X p hX hB rest (j + 1) nxt _ t3 tE _ _ f5)

/-- A yes of the test's decision leaves a statement that has grown out of the one it was handed.
-/
theorem k12_grows_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t')
    (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) :
    Grows t0.st tE.st := by
  obtain ⟨first, rest, ds, tF, t1, _, _, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  exact (batJ_grows _ _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)).trans
    (stages_grows X p hX hB rest 0 first _ t1 tE _ _ hst)

/-- Of proximityTestKind proximityTestParts p (Join.lean's own parts). -/
theorem k12_grows_joined (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind K12.proximityTestParts p : Blk').decide t0 rs gs = .ok tE) : Grows t0.st tE.st :=
  k12_grows_of K12.proximityTestParts p (like_joined p)
    (fun j cur cut t t' rs gs h => baseJ_st p j cur cut t t' rs gs h) t0 tE rs gs h

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_grows (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : Grows t0.st tE.st :=
  k12_grows_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    t0 tE rs gs h

end H2K.Out

#print axioms H2K.Out.k12_grows_of
#print axioms H2K.Out.k12_grows_joined
#print axioms H2K.Out.k12_grows
