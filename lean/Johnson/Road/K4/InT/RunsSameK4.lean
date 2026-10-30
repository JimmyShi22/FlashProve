-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/RunsSameK4.lean: K4's TWO RUNS OF CLAIMS "front" AND "back" ANSWER AT A LATER
STATE WHAT THEY ANSWER AT AN EARLIER ONE (`RunSame`, Johnson/Top/H/Keep/FormsPassK3.lean),
where the two states stand in a layers' segment with one and the same "what K4's hearing
returned", the later ledger is a later one over the same arrays, and the runs' three windows are
free in it. Statements with their proofs: calls.

  `lifted_of`: a lifted run of K4's returns where the state stands in a layers' segment, what was
    heard is there and the listing returns: the way back of `runOfAtS`
    (Johnson/Desc/First/K4/RunsAtS.lean).
  `K4Stays s s'`: the premise, a field a fact.
  `runSame_core`: a lifted run whose listing goes forward is RunSame.
  `K4StaysBelow` | **`k4_runSame_below`**: the same from "nothing turns under a slot below the
    ledger's next, and the three windows lie below it": that the windows are free is not asked: a
    run that returns has found them free.
  **`k4_runSame`**: name = "front" ∨ name = "back" · (blockAtC p).claims.lookup name = some runC ·
  K4Stays s s' ⟹ RunSame runC s s'.

Limits. K4Stays IS A PREMISE: that an accept of another sub-protocol gives it is that sub-protocol's
files' to show (own? stays · "later" · the arrays · no slot of the three windows is filled). AT K4's
OWN RUNS: the driver's guard round them is Johnson/Road/K4/InT/SeatTie.lean's. K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.RunsFwd
import Johnson.Road.K4.InT.SeatTie
import Johnson.Top.H.Keep.FormsPassK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.InT

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par blockAtC blockAtS atClaims claimOf block seatOwn part? setPart runOf
  runOf_ok runOfAtS liftPart_run atClaims_run block_front block_back frontOf formsBack
  formsFrontWith formsFront formsFrontNoRows formsFrontWith_some formsBack_some)
open OnBytes.Desc.First.K4.Slots (WinFree InWin SameAt run_same formsFront_fwd formsBack_fwd)
open VerifiableInference.Desc (named K9.lateOf Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.OnPublicFiles (RunSame)

/-- A lifted run of K4's returns. -/
theorem lifted_of {nm : String} {f : Own → Fork → Option (Array Aff × Fork)} {s : S} {a : LayOwn}
    {o : Own} {fs : Array Aff} {G : Fork} (ha : s.here = .lay a) (ho : a.own = some o)
    (hf : f o a.F = some (fs, G)) :
    ((named "the part is not there" (part? s)).bind fun q =>
      (runOf seatOwn nm f q).map fun y => (y.1, setPart s y.2)) =
      .ok (fs.toList, { s with here := .lay { a with F := G },
                               rowsOwed := if s.noneWaits then none else s.rowsOwed }) := by
  have hq : part? s = some (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
    simp [part?, ha]
  have hd : runOf seatOwn nm f (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) =
      .ok (fs.toList, seatOwn.setFork (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) G) :=
    (runOf_ok seatOwn nm f _ _ _).mpr ⟨o, fs, G, ho, hf, rfl, rfl⟩
  rw [hq]
  simp only [named, Except.bind, hd, Except.map]
  rfl

/-- **What is asked of the two states.** -/
structure K4Stays (s s' : S) : Prop where
  /-- both stand in a layers' segment, with one "what K4's hearing returned", the later ledger a
  later
  one over the same arrays, from a ledger with arrays of the right sizes -/
  lay : ∃ a a' : LayOwn, s.here = .lay a ∧ s'.here = .lay a' ∧ a'.own = a.own ∧ PscRun.Sized a.F ∧
    Later a.F a'.F ∧ a'.F.trees = a.F.trees ∧
    ∀ o, a.own = some o → WinFree o.H.tV.p a'.F ∧ WinFree o.H.fo.leaves a'.F ∧
      WinFree o.wo.toWsMerged.p a'.F

theorem runSame_core {nm : String} {f : Own → Fork → Option (Array Aff × Fork)} {s s' : S}
    {a a' : LayOwn} (ha : s.here = .lay a) (ha' : s'.here = .lay a') (hown : a'.own = a.own)
    (htr : a'.F.trees = a.F.trees)
    (hfwd : ∀ o fs G, a.own = some o → f o a.F = some (fs, G) →
      ∃ G', f o a'.F = some (fs, G') ∧ K9.lateOf a'.F G' = K9.lateOf a.F G) :
    RunSame (fun _ t => (((named "the part is not there" (part? t)).bind fun q =>
      (runOf seatOwn nm f q).map fun y => (y.1, setPart t y.2))).map
        fun y => (y.1.map claimOf, y.2)) s s' := by
  intro cl t F G hr hF hG
  cases hd : ((named "the part is not there" (part? s)).bind fun q =>
      (runOf seatOwn nm f q).map fun y => (y.1, setPart s y.2)) with
  | error e =>
    have hr' : Except.map (fun y : List Aff × S => (y.1.map claimOf, y.2))
        ((named "the part is not there" (part? s)).bind fun q =>
          (runOf seatOwn nm f q).map fun y => (y.1, setPart s y.2)) = .ok (cl, t) := hr
    rw [hd] at hr'
    exact nomatch hr'
  | ok y =>
    obtain ⟨y1, y2⟩ := y
    have hr' : Except.map (fun y : List Aff × S => (y.1.map claimOf, y.2))
        ((named "the part is not there" (part? s)).bind fun q =>
          (runOf seatOwn nm f q).map fun y => (y.1, setPart s y.2)) = .ok (cl, t) := hr
    rw [hd] at hr'
    have hr2 : (y1.map claimOf, y2) = (cl, t) := Except.ok.inj hr'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr2
    obtain ⟨a₁, o, fs, G₁, ho, hf, rfl, hw⟩ := runOfAtS hd
    have ea : a₁ = a := by
      have := hw.1.symm.trans ha
      injection this
    subst ea
    have eF : F = a₁.F := by
      have : s.fork? = some a₁.F := by simp [S.fork?, ha]
      exact Option.some.inj (hF.symm.trans this)
    have eG : G = G₁ := by
      have : y2.fork? = some G₁ := by rw [hw.2]; rfl
      exact Option.some.inj (hG.symm.trans this)
    subst eF
    subst eG
    obtain ⟨G', hf', hl⟩ := hfwd o fs G ho hf
    refine ⟨{ s' with here := .lay { a' with F := G' },
                      rowsOwed := if s'.noneWaits then none else s'.rowsOwed }, a'.F, G', ?_,
      by simp [S.fork?, ha'], ?_, hl, htr⟩
    · show Except.map _ _ = _
      rw [lifted_of ha' (hown.trans ho) hf']
      rfl
    · rfl

/-- **K4's two runs answer at the later state what they answer at the earlier one.** -/
theorem k4_runSame {p : Par} {name : String} (hn : name = "front" ∨ name = "back")
    {runC : ℕ → S → Except String (List Claim × S)}
    (hC : (blockAtC p).claims.lookup name = some runC) {s s' : S} (K : K4Stays s s') :
    RunSame runC s s' := by
  obtain ⟨a, a', ha, ha', hown, hS, L, htr, W⟩ := K.lay
  have hC' : (atClaims (blockAtS p)).claims.lookup name = some runC := hC
  rw [atClaims_run] at hC'
  have hl := liftPart_run part? setPart (block seatOwn p) name
  rcases hn with rfl | rfl
  · rw [block_front] at hl
    rw [show (blockAtS p).claims.lookup "front" = _ from hl] at hC'
    obtain rfl := Option.some.inj hC'
    refine runSame_core ha ha' hown htr fun o fs G ho hf => ?_
    obtain ⟨w1, w2, _⟩ := W o ho
    unfold frontOf at hf ⊢
    by_cases hk : p.k3Runs = true
    · rw [if_pos hk] at hf ⊢
      obtain ⟨G', g1, _, g3⟩ := formsFront_fwd hS L w1 w2 hf
      exact ⟨G', g1, g3⟩
    · rw [if_neg hk] at hf ⊢
      obtain ⟨G', g1, _, g3⟩ := formsFront_fwd hS L w1 w2 hf
      exact ⟨G', g1, g3⟩
  · rw [block_back] at hl
    rw [show (blockAtS p).claims.lookup "back" = _ from hl] at hC'
    obtain rfl := Option.some.inj hC'
    refine runSame_core ha ha' hown htr fun o fs G ho hf => ?_
    obtain ⟨_, _, w3⟩ := W o ho
    obtain ⟨G', g1, _, g3⟩ := formsBack_fwd hS L w3 hf
    exact ⟨G', g1, g3⟩

/-! ## The same from "nothing turns below the ledger's next" -/

/-- **What is asked of the two states, in the words of a sub-protocol that takes its slots from the
ledger's next on**: nothing turns under a slot below that next, and K4's three windows lie below
it. That the windows are free need not be asked: a run that returns has found them free. -/
structure K4StaysBelow (s s' : S) : Prop where
  lay : ∃ a a' : LayOwn, s.here = .lay a ∧ s'.here = .lay a' ∧ a'.own = a.own ∧ PscRun.Sized a.F ∧
    Later a.F a'.F ∧ a'.F.trees = a.F.trees ∧ (∀ j, j < a.F.next → SameAt a.F a'.F j) ∧
    ∀ o, a.own = some o →
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ a.F.next ∧
      o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ a.F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ a.F.next

/-- A window from which a run is taken is free. -/
theorem free_of_run {p : Psc} {F G : Fork} (hF : PscRun.Sized F)
    (h : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    WinFree p F := by
  obtain ⟨_, _, a, _⟩ := PscRun.hideRun_ok F G _ _ _ hF h
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = p.first + i := ⟨j - p.first, by have := hj.1; omega⟩
  refine (a i ?_).2.1
  rw [Array.size_replicate]
  have := hj.2
  omega

/-- A window below n that is free in F is free in a ledger that agrees with F below n. -/
theorem free_below {p : Psc} {F F' : Fork} {n : ℕ} (W : WinFree p F)
    (hw : p.first + p.walk.1.length ≤ n) (hs : ∀ j, j < n → SameAt F F' j) : WinFree p F' :=
  fun j hj c => W j hj ((hs j (by have := hj.2; omega)).1.1 c)

theorem k4_runSame_below {p : Par} {name : String} (hn : name = "front" ∨ name = "back")
    {runC : ℕ → S → Except String (List Claim × S)}
    (hC : (blockAtC p).claims.lookup name = some runC) {s s' : S} (K : K4StaysBelow s s') :
    RunSame runC s s' := by
  obtain ⟨a, a', ha, ha', hown, hS, L, htr, hs, W⟩ := K.lay
  have hC' : (atClaims (blockAtS p)).claims.lookup name = some runC := hC
  rw [atClaims_run] at hC'
  have hl := liftPart_run part? setPart (block seatOwn p) name
  have front : ∀ rows o fs G, a.own = some o → formsFrontWith rows p.P p.g o a.F = some (fs, G) →
      ∃ G', formsFrontWith rows p.P p.g o a'.F = some (fs, G') ∧
        K9.lateOf a'.F G' = K9.lateOf a.F G := by
    intro rows o fs G ho hf
    obtain ⟨w1, w2, _⟩ := W o ho
    obtain ⟨_, _, _, F1, F2, _, _, _, _, r1, r2, _⟩ := formsFrontWith_some hf
    obtain ⟨s1, _, _⟩ := run_same hS r1
    have f1 : WinFree o.H.tV.p a.F := free_of_run hS r1
    have f2 : WinFree o.H.fo.leaves a.F := fun j hj c =>
      free_of_run s1 r2 j hj ((PscRun.hideRun_keeps r1).keep j c).1
    obtain ⟨G', g1, _, g3⟩ :=
      formsFront_fwd hS L (free_below f1 w1 hs) (free_below f2 w2 hs) hf
    exact ⟨G', g1, g3⟩
  rcases hn with rfl | rfl
  · rw [block_front] at hl
    rw [show (blockAtS p).claims.lookup "front" = _ from hl] at hC'
    obtain rfl := Option.some.inj hC'
    refine runSame_core ha ha' hown htr fun o fs G ho hf => ?_
    unfold frontOf at hf ⊢
    by_cases hk : p.k3Runs = true
    · rw [if_pos hk] at hf ⊢
      exact front false o fs G ho hf
    · rw [if_neg hk] at hf ⊢
      exact front true o fs G ho hf
  · rw [block_back] at hl
    rw [show (blockAtS p).claims.lookup "back" = _ from hl] at hC'
    obtain rfl := Option.some.inj hC'
    refine runSame_core ha ha' hown htr fun o fs G ho hf => ?_
    obtain ⟨_, _, w3⟩ := W o ho
    obtain ⟨F1, _, r1, _⟩ := formsBack_some hf
    obtain ⟨G', g1, _, g3⟩ := formsBack_fwd hS L (free_below (free_of_run hS r1) w3 hs) hf
    exact ⟨G', g1, g3⟩

end OnBytes.Road.K4.InT

#print axioms OnBytes.Road.K4.InT.free_of_run
#print axioms OnBytes.Road.K4.InT.free_below
#print axioms OnBytes.Road.K4.InT.k4_runSame_below
#print axioms OnBytes.Road.K4.InT.lifted_of
#print axioms OnBytes.Road.K4.InT.runSame_core
#print axioms OnBytes.Road.K4.InT.k4_runSame
