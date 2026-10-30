-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Points.lean: THE LAYERS' OWN ROUNDS (K4): ONE OF THE PREMISES OF "THE
HEARING RETURNS" IS PAID: HearPub's field points (Johnson/Desc/First/K4/Returns/Whole.lean): the
points at which the tables are read (pointsOf) and the tables' weights (funsOf,
OnBytes/Model/Layer.lean) return. General laws: nothing is evaluated.

  lastOf_some, lastOf_size, mapM_some   small tools.
  ptSizes         the ten points' names, each with its number of coordinates.
  askB, pointsB   THE TEST WITH CODE ON THE PLAN: the layers' numbers of variables reach the number
                  of a block's row's coordinates; each family of tables is one of the three on the
                  planes' matrix, or its point is a known name with the number of coordinates that
                  the kind of table asks.
  **points_pay**   the test's yes; the lookup's point has its last coordinates; the token point has
                  its length; the planes' matrix fits the lookup's shape (planeCols): HearPub's
                  field points, for all arrays of the lengths that it names.

Limits. That the test is true at a plan is not shown here. Two of the four premises read the
lookup's record (sizes and its shape). Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest

/-- The last k coordinates of a point that has them. -/
theorem lastOf_some (z : Array E) (k : Nat) (h : k ≤ z.size) :
    ∃ a, (lastOf z k).toOption = some a ∧ a.size = k := by
  refine ⟨z.extract (z.size - k) z.size, ?_, by simp; omega⟩
  unfold lastOf cutLast
  rw [if_neg (by omega)]
  rfl

/-- What lastOf returns has k coordinates. -/
theorem lastOf_size {z a : Array E} {k : Nat} (h : (lastOf z k).toOption = some a) :
    a.size = k := by
  by_cases hk : k ≤ z.size
  · obtain ⟨b, e, hb⟩ := lastOf_some z k hk
    rw [e] at h
    obtain rfl := Option.some.inj h
    exact hb
  · unfold lastOf cutLast at h
    rw [if_pos (by omega)] at h
    cases h

/-- A list's members one by one, in Option. -/
theorem mapM_some {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ x ∈ l, ∃ b, f x = some b) →
    ∃ bs, l.mapM f = some bs
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨b, hb⟩ := h x (List.mem_cons_self ..)
    obtain ⟨bs, hbs⟩ := mapM_some f l fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨b :: bs, by rw [List.mapM_cons, hb, hbs]; rfl⟩

/-- The names of the points at which the tables are read, each with its number of coordinates. -/
def ptSizes (P : Pub) (g : Nat) : List (String × Nat) :=
  [("Z", P.y.h.la), ("zt", P.y.h.lt), ("Z_V", P.y.h.la), ("P_V", P.y.h.lt),
    ("Z_E", if (g == 0) = true then P.y.ls + P.y.h.lt else 0), ("r_tV", P.y.h.lt),
    ("Z_a", P.y.h.la), ("Y", min P.y.ls P.y.h.la + P.y.h.lt), ("rt", P.y.h.lt),
    ("Z_b", P.y.h.la)]

/-- One family of tables: it is one of the three on the planes' matrix, or its point is a known name
with the number of coordinates that the kind of table asks. -/
def askB (P : Pub) (g : Nat) (a : TableAsk) : Bool :=
  a.name == "b-bits-0" || a.name == "b-bits-1" || a.name == "b-pin" ||
    match (ptSizes P g).find? fun p => p.1 == a.point with
    | some p => p.2 == (if a.lng then P.y.h.la else P.y.h.lt)
    | none => false

/-- **The test with code on the plan** for the points and the tables' weights. -/
def pointsB (P : Pub) (g : Nat) (laid : List (TableAsk × List (Nat × Nat))) : Bool :=
  decide (P.y.h.la ≤ P.rd.muV) && decide (P.y.h.la ≤ P.rd.muH) && decide (P.y.h.la ≤ P.rd.muH2) &&
    laid.all fun x => askB P g x.1

/-- **The test pays HearPub's field points.** -/
theorem points_pay {P : Pub} {g : Nat} {fo : Forest.Heard} {Z ztF : Array E}
    {laid : List (TableAsk × List (Nat × Nat))} (hb : pointsB P g laid = true)
    (hZ : (lastOf fo.zx P.y.h.la).toOption = some Z) (hzt : ztF.size = P.y.h.lt)
    (hB : (Forest.planeCols fo.shape P.y.h.lmb).toBool = true) :
    ∀ (H : Heard) (hd hd2 : Level) (tT : Tsc), H.fo = fo → H.ztF = ztF → H.tT = some tT →
      tT.r.size = P.y.h.lt → H.PV.size = P.y.h.lt →
      H.ZE.size = (if (g == 0) = true then P.y.ls + P.y.h.lt else 0) → H.wpl.r.size = P.rd.muV →
      H.tV.r.size = P.y.h.lt → hd.r.size = P.rd.muH → hd2.r.size = P.rd.muH2 →
      ∃ pts funs, pointsOf P.y H hd (some hd2) = some pts ∧ funsOf P.y fo pts laid = some funs := by
  intro H hd hd2 tT eFo eZt eT s1 s2 s3 s4 s5 s6 s7
  unfold pointsB at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hb
  obtain ⟨zV, e1, z1⟩ := lastOf_some H.wpl.r P.y.h.la (by omega)
  obtain ⟨zA, e2, z2⟩ := lastOf_some hd.r P.y.h.la (by omega)
  obtain ⟨zB, e3, z3⟩ := lastOf_some hd2.r P.y.h.la (by omega)
  have z0 := lastOf_size hZ
  have hp : pointsOf P.y H hd (some hd2) = some ([("Z", Z), ("zt", H.ztF), ("Z_V", zV),
      ("P_V", H.PV), ("Z_E", H.ZE), ("r_tV", H.tV.r), ("Z_a", zA)] ++
      [("Y", longPoint (Z.extract 0 P.y.ls) tT.r), ("rt", tT.r)] ++ [("Z_b", zB)]) := by
    unfold pointsOf
    dsimp only
    rw [eFo, hZ, eT, e1, e2, e3]
    rfl
  have hsz : (([("Z", Z), ("zt", H.ztF), ("Z_V", zV), ("P_V", H.PV), ("Z_E", H.ZE),
      ("r_tV", H.tV.r), ("Z_a", zA)] ++
      [("Y", longPoint (Z.extract 0 P.y.ls) tT.r), ("rt", tT.r)] ++
      [("Z_b", zB)] : List (String × Array E)).map fun p => (p.1, p.2.size)) = ptSizes P g := by
    unfold ptSizes longPoint
    simp [z0, z1, z2, z3, s1, s2, s3, s5, eZt, hzt]
  have hphi : ∀ x ∈ laid, ∃ phi, phiOf P.y fo ([("Z", Z), ("zt", H.ztF), ("Z_V", zV), ("P_V", H.PV),
      ("Z_E", H.ZE), ("r_tV", H.tV.r), ("Z_a", zA)] ++
      [("Y", longPoint (Z.extract 0 P.y.ls) tT.r), ("rt", tT.r)] ++ [("Z_b", zB)]) x.1 =
      some phi := by
    intro x hx
    have ha := List.all_eq_true.1 b4 x hx
    unfold askB at ha
    unfold phiOf
    by_cases c1 : (x.1.name == "b-bits-0") = true
    · rw [if_pos c1]
      unfold Forest.phiB
      dsimp only
      rw [if_pos hB]
      exact ⟨_, rfl⟩
    · rw [if_neg c1]
      by_cases c2 : (x.1.name == "b-bits-1") = true
      · rw [if_pos c2]
        unfold Forest.phiB
        dsimp only
        rw [if_pos hB]
        exact ⟨_, rfl⟩
      · rw [if_neg c2]
        by_cases c3 : (x.1.name == "b-pin") = true
        · rw [if_pos c3]
          exact ⟨_, rfl⟩
        · rw [if_neg c3]
          simp only [c1, c2, c3, Bool.or_false, Bool.false_or] at ha
          rw [← hsz, List.find?_map] at ha
          cases hf : List.find? (fun p : String × Array E => p.1 == x.1.point)
              ([("Z", Z), ("zt", H.ztF), ("Z_V", zV), ("P_V", H.PV), ("Z_E", H.ZE),
                ("r_tV", H.tV.r), ("Z_a", zA)] ++
                [("Y", longPoint (Z.extract 0 P.y.ls) tT.r), ("rt", tT.r)] ++ [("Z_b", zB)]) with
          | none =>
            have hf' : List.find? ((fun p : String × Nat => p.1 == x.1.point) ∘
                fun p : String × Array E => (p.1, p.2.size)) _ = none := hf
            rw [hf'] at ha
            cases ha
          | some p =>
            have hf' : List.find? ((fun p : String × Nat => p.1 == x.1.point) ∘
                fun p : String × Array E => (p.1, p.2.size)) _ = some p := hf
            rw [hf'] at ha
            have hs : p.2.size = if x.1.lng = true then P.y.h.la else P.y.h.lt := by simpa using ha
            dsimp only
            rw [if_neg (by simpa using hs)]
            exact ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := mapM_some (fun x : TableAsk × List (Nat × Nat) => do
      let phi ← phiOf P.y fo ([("Z", Z), ("zt", H.ztF), ("Z_V", zV), ("P_V", H.PV), ("Z_E", H.ZE),
        ("r_tV", H.tV.r), ("Z_a", zA)] ++
        [("Y", longPoint (Z.extract 0 P.y.ls) tT.r), ("rt", tT.r)] ++ [("Z_b", zB)]) x.1
      pure (x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun)))
    laid fun x hx => by
      obtain ⟨phi, e⟩ := hphi x hx
      refine ⟨x.2.map fun m => ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun),
        ?_⟩
      dsimp only
      rw [e]
      rfl
  refine ⟨_, l.flatten.toArray, hp, ?_⟩
  unfold funsOf
  rw [hl]
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.lastOf_some
#print axioms OnBytes.Desc.First.K4.Rt.lastOf_size
#print axioms OnBytes.Desc.First.K4.Rt.mapM_some
#print axioms OnBytes.Desc.First.K4.Rt.points_pay
