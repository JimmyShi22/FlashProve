-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/GroundCorner.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the public facts
K4Ground (Johnson/Road/K4/W/Ground.lean) do not hang on the coordinates of the end point of the row
products' token sumcheck: where they hold at heard values H they hold at H with another point of
the same length in that point's place, at a list of points and a list of tables of its own. So
there is a world at each token's corner (CornerWorld, RowFields.lean). Statements and proofs.

  `atTok`           heard values with another end point of the row products' token sumcheck.
  `mapM_isSome`, `mapM_all_isSome`   mapM returns if and only if the function returns at each
                    member.
  `pointsOf_atTok`  the verifier's list of points there.
  `phiOf_atTok`     phiOf returns at the other list wherever it returned at the first.
  `funsOf_atTok`    funsOf returns there.
  **`ground_atTok`**   K4Ground there.
  **`cornerWorld_all`**   CornerWorld at every token.

Not shown here. That the public facts K4Ground hold anywhere: no example is known. That the tables
which own the places that the rows' forms name stand off the matrix of the lookup's planes (hOff)
is a hypothesis, asked at every list of tables that funsOf makes of the laid families; it follows
from three public premises (rows_off, RowsBelow.lean).
No property is claimed.
-/
import Johnson.Road.K4.C.CornerGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten Heard matIx TableAsk TableAt pointsOf phiOf funsOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4.W (K4Ground)

/-- Heard values with z for the end point of the row products' token sumcheck. -/
def atTok (H : Heard) (z : Array E) : Heard := { H with tV := { H.tV with r := z } }

/-- mapM returns where the function returns at each member. -/
theorem mapM_isSome {α β : Type} {f : α → Option β} : ∀ l : List α,
    (∀ x ∈ l, (f x).isSome = true) → ∃ L, l.mapM f = some L
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self ..))
    obtain ⟨L, hL⟩ := mapM_isSome l fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨b :: L, ?_⟩
    rw [List.mapM_cons]
    exact Option.bind_eq_some_iff.mpr ⟨b, hb, Option.bind_eq_some_iff.mpr ⟨L, hL, rfl⟩⟩

/-- Where mapM returns, the function returns at each member. -/
theorem mapM_all_isSome {α β : Type} {f : α → Option β} : ∀ (l : List α) (L : List β),
    l.mapM f = some L → ∀ x ∈ l, (f x).isSome = true
  | [], _, _, _, hx => by cases hx
  | a :: l, L, h, x, hx => by
    rw [List.mapM_cons] at h
    obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, _⟩ := Option.bind_eq_some_iff.mp h1
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hc]
      rfl
    · exact mapM_all_isSome l cs hcs x hx

/-- **The verifier's list of points at the other end point**: it returns, and holds under each name
what the list at H holds, but z under the name r_tV. -/
theorem pointsOf_atTok {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) (z : Array E) :
    ∃ pts', pointsOf y (atTok H z) hd hd2 = some pts' ∧
      ∀ n, (pts'.find? fun p => p.1 == n) =
        if n = "r_tV" then some ("r_tV", z) else pts.find? fun p => p.1 == n := by
  unfold pointsOf at h
  obtain ⟨Z, hZ, h⟩ := bind_some h
  cases hd2 with
  | none =>
    obtain ⟨routed, hr, h⟩ := bind_some h
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain rfl := Option.some.inj h
    refine ⟨[("Z", Z), ("zt", H.ztF), ("Z_V", a), ("P_V", H.PV), ("Z_E", H.ZE), ("r_tV", z),
        ("Z_a", b)] ++
      (match H.tT with
        | some tT => [("Y", longPoint (Z.extract 0 y.ls) tT.r), ("rt", tT.r)]
        | none => []) ++ routed, ?_, ?_⟩
    · unfold pointsOf
      exact Option.bind_eq_some_iff.mpr ⟨Z, hZ, Option.bind_eq_some_iff.mpr ⟨routed, hr,
        Option.bind_eq_some_iff.mpr ⟨a, ha, Option.bind_eq_some_iff.mpr ⟨b, hb, rfl⟩⟩⟩⟩
    · intro n
      by_cases hn : n = "r_tV"
      · subst hn
        rw [if_pos rfl]
        rfl
      · have hq : ("r_tV" == n) = false := beq_eq_false_iff_ne.mpr fun e => hn e.symm
        rw [if_neg hn]
        simp only [List.cons_append, List.find?_cons, hq]
        rfl
  | some o =>
    obtain ⟨routed, hr, h⟩ := bind_some h
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain rfl := Option.some.inj h
    refine ⟨[("Z", Z), ("zt", H.ztF), ("Z_V", a), ("P_V", H.PV), ("Z_E", H.ZE), ("r_tV", z),
        ("Z_a", b)] ++
      (match H.tT with
        | some tT => [("Y", longPoint (Z.extract 0 y.ls) tT.r), ("rt", tT.r)]
        | none => []) ++ routed, ?_, ?_⟩
    · unfold pointsOf
      exact Option.bind_eq_some_iff.mpr ⟨Z, hZ, Option.bind_eq_some_iff.mpr ⟨routed, hr,
        Option.bind_eq_some_iff.mpr ⟨a, ha, Option.bind_eq_some_iff.mpr ⟨b, hb, rfl⟩⟩⟩⟩
    · intro n
      by_cases hn : n = "r_tV"
      · subst hn
        rw [if_pos rfl]
        rfl
      · have hq : ("r_tV" == n) = false := beq_eq_false_iff_ne.mpr fun e => hn e.symm
        rw [if_neg hn]
        simp only [List.cons_append, List.find?_cons, hq]
        rfl

/-- **phiOf returns at the other list wherever it returned at the first.** At a family whose point
is r_tV the weights that it returns are others. -/
theorem phiOf_atTok {y : Lay} {fo : Forest.Heard} {pts pts' : List (String × Array E)}
    {z r0 : Array E}
    (hfind : ∀ n, (pts'.find? fun p => p.1 == n) =
      if n = "r_tV" then some ("r_tV", z) else pts.find? fun p => p.1 == n)
    (h5 : (pts.find? fun p => p.1 == "r_tV") = some ("r_tV", r0)) (hz : z.size = r0.size)
    (a : TableAsk) (h : (phiOf y fo pts a).isSome = true) :
    (phiOf y fo pts' a).isSome = true := by
  unfold phiOf at h ⊢
  by_cases c0 : (a.name == "b-bits-0") = true
  · rw [if_pos c0] at h ⊢
    exact h
  · rw [if_neg c0] at h ⊢
    by_cases c1 : (a.name == "b-bits-1") = true
    · rw [if_pos c1] at h ⊢
      exact h
    · rw [if_neg c1] at h ⊢
      by_cases c2 : (a.name == "b-pin") = true
      · rw [if_pos c2] at h ⊢
        exact h
      · rw [if_neg c2] at h ⊢
        rw [hfind a.point]
        by_cases hp : a.point = "r_tV"
        · rw [if_pos hp]
          rw [hp, h5] at h
          dsimp only at h ⊢
          rw [hz]
          by_cases c : (r0.size != if a.lng = true then y.h.la else y.h.lt) = true
          · rw [if_pos c] at h
            cases h
          · rw [if_neg c]
            rfl
        · rw [if_neg hp]
          exact h

/-- **funsOf returns there.** -/
theorem funsOf_atTok {y : Lay} {fo : Forest.Heard} {pts pts' : List (String × Array E)}
    {z r0 : Array E} {laid : List (TableAsk × List (ℕ × ℕ))} {funs : Array HFun}
    (hfind : ∀ n, (pts'.find? fun p => p.1 == n) =
      if n = "r_tV" then some ("r_tV", z) else pts.find? fun p => p.1 == n)
    (h5 : (pts.find? fun p => p.1 == "r_tV") = some ("r_tV", r0)) (hz : z.size = r0.size)
    (h : funsOf y fo pts laid = some funs) : ∃ funs', funsOf y fo pts' laid = some funs' := by
  unfold funsOf at h ⊢
  obtain ⟨l, hl, _⟩ := bind_some h
  have all := mapM_all_isSome _ _ hl
  obtain ⟨L, hL⟩ := mapM_isSome (f := fun x : TableAsk × List (ℕ × ℕ) => do
      let phi ← phiOf y fo pts' x.1
      pure (x.2.map fun m =>
        ({ mat := m.1, len := x.1.L, phi, tree := 2, start := m.2 } : HFun))) laid
    (fun x hx => by
      have h1 : (phiOf y fo pts x.1).isSome = true := by
        have h2 := all x hx
        cases hq : phiOf y fo pts x.1 with
        | none =>
          rw [hq] at h2
          cases h2
        | some _ => rfl
      obtain ⟨phi, hphi⟩ := Option.isSome_iff_exists.mp (phiOf_atTok hfind h5 hz x.1 h1)
      beta_reduce
      rw [hphi]
      rfl)
  exact ⟨_, Option.bind_eq_some_iff.mpr ⟨L, hL, rfl⟩⟩

variable {h : Layer.Shape} {pc : List (List String)} {v : Env} {rd : Layer.Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {H : Heard}
  {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)} {funs : Array HFun} {D : Dim}

/-- **THE PUBLIC FACTS AT ANOTHER END POINT OF THE SAME LENGTH.** -/
theorem ground_atTok (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) (z : Array E)
    (hz : z.size = H.tV.r.size) :
    ∃ pts' funs', K4Ground h pc v rd r tl (atTok H z) hd hd2 pts' funs' D := by
  obtain ⟨pts', hp, hfind⟩ := pointsOf_atTok G.points z
  obtain ⟨_, _, _, _, _, h5⟩ := pointsOf_names3 G.points
  obtain ⟨funs', hf⟩ := funsOf_atTok hfind h5 hz G.funs
  exact ⟨pts', funs',
    { lay := G.lay, sw := G.sw, scales := G.scales, grp := G.grp, reads := G.reads
      tables := G.tables, tab := G.tab, mats := G.mats, NM := G.NM, points := hp, zt := G.zt
      funs := hf, sized := G.sized }⟩

/-- **A WORLD WITH THE TRUE ENTRIES AT EVERY TOKEN's CORNER**, from the public facts at the heard
values. hOff: at every list of tables that the verifier's function funsOf makes of the laid
families, at whatever list of points. -/
theorem cornerWorld_all (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) {Q : K4Pub}
    (hy : v.y = Q.P.y) (Mm : Mats Cb.Gl.E) (hs : H.tV.r.size = D.lT)
    (hOff : ∀ (pts' : List (String × Array E)) (funs' : Array HFun),
      funsOf Q.P.y H.fo pts' r.2.1 = some funs' → ∀ fs, rowForms v = some fs → ∀ a ∈ fs.toList,
      ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs' →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) → z.1.mat ≠ (matIx Q.P.y).iB) :
    ∀ i, CornerWorld (scl := sclOf h v.sc v.g v.y.Lam) Q v tl r Mm D
      (cellsOf D (cellsAt v.y Mm)) i := by
  intro i
  have hz : (cornerPt D.lT i).size = H.tV.r.size := by rw [hs, cornerPt_size]
  obtain ⟨pts', funs', G'⟩ := ground_atTok G (cornerPt D.lT i) hz
  have hf : funsOf Q.P.y H.fo pts' r.2.1 = some funs' := by
    rw [← hy]
    exact G'.funs
  exact cornerWorld_of_ground G' hy Mm rfl (hOff pts' funs' hf)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.mapM_isSome
#print axioms OnBytes.Road.K4.C.mapM_all_isSome
#print axioms OnBytes.Road.K4.C.pointsOf_atTok
#print axioms OnBytes.Road.K4.C.phiOf_atTok
#print axioms OnBytes.Road.K4.C.funsOf_atTok
#print axioms OnBytes.Road.K4.C.ground_atTok
#print axioms OnBytes.Road.K4.C.cornerWorld_all
