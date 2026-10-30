-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TermsFormsOf.lean: CONDITIONAL. Statements with their proofs.

What is here. The layers' own rounds (sub-protocol K4): THE VERIFIER's FORMS ON THE SECOND TOKEN
SUMCHECK's END VALUES RETURN (`termsForms`, OnBytes/Desc/First/K4/Claims.lean), at the structure
that the honest side's `envOf` returns (`envPub`, RowMapsOf.lean), with any points of the calls, and
at every heard state that holds a second token sumcheck. That is the hypothesis h8 of
`sides_of_plan` (SidesOf.lean) and of `sides_return`
(Johnson/Desc/ProofFile/Honest/K4/Law/SidesReturn.lean).
How. The function asks three readers at the token point "rt": the reciprocal of each norm's row, the
score of each layer with routed experts, each entry of such a layer's selector. The family of tables
"ar@rt" is found and all its entries are there (`reach_five`, PointReturn.lean); the row's cells by
`rowCells_at` (RowCellsAt.lean); the two tensors' entries by `short_at` (PointReturn.lean).

Not shown here. That a plan with the public facts `K4Plan` exists: at the public parameters' own
data of the layers that is shown on conditions (`k4Plan_head`,
Johnson/Desc/ProofFile/Honest/K4/Law/W/PlanHead.lean); no example without a condition is known.
UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. That the list of tables is laid (hl), that
the reads' array has a column (hK) and that the row of the first free entry behind the tables fits
32 bits (hb) are hypotheses. Public data alone: whether a form IS THERE, nothing on what it is
worth. Nothing on soundness, on completeness or on any other property. No property is claimed.

  `optBind_there`, `optMapM_there`   a step that returns, behind a step that returns
  `termsForms_returns`   **the forms are there**
-/
import Johnson.Road.K4.C.RowCellsAt
import Johnson.Road.K4.C.PointReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard TableAsk TableAt layTables tableAsks)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First.K4 (termsForms)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf)
open Inst.Model.FFSeg (Dim Arr)

/-- A step that returns at every value, behind a step that returns. -/
theorem optBind_there {α β : Type} (x : Option α) (f : α → Option β) (hx : x.isSome = true)
    (hf : ∀ a, (f a).isSome = true) : (x.bind f).isSome = true := by
  obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp hx
  exact hf a

/-- A walk all of whose steps return returns. -/
theorem optMapM_there {α β : Type} {g : α → Option β} (l : List α)
    (h : ∀ x ∈ l, (g x).isSome = true) : (l.mapM g).isSome = true := by
  obtain ⟨L, hL⟩ := list_mapM_there l h
  rw [hL]
  rfl

variable {Q : K4Pub} {iU3 : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- CONDITIONAL on every hypothesis named. **THE VERIFIER's FORMS ON THE SECOND TOKEN SUMCHECK's END
VALUES ARE THERE.** -/
theorem termsForms_returns (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hK : ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (zk : Array (Array E)) (H : Heard) (hT : H.tT.isSome = true) :
    (termsForms (envPub Q r.1 iU3 zk) H).isSome = true := by
  have hmats : matsOf Q = matsR Q.P.y Q.g := A.tails
  have hl' : layTables (matsR (envPub Q r.1 iU3 zk).y (envPub Q r.1 iU3 zk).g)
      (tableAsks (envPub Q r.1 iU3 zk).y Q.P.rd (envPub Q r.1 iU3 zk).g) 0 = some r := by
    show layTables (matsR Q.P.y Q.g) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r
    rw [← hmats]
    exact hl
  obtain ⟨_, RS⟩ := reach_five (v := envPub Q r.1 iU3 zk) A.lay A.sw hp4 A.grp A.reads hl' rfl hK hb
  obtain ⟨tb, htb, Rch⟩ := RS ("ar" ++ "@" ++ "rt", 2) (by simp)
  have Ad := admitted_of_layout A.lay A.sw.p3
  have Sw : Switches Q.P.y.h := by rw [Ad.shape]; exact A.sw
  have h4 : Q.P.y.h.p4 = true := by rw [Ad.shape]; exact hp4
  have L2 := laid2_of_layout A.lay
  have hLamM : ∀ {lm : ℕ}, lm < Q.P.y.LamM → lm < 2 ^ Q.P.y.h.ll / 2 := fun {lm} h => by
    rw [← Ad.laid.LamM]
    exact h
  -- the rows
  have hR : ∀ i, i < Q.P.y.NN * Q.P.y.Lam → ((envPub Q r.1 iU3 zk).rowR "rt" i).isSome = true := by
    intro i hi
    have hi' : i < Q.P.y.NI := by
      have e1 := (normsPlan_of_plan A).NI
      have e2 : D.nNu = (dimOf hS).nNu := A.sized.nNu_eq
      have e3 : Q.P.y.NN = 2 := Ad.laid.NN
      have e4 : Q.P.y.Lam = 2 ^ Q.P.y.h.ll := Ad.laid.Lam
      rw [e3, e4] at hi
      rw [e1, e2, ← Ad.shape]
      exact hi
    obtain ⟨cells, hc⟩ := rowCells_at A hp4 (v := envPub Q r.1 iU3 zk) rfl (P := "rt") htb Rch hi'
    have x5 : ((envPub Q r.1 iU3 zk).y.h.xl == 5) = true := by
      show (Q.P.y.h.xl == 5) = true
      rw [Sw.xl]
      rfl
    unfold Env.rowR
    rw [if_pos x5]
    unfold Env.row5At
    rw [hc]
    rfl
  -- the scores and the selectors
  have hsc : ∀ lm, lm < Q.P.y.LamM → ((envPub Q r.1 iU3 zk).shA "sc" "rt" lm 0).isSome = true :=
    fun lm h => shA_some
      (short_at (v := envPub Q r.1 iU3 zk) Ad.laid L2 Sw (sized_dimOf _) h4 "rt" .sc (Or.inl rfl)
        (RS ("ar" ++ "@" ++ "rt", 2) (by simp)) (hLamM h)) Nat.zero_lt_one
  have hsel : ∀ lm j, lm < Q.P.y.LamM → j < Q.P.y.h.NE →
      ((envPub Q r.1 iU3 zk).shA "sel" "rt" lm j).isSome = true :=
    fun lm j h hj => shA_some
      (short_at (v := envPub Q r.1 iU3 zk) Ad.laid L2 Sw (sized_dimOf _) h4 "rt" .sel (Or.inl rfl)
        (RS ("ar" ++ "@" ++ "rt", 2) (by simp)) (hLamM h)) hj
  obtain ⟨tT, htT⟩ := Option.isSome_iff_exists.mp hT
  unfold termsForms
  simp only [Option.bind_eq_bind, Option.pure_def, htT, Option.bind_some]
  refine optBind_there _ _ (optMapM_there _ fun i hi => ?_) fun a =>
    optBind_there _ _ (optMapM_there _ fun lm hlm => ?_) fun b =>
      optBind_there _ _ (optMapM_there _ fun x hx => ?_) fun c => rfl
  · rw [Option.isSome_map]
    exact hR i (List.mem_range.1 hi)
  · rw [Option.isSome_map]
    exact hsc lm (List.mem_range.1 hlm)
  · rw [Option.isSome_map]
    have hx' : x < Q.P.y.LamM * Q.P.y.h.NE := List.mem_range.1 hx
    have hNE : 0 < Q.P.y.h.NE := by
      rcases Nat.eq_zero_or_pos Q.P.y.h.NE with e | e
      · rw [e, Nat.mul_zero] at hx'
        exact absurd hx' (Nat.not_lt_zero _)
      · exact e
    exact hsel _ _ ((Nat.div_lt_iff_lt_mul hNE).2 hx') (Nat.mod_lt _ hNE)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.optBind_there
#print axioms OnBytes.Road.K4.C.optMapM_there
#print axioms OnBytes.Road.K4.C.termsForms_returns
