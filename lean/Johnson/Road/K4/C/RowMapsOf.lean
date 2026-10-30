-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowMapsOf.lean: CONDITIONAL.

What is here. The honest side's function that lays the fields a, b, Rlo, Rhi of each norm's row as
tables on the tokens returns, at every input and at all sampled values (`rowMaps_returns`;
`rowMaps`: Johnson/Desc/K4/Honest/Norms.lean): the one return to which
Johnson/Desc/ProofFile/Honest/K4/Law/W/FitRows.lean brings two clauses of the public test
k4MakersFit. From the plan's nine public facts (`K4Plan`) and five further public facts. Step by
step: the structure which the forms read is made (`envOf_pub`); the family of tables "ar@r_tV" is
found, all its entries are within the verifier's reader's reach, and the honest reads hold its
weights wherever the point r_tV stands in the list with lt coordinates (`row_table`, over
Johnson/Road/K4/C/ReachPlan.lean's reach_family, the library's ask_of_name and
Johnson/Road/K4/C/HasOf.lean); so the verifier's forms of the rows' digits are made and name entries
of that one table alone (`rowCells_rtV`, after Johnson/Road/K4/C/StreamsThere.lean's rowDigits_of,
which stands at the point zt); the four fields are sums of digits (the library's ofDigits_four,
Johnson/Road/K4/Reads/NormRowEnts.lean); so each is valued at each token.

  `envPub Q tab iU3 zk`   the structure that envOf returns.
  `envOf_pub`   it returns it.
  `rtV_in`, `ask_rtV`   the point r_tV is among the points of the matrix of rows; its family is
      asked for.
  `list_mapM_there`, `amapM_there`   a walk all of whose steps return returns.
  `row_table`   the family's table.
  `inOne_rowCells`, `rowCells_rtV`   a row's cells.
  `tokPt Q t`   the list of the one point r_tV, laid at the bits of token t.
  `rowMaps_returns`   the whole.

Not shown here. FIVE PUBLIC HYPOTHESES BESIDE K4Plan: the shape's switch p4 is on (hp4); the plan
names the array of the reads (hU); the verifier's laying of the tables returns (hl); that array has
a column (hK); the first free entry's row fits 32 bits (hb: one entry more than the verifier's
reader ever tests). No statement here shows them. K4Plan's FIELD sw BARS EVERY SHAPE BUT THOSE WITH
THE LIBRARY's ELEVEN SWITCHES. That all of these hold together: no example is known. What the tables
hold. Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.C.HasOf
import Johnson.Road.K4.C.StreamsThere
import Johnson.Road.K4.C.TokReads
import Johnson.Road.K4.C.NormsPlanOf
import Johnson.Road.K4.C.PlanLens
import Johnson.Road.K4.Reads.NormRowEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Reads TableAsk TableAt layTables tableAsks matIx readsOf aff0)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First (P6.Row.ofDigits)
open OnBytes.Desc.First.K4 (digitsAt)
open OnBytes.Desc.First.K4.Reads (EntsIn entsIn_ofConst entsIn_add all_mapM all_flatten_mapM
  ofDigits_four)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts matsOf readsAt wtsFit affFits valAff? rowForms
  rowMaps)
open Inst.Model.FFSeg (Dim Arr Cell)

/-- The structure that the honest side's envOf returns. -/
def envPub (Q : K4Pub) (tab : List TableAt) (iU3 : ℕ) (zk : Array (Array E)) : Env :=
  { y := Q.P.y, sc := Q.P.sc, g := Q.g, iU3 := iU3
    K3 := ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := zk }

variable {Q : K4Pub} {iU3 : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **The structure which the forms read is made.** CONDITIONAL: on hU and hl. -/
theorem envOf_pub (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (p : Pts) :
    OnBytes.Desc.First.K4.Honest.envOf Q p = some (envPub Q r.1 iU3 p.fo.zk) := by
  obtain ⟨tab, laid, n⟩ := r
  simp only [OnBytes.Desc.First.K4.Honest.envOf, hU, hl, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  rfl

/-- The point r_tV is among the points of the matrix of rows. -/
theorem rtV_in {y : Lay} {rd : Reads} (e : readsOf y = .ok rd) : "r_tV" ∈ rd.rdAR := by
  unfold Layer.readsOf at e
  dsimp only at e
  obtain ⟨_, e⟩ := ok_of_refuse e
  cases e
  simp

/-- Its family is asked for. -/
theorem ask_rtV (y : Lay) (rd : Reads) (g : ℕ) (h : "r_tV" ∈ rd.rdAR) :
    (⟨"ar" ++ "@" ++ "r_tV", (matIx y).iAR, 1, y.T, "r_tV", false⟩ : TableAsk) ∈
      tableAsks y rd g :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨"r_tV", h, rfl⟩)))

/-- A walk all of whose steps return returns. -/
theorem list_mapM_there {α β : Type} {g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, (g x).isSome = true) → ∃ L, l.mapM g = some L
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    obtain ⟨L, hL⟩ := list_mapM_there l fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨b :: L, by rw [List.mapM_cons, hb, hL]; rfl⟩

/-- The same over an array. -/
theorem amapM_there {α β : Type} {g : α → Option β} (a : Array α)
    (h : ∀ x ∈ a.toList, (g x).isSome = true) : ∃ b, a.mapM g = some b := by
  obtain ⟨L, hL⟩ := list_mapM_there a.toList h
  exact ⟨L.toArray, by rw [Array.mapM_eq_mapM_toList, hL]; rfl⟩

variable {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- **The table of the family "ar@r_tV"**: found; the one that begins at its first entry; all its
entries within the reader's reach; the honest reads at its entries. CONDITIONAL: on every hypothesis
named. -/
theorem row_table (A : K4Plan hS pc Q.P Q.g tl D)
        (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hK : ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (zk : Array (Array E)) :
    ∃ x ∈ r.1, (envPub Q r.1 iU3 zk).tabAt ("ar@" ++ "r_tV") = some x.first ∧
      (r.1.find? fun z => z.first == x.first) = some x ∧
      Reach (envPub Q r.1 iU3 zk) x.first
        (partsM Q.P.y 2 * (colsM Q.P.y 2 * (rowsM Q.P.y 2 / Q.P.y.T))) ∧
      ∀ (w : K4In) (fo : Forest.Heard) (pt : List (String × Array E))
        (R : OnBytes.Desc.First.K4.Honest.Reads), readsAt Q w fo pt = some R →
        ∀ e, x.first ≤ e → e < x.first + x.len → R.has e = wtsFit Q.P.y fo pt
          (⟨"ar" ++ "@" ++ "r_tV", (matIx Q.P.y).iAR, 1, Q.P.y.T, "r_tV", false⟩ : TableAsk) := by
  have ha := ask_rtV Q.P.y Q.P.rd Q.g (rtV_in A.reads)
  have hmats : matsOf Q = matsR Q.P.y Q.g := A.tails
  obtain ⟨tb, htb, Rch⟩ := reach_family (v := envPub Q r.1 iU3 zk) A.grp A.reads
    (by
      show layTables (matsR Q.P.y Q.g) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r
      rw [← hmats]
      exact hl) rfl hK hb ("ar" ++ "@" ++ "r_tV") 2 Q.P.y.T (by omega)
    ⟨_, ha, rfl, rfl, rfl, rfl⟩
  obtain ⟨x, hxm, hxn, hxf⟩ := tabAt_mem htb
  obtain ⟨hc, _⟩ := layTables_chain _ _ 0 r hl
  subst hxf
  refine ⟨x, hxm, htb, chain_first r.1 0 hc x hxm, Rch, fun w fo pt R hR => ?_⟩
  obtain ⟨q, hq, n1, _, H⟩ := has_in_table hR hl hxm
  obtain ⟨_, L2⟩ := laid_of_layTables _ _ _ _ hl
  have hqa : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map_of_mem hq
  rw [ask_of_name A.reads hqa ha (n1.symm.trans hxn)] at H
  exact H

/-- The cells of a norm's row name entries of the one table that begins where the family does. -/
theorem inOne_rowCells {v : Env} {x : TableAt} {P : String} {i n : ℕ} {cells : Array Aff}
    (ht : v.tabAt ("ar@" ++ P) = some x.first)
    (hx : (v.tab.find? fun z => z.first == x.first) = some x)
    (h : v.rowCells P i n = some cells) (j : ℕ) : InOne v x (cells.getD j aff0) := by
  unfold Env.rowCells at h
  obtain ⟨t, ht', h⟩ := bind_some h
  obtain ⟨tr, -, h⟩ := bind_some h
  obtain rfl : x.first = t := Option.some.inj (ht.symm.trans ht')
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : j < ys.length
  · have e : ys.toArray.getD j aff0 = ys[j] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := InOne v x) (fun _ _ hb => inOne_U3at hx hb) _ ys hys _
      (List.getElem_mem hj)
  · have e : ys.toArray.getD j aff0 = aff0 := by simp [Array.getD, hj]
    rw [e]
    exact entsIn_ofConst _

/-- **The cells of each norm's row at the point r_tV are made.** CONDITIONAL: on every hypothesis
named. -/
theorem rowCells_rtV (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true) {v : Env}
    (hy : v.y = Q.P.y) {b : ℕ} (htb : v.tabAt ("ar@" ++ "r_tV") = some b)
    (Rch : Reach v b (partsM Q.P.y 2 * (colsM Q.P.y 2 * (rowsM Q.P.y 2 / Q.P.y.T)))) {i : ℕ}
    (hi : i < Q.P.y.NI) : ∃ cells, v.rowCells "r_tV" i 99 = some cells := by
  have Ad := admitted_of_layout A.lay A.sw.p3
  have Sw : Switches Q.P.y.h := by rw [Ad.shape]; exact A.sw
  have h4 : Q.P.y.h.p4 = true := by rw [Ad.shape]; exact hp4
  obtain ⟨trow, hT, -, -, -, hJ, -⟩ := ten_of Ad.laid Sw .D (Or.inl rfl)
  have hJ' : trow.J = 99 := hJ
  have hi' : i < 2 * 2 ^ Q.P.y.h.ll := by
    have e1 := (normsPlan_of_plan A).NI
    have e2 : D.nNu = (dimOf hS).nNu := A.sized.nNu_eq
    rw [e1, e2, ← Ad.shape] at hi
    exact hi
  obtain ⟨cells, hc⟩ := amapM_there (g := fun j => v.U3at b (trow.OFF + i * 99 + j))
    (Array.range 99) (fun j hj => by
      have hj' : j < 99 := by simpa using hj
      show (v.U3at b (trow.OFF + i * 99 + j)).isSome = true
      have e : trow.OFF + i * 99 + j = tenCell trow.place 0 i j := by
        show _ = trow.OFF + (0 * trow.cnt + i) * trow.J + j
        rw [hJ', Nat.zero_mul, Nat.zero_add]
      rw [e, (place_eq_feat Ad.laid Sw (sized_dimOf _) .D (Or.inl rfl) hT 0 _ _).1]
      have hv : (⟨.D, 0, i, j, 0⟩ : Cell).Valid (dimOf Q.P.y.h) :=
        ⟨Nat.zero_lt_one, hi', hj', Inst.Model.FFSeg.IndexFacts.T_pos _⟩
      obtain ⟨-, hlt⟩ := valid_inMat (laid2_of_layout A.lay) Sw (sized_dimOf _) h4 hv
      rw [Nat.mul_assoc] at hlt
      exact Rch _ hlt)
  refine ⟨cells, ?_⟩
  have hT' : Q.P.y.T_ "row" = some trow := hT
  unfold Env.rowCells
  rw [htb, hy, hT']
  exact hc

/-- The one point at which the rows' fields are read at token t: r_tV, laid at the token's bits. -/
abbrev tokPt (Q : K4Pub) (t : ℕ) : List (String × Array E) :=
  [("r_tV", OnBytes.Desc.First.K4.Honest.bitsOf Q.P.y.h.lt t)]

/-- **THE ROWS' FIELDS ARE LAID AS TABLES ON THE TOKENS.** CONDITIONAL: on every hypothesis named.
-/
theorem rowMaps_returns (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true)
    (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hK : ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (w : K4In) (p : Pts) : ∃ ms, rowMaps Q w p = some ms := by
  obtain ⟨x, hxm, htb, hfx, Rch, H⟩ := row_table A hl hK hb p.fo.zk
  have hT : Q.P.y.T = 2 ^ Q.P.y.h.lt := by
    rw [(normsPlan_of_plan A).T, (planLens_of_plan A).2.2.1]
  -- the forms
  obtain ⟨L, hL⟩ := list_mapM_there (g := fun i =>
      (digitsAt (envPub Q r.1 iU3 p.fo.zk) "r_tV" i).map fun Dg =>
        [(P6.Row.ofDigits Dg).a, (P6.Row.ofDigits Dg).b, (P6.Row.ofDigits Dg).Rlo,
          (P6.Row.ofDigits Dg).Rhi]) (List.range Q.P.y.NI) (fun i hi => by
    obtain ⟨cells, hc⟩ := rowCells_rtV A hp4 (v := envPub Q r.1 iU3 p.fo.zk) rfl htb Rch
      (List.mem_range.mp hi)
    show ((digitsAt (envPub Q r.1 iU3 p.fo.zk) "r_tV" i).map _).isSome = true
    unfold digitsAt
    rw [hc]
    rfl)
  have hfs : rowForms (envPub Q r.1 iU3 p.fo.zk) = some L.flatten.toArray := by
    unfold rowForms
    exact congrArg (Option.map fun l : List (List Aff) => l.flatten.toArray) hL
  have hIn : ∀ f ∈ L.flatten, InOne (envPub Q r.1 iU3 p.fo.zk) x f :=
    all_flatten_mapM (Pr := InOne (envPub Q r.1 iU3 p.fo.zk) x) (fun i l hl' f hf => by
      obtain ⟨Dg, hD, e⟩ := map_some hl'
      subst e
      unfold digitsAt at hD
      obtain ⟨cells, hc, e⟩ := map_some hD
      subst e
      exact ofDigits_four (fun j => entsIn_add (inOne_rowCells htb hfx hc j) (entsIn_ofConst _))
        f hf) _ L hL
  -- the reads
  obtain ⟨Rs, hRs⟩ := amapM_there (g := fun t => readsAt Q w p.fo (tokPt Q t))
    (Array.range (2 ^ Q.P.y.h.lt)) (fun t _ => by
      obtain ⟨R, hR⟩ := readsAt_of_lay hl w p.fo (tokPt Q t)
      show (readsAt Q w p.fo (tokPt Q t)).isSome = true
      rw [hR]
      rfl)
  have hRin : ∀ R ∈ Rs.toList, ∃ t, readsAt Q w p.fo (tokPt Q t) = some R := by
    rw [Array.mapM_eq_mapM_toList] at hRs
    obtain ⟨ys, hys, e⟩ := map_some hRs
    subst e
    exact all_mapM (Pr := fun R => ∃ t, readsAt Q w p.fo (tokPt Q t) = some R)
      (fun t _ hb => ⟨t, hb⟩) _ ys hys
  -- each form is valued at each token
  obtain ⟨ms, hms⟩ := amapM_there (g := fun f => Rs.mapM fun R =>
      valAff? (envPub Q r.1 iU3 p.fo.zk) R (fun _ => zeroE) f) L.flatten.toArray (fun f hf => by
    obtain ⟨b, hb⟩ := amapM_there (g := fun R =>
        valAff? (envPub Q r.1 iU3 p.fo.zk) R (fun _ => zeroE) f) Rs (fun R hR => by
      obtain ⟨t, ht⟩ := hRin R hR
      have hfit : affFits (envPub Q r.1 iU3 p.fo.zk) R f = true :=
        affFits_of_inOne (hIn f (by simpa using hf)) fun e h1 h2 => by
          rw [H w p.fo _ R ht e h1 h2, fit_found
            (p := ("r_tV", OnBytes.Desc.First.K4.Honest.bitsOf Q.P.y.h.lt t)) rfl rfl]
          simp [OnBytes.Desc.First.K4.Honest.bitsOf, hT]
      show (valAff? (envPub Q r.1 iU3 p.fo.zk) R (fun _ => zeroE) f).isSome = true
      unfold valAff?
      rw [if_pos hfit]
      rfl)
    show (Rs.mapM fun R => valAff? (envPub Q r.1 iU3 p.fo.zk) R (fun _ => zeroE) f).isSome = true
    rw [hb]
    rfl)
  exact ⟨ms, Option.bind_eq_some_iff.mpr ⟨_, envOf_pub hU hl p, Option.bind_eq_some_iff.mpr
    ⟨_, hfs, Option.bind_eq_some_iff.mpr ⟨Rs, hRs, hms⟩⟩⟩⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.envOf_pub
#print axioms OnBytes.Road.K4.C.rtV_in
#print axioms OnBytes.Road.K4.C.ask_rtV
#print axioms OnBytes.Road.K4.C.list_mapM_there
#print axioms OnBytes.Road.K4.C.amapM_there
#print axioms OnBytes.Road.K4.C.row_table
#print axioms OnBytes.Road.K4.C.inOne_rowCells
#print axioms OnBytes.Road.K4.C.rowCells_rtV
#print axioms OnBytes.Road.K4.C.rowMaps_returns
