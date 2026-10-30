-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietHeadTables.lean: THE HEAD's TABLES ON SHAPES, AND THE QUIET STEP BEHIND
THE SENDING OF THE READS AT THE HEAD's LINK AS A STEP ON THE CHAIN's SHAPE ALONE. General laws;
nothing is evaluated.
  1 `TabsS`, `tabs3`, `addS`, `parts_sh`, **`tableAdded_sh`**: one table more (Own.tableAdded,
    Johnson/Desc/Own/HeadTabs.lean), seen through the parts' shapes, the vector's length and the
    table of the tables: of a table's weights their number alone enters.
  2 `toOption_need`, `toOption_named`. The weights' sizes: `longPhiS` | `longPhi_sz`, `ztS` |
    `zk_size` | `ztOf_sz`, `planeS` | `plane_sz`. `asksS`: the fifteen lines, each with the number
    of its weights. **`tablesS h L hp x g`**: the maker's text on shapes: of the head's public
    shape, its layout, the plan, the shape of what the head's own rounds heard (HeadHeardSh) and the
    shape of the lookup's record (HeardAll). **`tables_sh`**: (tables h L hp cov x).toOption.map
    tabsSh = tablesS h L hp (headHeardSh x) (heardAll x.g1): the maker returns just where its text
    on shapes returns, and what the chain's shape sees of the tables is that text's value. One
    equation; no premise; THE COVERED POSITIONS DO NOT ENTER: no test of the maker reads a value.
  3 **`headReadsG P`**: the step on the chain's shape alone: headG (ReadsQuietHeadShape.lean) at
    tablesS of HeadSh.x and look. `headReads_sh`: where the covered positions can be said, the
    block's decision, seen through the shape, IS that step. `head_covered`. **`headReads_carries`**
    (strong: behind a yes the step returns the shape behind). **`headReads_returns`**: where the
    step returns and the covered positions can be said, the block says yes.
By head_sh (ReadsQuietHeadShape.lean), Rows.lean's foldlM_mk, the library's eqTab_size
(Johnson/Road/FormsKeysEq.lean), blockRows_size (Johnson/Desc/Reads/FoldAll.lean), bind_ok
(ReadsQuietLaws.lean).
Limits. "The covered positions can be said" (S.covered returns: four tests on the request's words
and the heard reply's token) IS A PREMISE ON THE STATE BEYOND ITS SHAPE: the step reads no covered
position, so its return does not say that S.covered returns. "ON THE CHAIN's SHAPE ALONE" is said of
the definition headReadsG, not of headReads_sh and headReads_returns. The bare block: the guards of
a seat are not in it. No state is shown at which the step returns. Nothing on soundness,
completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.ReadsQuietHeadShape
import Johnson.Desc.First.Shape.Rows
import Johnson.Desc.Reads.FoldAll
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc (need named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Road (eqTab_size)
open VerifiableInference.Reads (blockRows_size)

/-! ## 1 One table more, on shapes -/

/-- What is kept of the tables while they are made: the parts' shapes, the vector's length so far,
the table of the tables. -/
abbrev TabsS : Type := List FunSh × Nat × List (String × Nat × Nat)

def tabs3 (t : Tables) : TabsS := (t.funs.toList.map funSh, t.p, t.tab)

/-- One table more. a: the first matrix, the number of parts, a stretch's length, THE NUMBER OF
WEIGHTS, the name. -/
def addS (mats : Array TMat) (s : TabsS) (a : Nat × Nat × Nat × Nat × String) : Option TabsS :=
  let r := (List.range a.2.1).foldl
    (fun (u : List FunSh × Nat) q =>
      (u.1 ++ [{ mat := a.1 + q, len := a.2.2.1, weights := a.2.2.2.1, tree := 2, start := u.2 }],
        u.2 + (mats.getD (a.1 + q) {}).k * ((mats.getD (a.1 + q) {}).m / a.2.2.1)))
    (s.1, s.2.1)
  if r.2 == s.2.1 then none
  else some (r.1, r.2, s.2.2 ++ [(a.2.2.2.2, s.2.1, r.2 - s.2.1)])

theorem parts_sh (mats : Array TMat) (M0 Lf : Nat) (phi : Array E) :
    ∀ (l : List Nat) (u : Array HFun × Nat),
      ((l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) u).1.toList.map
              funSh,
       (l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) u).2) =
      l.foldl (fun (u : List FunSh × Nat) q =>
        (u.1 ++ [{ mat := M0 + q, len := Lf, weights := phi.size, tree := 2, start := u.2 }],
          u.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf)))
        (u.1.toList.map funSh, u.2)
  | [], _ => rfl
  | q :: l, u => by
    rw [List.foldl_cons, List.foldl_cons, parts_sh mats M0 Lf phi l]
    congr 2
    rw [Array.toList_push, List.map_append]
    rfl

theorem tableAdded_sh (mats : Array TMat) (t : Tables) (M0 parts Lf : Nat) (phi : Array E)
    (nm : String) :
    (Own.tableAdded mats t M0 parts Lf phi nm).map tabs3 =
      addS mats (tabs3 t) (M0, parts, Lf, phi.size, nm) := by
  have h := parts_sh mats M0 Lf phi (List.range parts) (t.funs, t.p)
  unfold Own.tableAdded addS tabs3
  dsimp only
  rw [← h]
  dsimp only
  split
  · rfl
  · rfl

/-! ## 2 The maker of the head's tables, on shapes -/

theorem toOption_need {α : Type} (n : String) (b : Bool) (f : Unit → Except String α) :
    (need n b >>= f).toOption = if b then (f ()).toOption else none := by
  cases b <;> rfl

theorem toOption_named {α β : Type} (n : String) (o : Option β) (f : β → Except String α) :
    (named n o >>= f).toOption = o.bind fun a => (f a).toOption := by
  cases o <;> rfl

/-- The size of a block's weights at a point of p coordinates. -/
def longPhiS (p ls lt : Nat) : Nat := 2 ^ (min ls p - 0) * 2 ^ (min (ls + lt) p - ls)

theorem longPhi_sz (p : Array E) (ls lt : Nat) : (longPhi p ls lt).size = longPhiS p.size ls lt :=
    by
  unfold longPhi longPhiS
  rw [blockRows_size, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract]

/-- The number of coordinates of a call's key point that belong to the positions. -/
def ztS (h : Shape) (L : HL) (g : HeardAll) (q : Nat) : Nat :=
  min ((L.calls.getD q default).lJ + h.lt) (g.zk.getD q 0) - (L.calls.getD q default).lJ

theorem zk_size (g1 : Forest.Heard) (q : Nat) :
    (g1.zk.getD q #[]).size = (heardAll g1).zk.getD q 0 := by
  show _ = (g1.zk.toList.map (·.size)).getD q 0
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases g1.zk[q]? <;> rfl

theorem ztOf_sz (h : Shape) (L : HL) (g1 : Forest.Heard) (q : Nat) :
    (ztOf h L g1 q).size = ztS h L (heardAll g1) q := by
  unfold ztOf ztS
  dsimp only
  rw [Array.size_extract, zk_size]

/-- The size of the weights under which the planes are read; nothing where the maker refuses. -/
def planeS (g : HeardAll) (lm e : Nat) : Option Nat :=
  let z := if e = 0 then g.zb0 else g.zb1
  if lm < 5 || lm > g.shape.kT + 5 then none
  else some (2 ^ ((min g.shape.kT z - (g.shape.kT + 5 - lm)) + (min z z - (g.shape.kT +
      g.shape.cK))))

theorem plane_sz (g1 : Forest.Heard) (lm e : Nat) :
    (Own.planeWeights g1 lm e).map (·.size) = planeS (heardAll g1) lm e := by
  unfold Own.planeWeights planeS
  dsimp only
  have hk : (heardAll g1).shape = g1.shape := rfl
  rw [hk]
  by_cases hc : (decide (lm < 5) || decide (lm > g1.shape.kT + 5)) = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc, Option.map_some, eqTab_size, Array.size_append, Array.size_extract,
      Array.size_extract]
    by_cases he : e = 0
    · simp only [he, if_true]
      rfl
    · simp only [he, if_false]
      rfl

/-- The fifteen lines, each with the NUMBER of its weights. -/
def asksS (h : Shape) (L : HL) (x : HeadHeardSh) (g : HeardAll) (ZV YN qFC qROW b0 b1 : Nat) :
    List (Nat × Nat × Nat × Nat × String) :=
  [(0, h.NHf, 2 ^ h.la, longPhiS x.Zl h.ls h.lt, "hf@Z"),
   (0, h.NHf, 2 ^ h.la, 2 ^ h.la, "hf@phiZ"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhiS ZV h.ls h.lt, "xbL@Z_V"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhiS YN h.ls h.lt, "xbL@Y_N"),
   (h.NHf, 1, h.T, 2 ^ ztS h L g qFC, "hd@zt_FC"),
   (h.NHf, 1, h.T, 2 ^ x.tH.r, "hd@r_H"),
   (h.NHf + 1, 1, h.T, 2 ^ ztS h L g qROW, "hr@zt_ROW"),
   (h.NHf + 1, 1, h.T, 2 ^ x.PV, "hr@P_V"),
   (h.NHf + 1, 1, h.T, 2 ^ x.tV.r, "hr@r_tV"),
   (h.NHf + 1, 1, h.T, 2 ^ x.tN.r, "hr@rt_N"),
   (h.NHf + 1, 1, h.T, 2 ^ ztS h L g x.qH, "hr@phiC"),
   (h.NHf + 1, 1, h.T, 2 ^ ztS h L g x.qH, "hr@rhoC"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b0, "bH-bits-0"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b1, "bH-bits-1"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, 2 ^ h.lmbH, "bH-pin")]

/-- **The maker of the head's tables, on shapes**: of the head's public shape, its layout, the plan,
the shape of what the head's own rounds heard and the shape of the lookup's record. -/
def tablesS (h : Shape) (L : HL) (hp : HPlanH2) (x : HeadHeardSh) (g : HeardAll) :
    Option (List FunSh × List (String × Nat × Nat)) :=
  if !hp.tl.funClosed then
    (if h.la > x.wpl.r then none else some (min x.wpl.r x.wpl.r - (x.wpl.r - h.la))).bind fun ZV =>
    let zj := min (L.calls.getD x.qN default).lJ (g.zk.getD x.qN 0) - 0
    (if h.ls > zj then none else some (min zj zj - (zj - h.ls))).bind fun low =>
    if (low + x.tN.r == h.la && h.la == h.ls + h.lt) then
      (Own.callWith L "CNF").bind fun qFC =>
      (Own.callWith L "ROW").bind fun qROW =>
      (planeS g h.lmbH 0).bind fun b0 =>
      (planeS g h.lmbH 1).bind fun b1 =>
      ((asksS h L x g ZV (low + x.tN.r) qFC qROW b0 b1).foldlM (addS hp.tl.mats)
        ([], 0, [])).bind fun t =>
      if t.2.1 == hp.nU.getD 2 0 then some (t.1, t.2.2) else none
    else none
  else none

/-- **THE MAKER, SEEN THROUGH THE SHAPES, IS ITS TEXT ON SHAPES**: it returns just where that text
returns, and what the chain's shape sees of the tables is that text's value. One equation; no
premise; the covered positions do not enter. -/
theorem tables_sh (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) :
    (tables h L hp cov x).toOption.map tabsSh =
      tablesS h L hp (headHeardSh x) (heardAll x.g1) := by
  have hT : (if h.la > (headHeardSh x).wpl.r then none
      else some (min (headHeardSh x).wpl.r (headHeardSh x).wpl.r - ((headHeardSh x).wpl.r - h.la)))
          =
      (Own.tailOf x.wpl.r h.la).map (·.size) := by
    unfold Own.tailOf Own.cutTail
    show (if h.la > x.wpl.r.size then none else some _) = _
    by_cases hc : h.la > x.wpl.r.size
    · rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc]
      show some _ = some (x.wpl.r.extract _ _).size
      rw [Array.size_extract]
      rfl
  have hz : (zjOf L x.g1 x.qN).size =
      min (L.calls.getD (headHeardSh x).qN default).lJ
        ((heardAll x.g1).zk.getD (headHeardSh x).qN 0) - 0 := by
    unfold zjOf
    rw [Array.size_extract, zk_size]
    rfl
  have hL : (if h.ls > min (L.calls.getD (headHeardSh x).qN default).lJ
        ((heardAll x.g1).zk.getD (headHeardSh x).qN 0) - 0 then none
      else some (min
        (min (L.calls.getD (headHeardSh x).qN default).lJ
          ((heardAll x.g1).zk.getD (headHeardSh x).qN 0) - 0)
        (min (L.calls.getD (headHeardSh x).qN default).lJ
          ((heardAll x.g1).zk.getD (headHeardSh x).qN 0) - 0) -
        (min (L.calls.getD (headHeardSh x).qN default).lJ
          ((heardAll x.g1).zk.getD (headHeardSh x).qN 0) - 0 - h.ls))) =
      (Own.cutTail (zjOf L x.g1 x.qN) h.ls).map (·.2.size) := by
    rw [← hz]
    unfold Own.cutTail
    by_cases hc : h.ls > (zjOf L x.g1 x.qN).size
    · rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc]
      show some _ = some ((zjOf L x.g1 x.qN).extract _ _).size
      rw [Array.size_extract]
  unfold tables tablesS
  simp only [toOption_need, toOption_named]
  rw [hT, hL, ← plane_sz, ← plane_sz]
  by_cases hc : (!hp.tl.funClosed) = true
  · rw [if_pos hc, if_pos hc]
    cases Own.tailOf x.wpl.r h.la with
    | none => rfl
    | some ZV =>
      cases Own.cutTail (zjOf L x.g1 x.qN) h.ls with
      | none => rfl
      | some low =>
        simp only [Option.bind_some, Option.map_some]
        have hY : (longPoint low.2 x.tN.r).size = low.2.size + (headHeardSh x).tN.r := by
          unfold longPoint
          rw [Array.size_append]
          rfl
        rw [hY]
        by_cases h4 : (low.2.size + (headHeardSh x).tN.r == h.la && h.la == h.ls + h.lt) = true
        · rw [if_pos h4, if_pos h4]
          cases Own.callWith L "CNF" with
          | none => rfl
          | some qFC =>
            cases Own.callWith L "ROW" with
            | none => rfl
            | some qROW =>
              cases Own.planeWeights x.g1 h.lmbH 0 with
              | none => rfl
              | some b0 =>
                cases Own.planeWeights x.g1 h.lmbH 1 with
                | none => rfl
                | some b1 =>
                  simp only [Option.bind_some, Option.map_some]
                  have hF := foldlM_mk tabs3
                    (fun a : Nat × Nat × Nat × Array E × String =>
                      (a.1, a.2.1, a.2.2.1, a.2.2.2.1.size, a.2.2.2.2))
                    (fun t a => Own.tableAdded hp.tl.mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
                    (addS hp.tl.mats)
                    (fun t a => tableAdded_sh hp.tl.mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
                  have hc1 : (costWeights cov (ztOf h L x.g1 x.qH)).1.size =
                      2 ^ ztS h L (heardAll x.g1) (headHeardSh x).qH := by
                    unfold costWeights
                    dsimp only
                    rw [Array.size_mapIdx, eqTab_size, ztOf_sz]
                    rfl
                  have hc2 : (costWeights cov (ztOf h L x.g1 x.qH)).2.2.size =
                      2 ^ ztS h L (heardAll x.g1) (headHeardSh x).qH := by
                    unfold costWeights
                    dsimp only
                    rw [Array.size_mapIdx, eqTab_size, ztOf_sz]
                    rfl
                  have hp5 : (Forest.phiP h.lmbH).size = 2 ^ h.lmbH := by simp [Forest.phiP]
                  have hA := hF [(0, h.NHf, 2 ^ h.la, longPhi x.Zl h.ls h.lt, "hf@Z"),
                    (0, h.NHf, 2 ^ h.la,
                      Array.map (fun i => (costWeights cov (ztOf h L x.g1 x.qH)).1.getD (i % h.T)
                          zeroE)
                        (Array.range (2 ^ h.la)), "hf@phiZ"),
                    (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhi ZV h.ls h.lt, "xbL@Z_V"),
                    (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhi (longPoint low.2 x.tN.r) h.ls h.lt,
                      "xbL@Y_N"),
                    (h.NHf, 1, h.T, eqTab (ztOf h L x.g1 qFC), "hd@zt_FC"),
                    (h.NHf, 1, h.T, eqTab x.tH.r, "hd@r_H"),
                    (h.NHf + 1, 1, h.T, eqTab (ztOf h L x.g1 qROW), "hr@zt_ROW"),
                    (h.NHf + 1, 1, h.T, eqTab x.PV, "hr@P_V"),
                    (h.NHf + 1, 1, h.T, eqTab x.tV.r, "hr@r_tV"),
                    (h.NHf + 1, 1, h.T, eqTab x.tN.r, "hr@rt_N"),
                    (h.NHf + 1, 1, h.T, (costWeights cov (ztOf h L x.g1 x.qH)).1, "hr@phiC"),
                    (h.NHf + 1, 1, h.T, (costWeights cov (ztOf h L x.g1 x.qH)).2.2, "hr@rhoC"),
                    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b0, "bH-bits-0"),
                    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b1, "bH-bits-1"),
                    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, Forest.phiP h.lmbH, "bH-pin")] {}
                  simp only [List.map_cons, List.map_nil, longPhi_sz, Array.size_map,
                    Array.size_range, eqTab_size, ztOf_sz, hc1, hc2, hp5, hY] at hA
                  have hA' : (asksS h L (headHeardSh x) (heardAll x.g1) ZV.size
                      (low.2.size + (headHeardSh x).tN.r) qFC qROW b0.size b1.size).foldlM
                      (addS hp.tl.mats) ([], 0, []) = _ := hA.symm
                  rw [hA']
                  generalize List.foldlM
                    (fun (t : Tables) (a : Nat × Nat × Nat × Array E × String) =>
                      Own.tableAdded hp.tl.mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) {} _ = fo
                  cases fo with
                  | none => rfl
                  | some t =>
                    simp only [Option.bind_some, Option.map_some]
                    show Option.map tabsSh (if (t.p == hp.nU.getD 2 0) = true then some t else none)
                        =
                      if (t.p == hp.nU.getD 2 0) = true then some (tabsSh t) else none
                    split <;> rfl
        · rw [if_neg h4, if_neg h4]
          rfl
  · rw [if_neg hc, if_neg hc]
    rfl

/-! ## 3 The quiet step at the head's link, on the shape alone -/

/-- **THE STEP ON THE CHAIN's SHAPE ALONE**: what the shape sees of the tables is made off the shape
    of
what the head's own rounds heard (HeadSh.x) and of the lookup's record that they hand on (look). -/
def headReadsG (P : PH) (a : ChainSh) : Option ChainSh :=
  match a.head.bind (·.x), a.look with
  | some xs, some g => headG (tailSh P.hp.tl) (tablesS P.h P.L P.hp xs g) a
  | _, _ => none

/-- Where the covered positions can be said, the block's decision, seen through the shape, IS the
step on the shape alone. -/
theorem headReads_sh (P : PH) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hcov : (s.covered P.h.T P.h.V).toOption.isSome = true) :
    (((head P).decide s rs gs).toOption.map chainSh) = headReadsG P (chainSh s) := by
  rw [head_sh]
  unfold headReadsG
  obtain ⟨cov, hc⟩ := Option.isSome_iff_exists.1 hcov
  cases hh : s.here with
  | head a =>
    have h5 : (chainSh s).head = some (headSh a) := by
      show headOf s.here = _
      rw [hh]
      rfl
    cases ho : a.opened with
    | false =>
      have h1 : ((chainSh s).here != 3) = true := by
        show (hereNo s.here != 3) = true
        rw [hh]
        simp only [hereNo, ho]
        rfl
      have e : ∀ m, headG (tailSh P.hp.tl) m (chainSh s) = none := fun m => by
        unfold headG
        rw [if_pos h1]
      rw [e]
      split
      · exact (e _).symm
      · rfl
    | true =>
      have hl : (chainSh s).look = a.x.map fun x => heardAll x.g1 := by
        show s.look?.map heardAll = _
        unfold S.look?
        rw [hh]
        dsimp only
        rw [ho]
        cases a.x <;> rfl
      have htb : headTabsAt P s = a.x.bind fun x => (tables P.h P.L P.hp cov x).toOption := by
        unfold headTabsAt
        rw [hh]
        dsimp only
        rw [ho, if_pos rfl, hc]
        rfl
      have hx : ((some (headSh a)).bind fun x => x.x) = a.x.map headHeardSh := rfl
      rw [h5, hl, htb, hx]
      cases a.x with
      | none =>
        show headG _ none _ = none
        unfold headG
        split
        · rfl
        · rfl
      | some x =>
        show headG _ (((tables P.h P.L P.hp cov x).toOption).map tabsSh) _ =
          headG _ (tablesS P.h P.L P.hp (headHeardSh x) (heardAll x.g1)) _
        rw [tables_sh]
  | _ =>
    have h5 : (chainSh s).head = none := by
      show headOf s.here = _
      rw [hh]
      rfl
    have h1 : ((chainSh s).here != 3) = true := by
      show (hereNo s.here != 3) = true
      rw [hh]
      rfl
    rw [h5]
    unfold headG
    rw [if_pos h1]
    rfl

/-- A yes of the block: the covered positions could be said. -/
theorem head_covered {P : PH} {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (head P).decide s rs gs = .ok t) : (s.covered P.h.T P.h.V).toOption.isSome = true := by
  unfold head at h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨cov, hc, -⟩ := bind_ok h
    cases hq : s.covered P.h.T P.h.V with
    | ok c => rfl
    | error e =>
      rw [hq] at hc
      cases hc
  · cases h

/-- **"Carries", strong.** -/
theorem headReads_carries {P : PH} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (head P).decide s rs gs = .ok t) :
    headReadsG P (chainSh s) = some (chainSh t) := by
  rw [← headReads_sh P s rs gs (head_covered h), h]
  rfl

/-- **"Returns"**: where the step returns and the covered positions can be said, the block says yes.
-/
theorem headReads_returns {P : PH} {s : S} {u : ChainSh} (hg : headReadsG P (chainSh s) = some u)
    (hcov : (s.covered P.h.T P.h.V).toOption.isSome = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) : ∃ t, (head P).decide s rs gs = .ok t := by
  have e := headReads_sh P s rs gs hcov
  rw [hg] at e
  cases hd : (head P).decide s rs gs with
  | ok t => exact ⟨t, rfl⟩
  | error w =>
    rw [hd] at e
    cases e

end VerifiableInference.Desc.K8.ReadsQuiet

#print axioms VerifiableInference.Desc.K8.ReadsQuiet.parts_sh
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.tableAdded_sh
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.toOption_need
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.toOption_named
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.longPhi_sz
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.zk_size
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.ztOf_sz
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.plane_sz
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.tables_sh
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.headReads_sh
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.head_covered
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.headReads_carries
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.headReads_returns
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.TabsS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.tabs3
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.addS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.longPhiS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.ztS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.planeS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.asksS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.tablesS
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.headReadsG
