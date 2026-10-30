-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5LeftAll.lean: the law of kind K5: the rows that the kind's runs add are the
rows
of which the law speaks. leftP (Att/LeftP.lean), where it returns, taken apart: each of its forms is
left
(or leftKey) of that sumcheck's record at weights that are named here, and so formOf of the record
at a
summand that is written out.

Main names:
  `wDivision`, `wBelow`, `wOn`, `wAtIndex`, `wCells`: the weights, as leftP's own lines write them.
  `ScoresLeft`, `LeftIs`, `leftP_spec`: all of leftP's returns.
  `leftKey_spec`: leftKey returns formOf at the library's keyFlat on what lies under the end values'
    slots.
  `out_ini`, `leftD_uholds`: leftKey's row at letters made of the sumcheck by degrees, with (D4)
    paid.
  `LeftIs.forms`: every row is formOf of its record at a named summand.

Sources: OnBytes/Tie/Pv/Att/Flat.lean (sc3Flat, keyFlat, keyTermFlat, scdNum, keyFlat_read);
ScdTop.lean
(scdNum_lt); Cb/Pv/Att/Scd.lean (ScdSize, Scd, scdS); OnBytes/Model/AttentionShape.lean (eqPts,
eqPair: the
kind's own eqPts is that text, by unfolding).
Limits: one direction, from a return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5LeftLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Att (sc3Flat keyFlat keyTermFlat)
open VerifiableInference.Desc.Part

/-! ## Option's mapM -/

theorem optMapM_spec {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β), l.mapM f = some bs →
    List.Forall₂ (fun a b => f a = some b) l bs
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨bs', h3, h4⟩ := Option.bind_eq_some_iff.1 h2
    simp only [Option.pure_def, Option.some.injEq] at h4
    subst h4
    exact .cons h1 (optMapM_spec f l bs' h3)

theorem guard_some {p : Prop} [Decidable p] {u : Unit} (h : (guard p : Option Unit) = some u) : p := by
  by_contra hc
  simp [guard, hc, failure] at h

/-! ## The weights, as leftP's lines write them -/

def wDivision (g : Geo) (pw zW : Array E) (h : Heard) : Array E :=
  let r := chal h.division
  pw.map (mulE · (mulE (eqPts (zW.extract 1 (1 + g.lgk)) (r.extract 0 g.lgk))
    (eqPts (zW.extract (1 + g.lgk) (1 + g.lgk + g.lt)) (r.extract g.lgk (g.lgk + g.lt)))))

def wBelow (g : Geo) (pw zW : Array E) (h : Heard) : Array E :=
  let r := chal h.below
  let atS := g.lgk + (g.lnT - 1)
  let w := tileSums g (eqTab (r.extract g.lgk atS)) (eqTab (r.extract atS (atS + g.lnT)))
  pw.map (mulE · (mulE (overTileRows g w.1 (eqTab ((zW.extract (1 + g.lgk) (1 + g.lgk + g.lt)).extract 0 g.lnT)))
    (eqPts (zW.extract 1 (1 + g.lgk)) (r.extract 0 g.lgk))))

def wOn (g : Geo) (pw zW : Array E) (h : Heard) : Array E :=
  let r := chal h.on
  pw.map (mulE · (mulE (eqPts (zW.extract 1 (1 + g.lgk)) (r.extract 0 g.lgk))
    (eqPts ((zW.extract (1 + g.lgk) (1 + g.lgk + g.lt)).extract 0 g.lnT) (r.extract g.lgk (g.lgk + g.lnT)))))

def wAtIndex (g : Geo) (h : Heard) : Array E :=
  let rho := chal h.atIndex
  h.om.map (mulE · (mulE (eqPts (h.point.extract 0 g.lgk) (rho.extract g.lt (g.lt + g.lgk)))
    (eqPts (h.point.extract g.lgk (g.lgk + g.lt)) (rho.extract 0 g.lt))))

def wCells (g : Geo) (h : Heard) : Array E :=
  let r := chal h.cells
  h.om''.map (mulE · (mulE (mulE (eqPts (h.point.extract (2 * g.lgk + g.lt + 4) (2 * g.lgk + 2 * g.lt + 4))
      (r.extract 0 g.lt))
    (eqPts (h.point.extract (g.lgk + g.lt + 4) (2 * g.lgk + g.lt + 4)) (r.extract g.lt (g.lt + g.lgk))))
    (eqPts (h.point.extract (g.lgk + g.lt) (g.lgk + g.lt + 4)) (r.extract (g.lt + g.lgk) (g.lt + g.lgk + 4)))))

/-- The units' rows, one by one. -/
def ScoresLeft (g : Geo) (zk : Array (Array E)) (F : Fork) (u : UnitG × Nat × MaskedSum.Heard) (f : Aff) : Prop :=
  ∃ W, scoreW g u.1 (zk.getD u.1.call #[]) (chal u.2.2) = some W ∧ left F u.2.2 W = some f

/-- **leftP's returns.** -/
structure LeftIs (g : Geo) (zk : Array (Array E)) (h : Heard) (F : Fork) (l : Left) : Prop where
  nUnits : g.scores.length = h.scores.size
  scores : List.Forall₂ (ScoresLeft g zk F) (g.scores.toArray.zip h.scores).toList l.scores.toList
  rest : ∃ wl : UnitG, g.single .wl = some wl ∧
    (weights wl (zk.getD wl.call #[])).size = g.NP ∧
    (inner wl (zk.getD wl.call #[])).size = 1 + g.lgk + g.lt + g.ldh ∧
    left F h.division (wDivision g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) h) =
      some l.division ∧
    left F h.below (wBelow g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) h) = some l.below ∧
    left F h.on (wOn g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) h) = some l.on ∧
    left F h.atIndex (wAtIndex g h) = some l.atIndex ∧
    leftKey g F h.key (chal h.atIndex) h.om' = some l.key ∧
    left F h.cells (wCells g h) = some l.cells

theorem leftP_spec {g : Geo} {zk : Array (Array E)} {h : Heard} {F : Fork} {l : Left}
    (hl : leftP g zk h F = some l) : LeftIs g zk h F l := by
  unfold leftP at hl
  simp only [Option.bind_eq_bind] at hl
  obtain ⟨_, g1, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨scores, g2, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨wl, g3, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨_, g4, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨division, g5, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨below, g6, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨on, g7, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨atIndex, g8, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨keyRow, g9, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨cells, g10, hl⟩ := Option.bind_eq_some_iff.1 hl
  simp only [Option.pure_def, Option.some.injEq] at hl
  subst hl
  have n1 : g.scores.length = h.scores.size := by
    have := guard_some g1
    simpa using this
  have n4 : (weights wl (zk.getD wl.call #[])).size = g.NP ∧
      (inner wl (zk.getD wl.call #[])).size = 1 + g.lgk + g.lt + g.ldh := by
    have := guard_some g4
    simpa using this
  refine ⟨n1, ?_, wl, g3, n4.1, n4.2, g5, g6, g7, g8, g9, g10⟩
  rw [Array.mapM_eq_mapM_toList] at g2
  obtain ⟨bs, b1, b2⟩ := Option.map_eq_some_iff.1 g2
  subst b2
  refine (optMapM_spec _ _ _ b1).imp fun u f hu => ?_
  obtain ⟨W, w1, w2⟩ := Option.bind_eq_some_iff.1 hu
  exact ⟨W, w1, w2⟩

/-! ## «leftKey»: the sumcheck by degrees -/

theorem key_inner (F : Fork) (s c lt : Nat) (pj : Array E) : ∀ (l : List Nat) (t r : E),
    l.foldlM (fun t k => do
      let y := pj.getD (lt - 1 - k) zeroE
      let v ← F.shown (s + (c + k))
      pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y)))) t = some r →
    r = l.foldl (fun t k => mulE t (addE
      (mulE (F.vp.getD (s + (c + k)) zeroE)
        (subE (addE (pj.getD (lt - 1 - k) zeroE) (pj.getD (lt - 1 - k) zeroE)) oneE))
      (subE oneE (pj.getD (lt - 1 - k) zeroE)))) t
  | [], t, r, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h.symm
  | k :: l, t, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, k1, h1⟩ := Option.bind_eq_some_iff.1 h1
    simp only [Option.pure_def, Option.some.injEq] at h1
    rw [List.foldl_cons, ← shown_val k1, h1]
    exact key_inner F s c lt pj l t' r h2

theorem key_outer (F : Fork) (s lt Lam HA : Nat) (pj om' : Array E) : ∀ (l : List Nat) (a r : E),
    l.foldlM (fun a b => do
      let kc ← F.shown (s + b / HA)
      let t ← (List.range lt).foldlM (fun t k => do
        let y := pj.getD (lt - 1 - k) zeroE
        let v ← F.shown (s + (Lam + b * lt + k))
        pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y)))) (mulE (om'.getD b zeroE) kc)
      pure (addE a t)) a = some r →
    r = l.foldl (fun a b => addE a
      (keyTermFlat lt Lam HA (fun j => F.vp.getD (s + j) zeroE) pj (om'.getD b zeroE) b)) a
  | [], a, r, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h.symm
  | b :: l, a, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨kc, k1, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨t, k2, h1⟩ := Option.bind_eq_some_iff.1 h1
    simp only [Option.pure_def, Option.some.injEq] at h1
    have e := key_inner F s (Lam + b * lt) lt pj _ _ _ k2
    have ea : a' = addE a (keyTermFlat lt Lam HA (fun j => F.vp.getD (s + j) zeroE) pj (om'.getD b zeroE) b) := by
      rw [← h1, e, shown_val k1]
      unfold keyTermFlat
      rfl
    rw [List.foldl_cons, ← ea]
    exact key_outer F s lt Lam HA pj om' l a' r h2

/-- «leftKey» returns formOf at the library's plain function keyFlat on what lies under the end
values' slots. -/
theorem leftKey_spec {g : Geo} {F : Fork} {h : MaskedSum.Heard} {rho om' : Array E} {f : Aff}
    (hf : leftKey g F h rho om' = some f) :
    f = formOf h (keyFlat g.lt g.Lam g.HA g.NP (rho.extract 0 g.lt) (rho.extract g.lt (g.lt + g.lgk))
      ((chal h).extract 0 g.lt) ((chal h).extract g.lt (g.lt + g.lgk))
      ((chal h).extract (g.lt + g.lgk) (2 * g.lt + g.lgk)) om' fun j => F.vp.getD (h.sEnd + j) zeroE) {} := by
  unfold leftKey at hf
  obtain ⟨sum, h1, h2⟩ := Option.bind_eq_some_iff.1 hf
  simp only [Option.pure_def, Option.some.injEq] at h2
  rw [← h2, key_outer F h.sEnd g.lt g.Lam g.HA _ om' _ _ _ h1]
  rfl

/-- **Every row that leftP returns is formOf of its record at a named summand.** -/
theorem LeftIs.forms {g : Geo} {zk : Array (Array E)} {h : Heard} {F : Fork} {l : Left} (a : LeftIs g zk h F l) :
    List.Forall₂ (fun (u : UnitG × Nat × MaskedSum.Heard) f => ∃ S0, f = formOf u.2.2 S0 {})
      (g.scores.toArray.zip h.scores).toList l.scores.toList ∧
    (∃ S0, l.division = formOf h.division S0 {}) ∧ (∃ S0, l.below = formOf h.below S0 {}) ∧
    (∃ S0, l.on = formOf h.on S0 {}) ∧ (∃ S0, l.atIndex = formOf h.atIndex S0 {}) ∧
    (∃ S0, l.key = formOf h.key S0 {}) ∧ (∃ S0, l.cells = formOf h.cells S0 {}) := by
  obtain ⟨wl, _, _, _, b1, b2, b3, b4, b5, b6⟩ := a.rest
  exact ⟨a.scores.imp fun u f ⟨W, _, hw⟩ => ⟨_, left_spec hw⟩, ⟨_, left_spec b1⟩, ⟨_, left_spec b2⟩,
    ⟨_, left_spec b3⟩, ⟨_, left_spec b4⟩, ⟨_, leftKey_spec b5⟩, ⟨_, left_spec b6⟩⟩

/-! ## The key's fourth equation, paid -/

section Typed
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH plain_ini plain_vals scdNum keyFlat_read)
open VerifiableInference.Desc.Part.MaskedSum (PartRowLaw)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

theorem extract_getD (a : Array E) (s e i : Nat) (h : s + i < e) :
    (a.extract s e).getD i zeroE = a.getD (s + i) zeroE := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · rename_i hc
    have : a.size ≤ s + i := by omega
    simp [Array.getElem?_eq_none this]

/-- The output's point, coordinate by coordinate, is the reading of the record's challenges. -/
theorem out_ini {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf)
    (i : Fin S.T.nv) :
    ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt i = ρ.val ((chal hh).getD i.1 zeroE) := by
  obtain ⟨vs, e, F, G, used, e1, sd, _⟩ := h
  obtain ⟨n, e2⟩ := hs
  rw [e1] at e2
  injection e2 with e3 e4
  subst e3 e4
  obtain ⟨_, _, hH, _⟩ := hD
  subst hH
  have hl : D.H.rs.map (·.1.length) = List.ofFn S.T.deg := by
    rw [sd.lens, List.map_map]
    exact List.map_id _
  have hlen : D.H.rs.length = S.T.nv := by
    have := congrArg List.length hl
    simpa using this
  refine (plain_ini ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _ i).trans ?_
  congr 1
  unfold chal
  rw [sd.r, List.dropLast_concat]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases D.H.rs[i.1]? <;> rfl

/-- **«leftKey»'s row at the sumcheck by degrees**, with (D4) paid: from the place's numbers, the
typed state's points
and factors as readings of what was heard, and the end values' tie. -/
theorem leftD_uholds (law : PartRowLaw) {X : Type} {s : ScdSize} (T : Scd K s) (n : ℕ)
    (cl : X → (Fin n → K) → K × T.St) (msg : M → T.J → K) (Lc : X → (Fin n → K) → M → Prop)
    (D : SumH ρ (SumL.ofD T n cl msg Lc)) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP (SumL.ofD T n cl msg Lc) st) (hD : OfP D riders H hh)
    (h : SumAt C st riders H hh Gf) (W : World K) (m : M) {g : Geo} {rho om' : Array E} {f : Aff}
    (hf : leftKey g Gf hh rho om' = some f)
    (g1 : g.lt = s.lt) (g2 : g.lgk = s.lgk) (g3 : g.Lam = s.Lam) (g4 : g.HA = s.HA) (g5 : g.NP = s.pairs)
    (hrho : s.lt + s.lgk ≤ rho.size) (hn : s.Lam + s.pairs * s.lt ≤ H.v.length)
    (hv : D.v = fun a => ρ.val (H.v.getD (scdNum s a) zeroE))
    (hri : ∀ a, T.ri D.st a = ρ.val (rho.getD a.1 zeroE))
    (hrg : ∀ a, T.rg D.st a = ρ.val (rho.getD (s.lt + a.1) zeroE))
    (hom : ∀ b, T.om D.st b = ρ.val (om'.getD b.1 zeroE))
    (D1 : T.plain.our.par.W D.st (msg m) = OnBytes.Road.Hd.place W.slot (T.plain.our.par.vars D.st) hh.first)
    (D2 : T.plain.our.par.inc D.st (msg m) = ρ.val hh.target - C.value ρ W) :
    f.value ρ W = 0 ↔ T.plain.our.par.UHolds D.out (msg m) := by
  rw [leftKey_spec hf]
  refine row_uholds law _ D hs hD h W _ m D1 D2 ?_
  have hini := out_ini _ D hs hD h
  have hvals : D.out.vals = D.v := plain_vals ρ _ D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _
  obtain ⟨vs, e, F, G, used, _, sd, hst⟩ := h
  rw [g1, g2, g3, g4, g5]
  rw [keyFlat_read ρ s _ _ _ _ _ om' _ (by simp; omega) (by simp; omega)
    (ldPartIni s.k s.deg (pDummy K (s.lt + 1)) D.out.pt)
    (fun a => by
      rw [extract_getD _ _ _ _ (by have := a.2; omega)]
      exact (hini (s.jAt a)).trans (by simp [ScdSize.jAt]))
    (fun a => by
      rw [extract_getD _ _ _ _ (by have := a.2; omega)]
      exact hini (s.gAt a))
    (fun a => by
      rw [extract_getD _ _ _ _ (by have := a.2; omega)]
      exact hini (s.iAt a))]
  show scdS s (T.ri D.st) (T.rg D.st) (T.om D.st) _ D.out.vals = _
  rw [hvals, hv]
  congr 1
  · funext a
    rw [hri, extract_getD _ _ _ _ (by have := a.2; omega), Nat.zero_add]
  · funext a
    rw [hrg, extract_getD _ _ _ _ (by have := a.2; omega)]
  · funext b
    exact hom b
  · funext a
    have hlt := OnBytes.Tie.Pv.Att.scdNum_lt s a
    rw [(hst _ _ _ (sd.ends (scdNum s a) (by rw [← sd.lenV]; omega))).2.1]

end Typed

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.leftD_uholds
#print axioms VerifiableInference.Desc.First.Att.P.leftP_spec
#print axioms VerifiableInference.Desc.First.Att.P.leftKey_spec
#print axioms VerifiableInference.Desc.First.Att.P.LeftIs.forms
