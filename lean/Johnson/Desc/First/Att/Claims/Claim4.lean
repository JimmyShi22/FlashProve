-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Claim4.lean: kind K5, the claims are the written lists: the other
readers (shV, xl, readHead, readGroup, readMaximum, readDenominator, readIndexBit) and claim 4
(endValues, unitKFD, callKFD, claim4).

Main names:
  `scoreOf`, `scoreTOf`: the record of a softmax-table unit, and of its tables, as the kind's: the
    functions inside ptsOfOwn and tabsOld.
  `cutLast_old`, `headFeat_old`: the kind's two functions are those of OnBytes/Model/Tensors.lean,
    the refusal's name dropped.
  `gv_…`: wherever the kind's routine returns at K, at `inOld h`, it returns the written value and
    has gathered just the written list.
Used of OnBytes: plain records, pure functions and definitions alone; no routine in a context and no
theorem on a run: the records Attention.Heard, Score, ScoreTables, Sc3, PW, Joins, ACall, Shape,
ShD, Model.TenAt, Model.Call; the pure functions Model.cutLast, headFeat, tenCell, Attention.keyKFD,
padTerm, wall, sc3A, sc3B, Shape.shd, Call.tauAt; the written forms and lists Fo.shVF, overGF, xlF,
xlT, readHeadT, readGroupT, readMaximumF, readDenominatorF, readIndexBitF, endValuesT, unitKFDT,
callKFDV, callKFDT, claim4V, claim4T.
Not claimed: that a routine returns (where xl refuses, Fo.xlT is the empty form and nothing is
said); what a form is worth.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Claim3b

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (TablesP ScoreT Fun1 geoOf ptsOfOwn w1Of callOf tabOf keysOf tenOf sum3Of sumDOf)

variable {K : ℕ}

/-! ### rules on mapped lists -/

theorem GV.forMmap {α β : Type} (φ : α → β) (f : β → P.Runs.W PUnit) (L : α → List Aff)
    (hf : ∀ a, GV K (f (φ a)) () (L a)) : ∀ xs : List α, GV K ((xs.map φ).forM f) () (xs.flatMap L)
  | [] => by simpa using GV.pure (K := K) ()
  | a :: xs => by
    simp only [List.map_cons, List.flatMap_cons]
    exact GV.bind (hf a) (GV.forMmap φ f L hf xs)

/-- The one piece of the kind made of that of OnBytes/Model. -/
def w1 (w : PW) : P.W1 := { lam := w.lam, a := w.a, wp := w.wp }

theorem w1Of_zip (pw : Array PW) :
    (w1Of pw).toList.zipIdx = pw.toList.zipIdx.map fun x => (w1 x.1, x.2) := by
  unfold w1Of
  rw [Array.toList_map, List.zipIdx_map]
  rfl

/-! ### the readers -/

theorem gv_shV (h : Attention.Heard) (t off nl J lam j : ℕ) :
    GV K (P.Runs.shV (inOld h) t off nl J lam j) (Fo.shVF h K t off nl J lam j) [] := by
  unfold P.Runs.shV Fo.shVF
  exact gv_weighted _ _ _ _ fun _ => gv_u3at (inOld h) t _

theorem gv_overG (h : Attention.Heard) (zg : Array E) (f : ℕ → P.Runs.W Aff) (fv : ℕ → Aff)
    (hf : ∀ i, GV K (f i) (fv i) []) : GV K (P.Runs.overG (inOld h) zg f) (Fo.overGF h zg fv) [] := by
  unfold P.Runs.overG Fo.overGF
  exact gv_weighted _ _ _ _ hf

theorem gv_readMaximum (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    GV K (P.Runs.readMaximum (inOld h) t zg lam a) (Fo.readMaximumF h K t zg lam a) [] := by
  unfold P.Runs.readMaximum Fo.readMaximumF
  exact gv_overG h _ _ _ fun _ => gv_shV h t _ _ _ _ _

theorem gv_readDenominator (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    GV K (P.Runs.readDenominator (inOld h) t zg lam a) (Fo.readDenominatorF h K t zg lam a) [] := by
  unfold P.Runs.readDenominator Fo.readDenominatorF
  exact gv_overG h _ _ _ fun _ => gv_shV h t _ _ _ _ _

theorem gv_readIndexBit (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a b : ℕ) :
    GV K (P.Runs.readIndexBit (inOld h) t zg lam a b) (Fo.readIndexBitF h K t zg lam a b) [] := by
  unfold P.Runs.readIndexBit Fo.readIndexBitF
  exact gv_overG h _ _ _ fun _ => gv_shV h t _ _ _ _ _

/-- The kind's cut of a point is that of OnBytes/Model, its refusal's name dropped. -/
theorem cutLast_old (z : Array E) (k : ℕ) : P.cutLast z k = (Model.cutLast z k).toOption := by
  unfold P.cutLast Model.cutLast
  split <;> rfl

/-- The kind's first feature of a head is that of OnBytes/Model, its refusal's name dropped. -/
theorem headFeat_old (X : TenAt) (hd dh : ℕ) :
    P.headFeat (tenOf X) hd dh = (Model.headFeat X hd dh).toOption := by
  unfold P.headFeat Model.headFeat tenOf
  dsimp only
  split <;> rfl

theorem gv_xl (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    GV K (P.Runs.xl (inOld h) t (tenOf X) lam hd zc) (Fo.xlT h K t X lam hd zc) [] := by
  unfold P.Runs.xl Fo.xlT Fo.xlF
  dsimp only
  rw [cutLast_old, headFeat_old]
  show GV K (match (Model.cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls).toOption with
    | some cut => _ | _ => _) _ _
  cases Model.cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls with
  | error e => exact gv_refuse _ _ _
  | ok cut =>
    show GV K (match (Model.headFeat X hd h.S.dh).toOption with | some j0 => _ | _ => _) _ _
    cases Model.headFeat X hd h.S.dh with
    | error e => exact gv_refuse _ _ _
    | ok j0 =>
      exact gv_weighted _ _ _ _ fun _ => gv_weighted _ _ _ _ fun _ => gv_u3at (inOld h) t _

theorem gv_readHead (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    GV K (P.Runs.readHead (inOld h) t (tenOf X) zg zc lam a) (Fo.readHeadT h K t X zg zc lam a) [] := by
  unfold P.Runs.readHead Fo.readHeadT
  exact gv_overG h _ _ _ fun _ => gv_xl h t X lam _ zc

theorem gv_readGroup (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    GV K (P.Runs.readGroup (inOld h) t (tenOf X) zg zc lam) (Fo.readGroupT h K t X zg zc lam) [] := by
  unfold P.Runs.readGroup Fo.readGroupT
  exact gv_overG h _ _ _ fun _ => gv_xl h t X lam _ zc

/-! ### claim 4 -/

/-- The record of OnBytes/Model of a softmax-table unit as the kind's: the function inside ptsOfOwn. -/
def scoreOf (k : Score) : P.ScoreP :=
  { call := k.call, claim := k.claim, below := k.seg == Seg.fm, pw := w1Of k.pw, zg := k.zg, zs := k.zs, zi := k.zi, zj := k.zj, wI := k.wI, s0 := k.s0, sc := sum3Of k.sc }

/-- The record of OnBytes/Model of a unit's tables as the kind's: the function inside tabsOld. -/
def scoreTOf (s : ScoreTables) : ScoreT := { tM := s.tM, tQ := s.tQ, tK := s.tK }

theorem scores_inOld (h : Attention.Heard) : (inOld h).p.scores = h.scores.map scoreOf := rfl

theorem scoreT_inOld (h : Attention.Heard) : (inOld h).t.score = h.t.score.map scoreTOf := rfl

theorem scores_zip (h : Attention.Heard) :
    (inOld h).p.scores.toList.zipIdx = h.scores.toList.zipIdx.map fun x => (scoreOf x.1, x.2) := by
  rw [scores_inOld, Array.toList_map, List.zipIdx_map]
  rfl

theorem gv_endValues (h : Attention.Heard) (k : Score) (tb : ScoreTables) (rc : Array E) (b : ℕ)
    (w : PW) : GV K (P.Runs.endValues (inOld h) (scoreOf k) (scoreTOf tb) rc b (w1 w)) ()
      (Fo.endValuesT h K k tb rc b w) := by
  unfold P.Runs.endValues Fo.endValuesT
  exact GV.bind0 (gv_readHead h _ h.S.atQ _ _ _ _) (GV.bind (GV.lin _)
    (GV.bind0 (gv_readGroup h _ h.S.atK _ _ _) (GV.lin _)))

theorem gv_unitKFD (h : Attention.Heard) (i : ℕ) (k : Score) :
    GV K (P.Runs.unitKFD (inOld h) i (scoreOf k)) () (Fo.unitKFDT h K i k) := by
  unfold P.Runs.unitKFD Fo.unitKFDT
  dsimp only
  rw [scoreT_inOld, planes_inOld, Array.getElem?_map, Array.getElem?_map]
  show GV K (P.Runs.W.need (Option.map scoreTOf h.t.score[i]?) >>= fun tb =>
    P.Runs.W.need (Option.map remOf h.planes[k.claim]?) >>= _) _ _
  cases h.t.score[i]? with
  | none => exact GV.never_bind (fun _ => rfl) _ _ _
  | some tb =>
    refine GV.bind0 (GV.needSome _) ?_
    cases h.planes[k.claim]? with
    | none => exact GV.never_bind (fun _ => rfl) _ _ _
    | some pc =>
      refine GV.bind0 (GV.needSome _) (GV.bind (gv_linPlanes h pc) ?_)
      refine GV.bind0 (gv_lessPieces (Aff.slot (k.s0 + 5)) k.pw _
        (fun w => Fo.readMaximumF h K tb.tM k.zg w.lam w.a)
        fun w => gv_readMaximum h tb.tM k.zg w.lam w.a) ?_
      refine GV.bind (GV.lin _) (GV.bind (GV.lin _) ?_)
      show GV K ((w1Of k.pw).toList.zipIdx.forM _) _ _
      rw [w1Of_zip]
      exact GV.forMmap (fun x : PW × ℕ => (w1 x.1, x.2))
        (fun x => P.Runs.endValues (inOld h) (scoreOf k) (scoreTOf tb)
          (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) x.2 x.1)
        (fun x => Fo.endValuesT h K k tb
          (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) x.2 x.1)
        (fun x => gv_endValues h k tb _ x.2 x.1) _

theorem keyKFD_scoreOf (S : Shape) (sh : ℕ) (k : Score) :
    P.Runs.keyKFD ((geoOf S).gapC sh) ((geoOf S).gapOm sh) (scoreOf k) = keyKFD (S.shd sh) k := by
  unfold P.Runs.keyKFD keyKFD scoreOf
  dsimp only
  rw [sumW_w1Of]
  rfl

theorem wall_callOf (c : ACall) (zk : Array E) : P.Runs.wall (callOf c) zk = wall c zk := by
  unfold P.Runs.wall wall callOf
  dsimp only
  rw [← Array.foldl_toList, List.foldl_map]
  rfl

theorem padTerm_callOf (c : ACall) (zk : Array E) : P.Runs.padTerm (callOf c) zk = padTerm c zk := by
  unfold P.Runs.padTerm padTerm
  rw [wall_callOf]
  rfl

theorem gv_callKFD (h : Attention.Heard) (q : ℕ) (c : ACall) :
    GV K (P.Runs.callKFD (inOld h) q (callOf c)) (Fo.callKFDV h q c) (Fo.callKFDT h K q) := by
  unfold P.Runs.callKFD Fo.callKFDV Fo.callKFDT
  rw [scores_zip, List.foldlM_map, padTerm_callOf]
  exact GV.foldlM _
    (fun (v : Aff) (x : Score × ℕ) => if x.1.call == q then v + keyKFD (h.S.shd c.sh) x.1 else v)
    (fun (x : Score × ℕ) => if x.1.call == q then Fo.unitKFDT h K x.2 x.1 ++ [] else [])
    (fun v x => GV.ite (GV.bind (gv_unitKFD h x.2 x.1)
      ((GV.pure _).cast (congrArg (v + ·) (keyKFD_scoreOf h.S c.sh x.1)) rfl)) (GV.pure _)) _ _

/-- **Claim 4 of the kind's own text: the written joins and the written list.** -/
theorem gv_claim4 (h : Attention.Heard) (j : Joins) :
    GV K (P.Runs.claim4 (inOld h) (jP j)) (jP (Fo.claim4V h j)) (Fo.claim4T h K) := by
  unfold P.Runs.claim4 Fo.claim4V Fo.claim4T
  show GV K ((geoOf h.S).calls.toList.zipIdx.foldlM _ _) _ _
  rw [calls_zip, List.foldlM_map]
  exact GV.foldlMmap jP _
    (fun (j : Joins) (x : ACall × ℕ) =>
      if x.1.kind == .kfd then j.set x.2 (Fo.callKFDV h x.2 x.1) else j)
    (fun (x : ACall × ℕ) => if x.1.kind == .kfd then Fo.callKFDT h K x.2 ++ [] else [])
    (fun j x => GV.cast (GV.ite' (q := (x.1.kind == Table.kfd) = true)
      (by rw [← tab_eq x.1.kind Table.kfd]; exact Iff.rfl)
      (GV.bind (gv_callKFD h x.2 x.1) (GV.pure ((jP j).set x.2 (Fo.callKFDV h x.2 x.1))))
      (GV.pure (jP j))) (apply_ite jP _ _ _).symm rfl) _ _

end K5Law
