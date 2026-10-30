-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SameClaims.lean: kind K5: whether the claims return depends on public
numbers and lengths alone: claims 3 to 8.

Main names:
  `rs_claim3` … `rs_claim8`: at two records that agree in what is public (`Same`,
    Johnson/Desc/First/Att/Claims/Same.lean) the routine returns at both or at neither; claims 3, 4
    and 5 then hand on records of key forms with one array of counts (`JR`).
Nothing of OnBytes is used but the types Aff and E.
Not claimed: that a routine returns anywhere; what it returns.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Same

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP MaxP Pts SumP TablesP ScoreT Geo Ten CallG)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)

variable {K : ℕ} {i i' : In}

/-- Two records of key forms with one array of counts. -/
def JR (j j' : JoinsP) : Prop := j.joined = j'.joined

theorem JR.set {j j' : JoinsP} (h : JR j j') (q : ℕ) (v v' : Aff) : JR (j.set q v) (j'.set q v') := by
  unfold JR JoinsP.set
  dsimp only
  rw [h]

theorem optRel_refl {α : Type} (x : Option α) : OptRel Eq x x := by
  cases x
  · trivial
  · exact rfl

/-! ### claim 3 -/

theorem rs_linPlanes (H : Same i i') {pc pc' : RemP} (h : SameRem pc pc') :
    RS K Any (P.Runs.linPlanes i pc) (P.Runs.linPlanes i' pc') := by
  unfold P.Runs.linPlanes
  rw [h.np]
  refine RS.forM1 (fun x => RS.bind (R := Any) (rs_lessPieces _ _ h.pw _ _ fun w w' hl ha => ?_)
    fun _ _ _ => RS.lin _ _) _
  rw [hl, ha, H.t.tA, h.isD]
  exact rs_plane H _ _ _ _ _ _ h.z _

theorem rs_callKR (H : Same i i') (q : ℕ) : RS K Any (P.Runs.callKR i q) (P.Runs.callKR i' q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  refine RS.foldlM₂ (R := Any) (P := SameRem) (fun _ _ pc pc' _ h => ?_) H.p.planes trivial
  rw [h.call]
  exact RS.ite Iff.rfl (RS.bind (rs_linPlanes H h) fun _ _ _ => RS.pure trivial) (RS.pure trivial)

theorem rs_claim3 (H : Same i i') {j j' : JoinsP} (hj : JR j j') :
    RS K JR (P.Runs.claim3 i j) (P.Runs.claim3 i' j') := by
  unfold P.Runs.claim3
  rw [H.g]
  refine RS.foldlM1 (R := JR) (fun j j' x hj => ?_) _ hj
  exact RS.ite Iff.rfl (RS.bind (rs_callKR H x.2) fun _ _ _ => RS.pure (hj.set _ _ _)) (RS.pure hj)

/-! ### claim 4 -/

theorem rs_endValues (H : Same i i') (k k' : ScoreP) (tb : ScoreT) (rc rc' : Array E)
    (hrc : rc.size = rc'.size) (b b' : ℕ) {w w' : W1} (hl : w.lam = w'.lam) (ha : w.a = w'.a) :
    RS K Any (P.Runs.endValues i k tb rc b w) (P.Runs.endValues i' k' tb rc' b' w') := by
  unfold P.Runs.endValues
  rw [hl, ha, H.g]
  exact RS.bind (rs_readHead H _ _ _ _ _ _ hrc _ _) fun _ _ _ => RS.bind (RS.lin _ _) fun _ _ _ =>
    RS.bind (rs_readGroup H _ _ _ _ _ _ hrc _) fun _ _ _ => RS.lin _ _

theorem rs_unitKFD (H : Same i i') (n : ℕ) {k k' : ScoreP} (hk : SameScore k k') :
    RS K Any (P.Runs.unitKFD i n k) (P.Runs.unitKFD i' n k') := by
  unfold P.Runs.unitKFD
  dsimp only
  rw [H.t.score, H.g, hk.claim]
  refine RS.bind (RS.need (optRel_refl _)) fun tb tb' e => ?_
  subst e
  refine RS.bind (R := SameRem) (RS.need ?_) fun pc pc' hpc => ?_
  · rw [← Array.getElem?_toList, ← Array.getElem?_toList]
    exact forall₂_getElem? H.p.planes _
  refine RS.bind (rs_linPlanes H hpc) fun _ _ _ => ?_
  refine RS.bind (R := Any) (rs_lessPieces _ _ hk.pw _ _ fun w w' hl ha => ?_) fun _ _ _ => ?_
  · rw [hl, ha]
    exact rs_readMaximum H _ _ _ _ _
  refine RS.bind (RS.lin _ _) fun _ _ _ => RS.bind (RS.lin _ _) fun _ _ _ => ?_
  exact RS.forM₂ (fun x x' h => rs_endValues H _ _ _ _ _
    (by rw [Array.size_extract, Array.size_extract, hk.r]) _ _ h.1.1 h.1.2) (forall₂_zipIdx hk.pw 0)

theorem rs_callKFD (H : Same i i') (q : ℕ) (c : CallG) :
    RS K Any (P.Runs.callKFD i q c) (P.Runs.callKFD i' q c) := by
  unfold P.Runs.callKFD
  refine RS.foldlM₂ (R := Any) (fun _ _ x x' _ h => ?_) (forall₂_zipIdx H.p.scores 0) trivial
  rw [h.1.call, h.2]
  exact RS.ite Iff.rfl (RS.bind (rs_unitKFD H _ h.1) fun _ _ _ => RS.pure trivial) (RS.pure trivial)

theorem rs_claim4 (H : Same i i') {j j' : JoinsP} (hj : JR j j') :
    RS K JR (P.Runs.claim4 i j) (P.Runs.claim4 i' j') := by
  unfold P.Runs.claim4
  rw [H.g]
  refine RS.foldlM1 (R := JR) (fun j j' x hj => ?_) _ hj
  exact RS.ite Iff.rfl (RS.bind (rs_callKFD H x.2 x.1) fun _ _ _ => RS.pure (hj.set _ _ _))
    (RS.pure hj)

/-! ### claim 5 -/

theorem foldl_rel {α σ σ' : Type} {R : σ → σ' → Prop} {f : σ → α → σ} {f' : σ' → α → σ'}
    (hf : ∀ s s' a, R s s' → R (f s a) (f' s' a)) :
    ∀ (xs : List α) {s : σ} {s' : σ'}, R s s' → R (xs.foldl f s) (xs.foldl f' s')
  | [], _, _, h => h
  | a :: xs, _, _, h => foldl_rel hf xs (hf _ _ a h)

theorem joinR16_JR (S : Geo) (d d' : DivP) {j j' : JoinsP} (hj : JR j j') :
    JR (P.Runs.joinR16 S d j) (P.Runs.joinR16 S d' j') := by
  unfold P.Runs.joinR16
  dsimp only
  refine foldl_rel (fun s s' x h => ?_) _ hj
  split
  · exact h.set _ _ _
  · exact h

theorem rs_endValuesE (H : Same i i') (b : ℕ) {w w' : W1} (hl : w.lam = w'.lam) (ha : w.a = w'.a) :
    RS K Any (P.Runs.endValuesE i b w) (P.Runs.endValuesE i' b w') := by
  unfold P.Runs.endValuesE
  dsimp only
  rw [hl, ha, H.g, H.t.hE, H.t.qO]
  exact RS.bind (rs_readDenominator H _ _ _ _ _) fun _ _ _ => RS.bind (RS.lin _ _) fun _ _ _ =>
    RS.bind (rs_readHead H _ _ _ _ _ _ H.p.d.zcW _ _) fun _ _ _ => RS.lin _ _

theorem rs_claim5 (H : Same i i') {j j' : JoinsP} (hj : JR j j') :
    RS K JR (P.Runs.claim5 i j) (P.Runs.claim5 i' j') := by
  unfold P.Runs.claim5
  dsimp only
  rw [H.g, H.t.hW, H.t.tO, H.t.hX, H.p.d.qWH]
  refine RS.bind (R := Any) (rs_lessPieces _ _ H.p.d.pwW _ _ fun w w' hl ha => ?_) fun _ _ _ => ?_
  · rw [hl, ha]; exact rs_readDenominator H _ _ _ _ _
  refine RS.bind (R := Any) (rs_lessPieces _ _ H.p.d.pwW _ _ fun w w' hl ha => ?_) fun _ _ _ => ?_
  · rw [hl, ha]; exact rs_readHead H _ _ _ _ _ _ H.p.d.zcW _ _
  refine RS.bind (R := Any) (rs_lessPieces _ _ H.p.d.pwW _ _ fun w w' hl ha => ?_) fun _ _ _ => ?_
  · rw [hl, ha]; exact rs_readHead H _ _ _ _ _ _ H.p.d.zcW _ _
  refine RS.bind (R := Any) (rs_lessPieces _ _ H.p.d.pwH _ _ fun w w' hl ha => ?_) fun _ _ _ => ?_
  · rw [hl, ha]; exact rs_readHead H _ _ _ _ _ _ H.p.d.zcH _ _
  refine RS.bind (R := Any) (rs_lessPieces _ _ H.p.d.pwH _ _ fun w w' hl ha => ?_) fun _ _ _ => ?_
  · rw [hl, ha]; exact rs_readHead H _ _ _ _ _ _ H.p.d.zcH _ _
  refine RS.bind (RS.lin _ _) fun _ _ _ => RS.bind (RS.lin _ _) fun _ _ _ =>
    RS.bind (RS.lin _ _) fun _ _ _ => ?_
  refine RS.bind (R := Any) (RS.forIn1 (fun k => ?_) _) fun _ _ _ => ?_
  · refine RS.bind (R := Any) (rs_lessPieces _ _ H.p.d.pwX _ _ fun w w' hl ha => ?_)
      fun _ _ _ => RS.linYield _ _
    rw [hl, ha]; exact rs_readIndexBit H _ _ _ _ _ _
  refine RS.bind (RS.lin _ _) fun _ _ _ => RS.bind (RS.lin _ _) fun _ _ _ =>
    RS.bind (RS.lin _ _) fun _ _ _ => ?_
  refine RS.bind (R := Any) (RS.forIn1 (fun b => ?_) _) fun _ _ _ => ?_
  · exact RS.bind (rs_endValuesE H b (sameW_getD H.p.d.pwW b).1 (sameW_getD H.p.d.pwW b).2)
      fun _ _ _ => RS.yield
  exact RS.pure ((joinR16_JR _ _ _ hj).set _ _ _)

/-! ### claims 6, 7, 8 -/

theorem rs_valueProduct (H : Same i i') (sc sc' : SumP) (tS : ℕ) (pt pt' : Array E)
    (hpt : pt.size = pt'.size) (isD : Bool) (tV : ℕ) :
    RS K Any (P.Runs.valueProduct i sc tS pt isD tV) (P.Runs.valueProduct i' sc' tS pt' isD tV) := by
  unfold P.Runs.valueProduct
  rw [H.g]
  refine RS.bind (RS.lin _ _) fun _ _ _ => RS.bind (R := Any) (RS.forIn1 (fun b => ?_) _)
    fun _ _ _ => RS.pure trivial
  dsimp only
  rw [(sameW_getD H.p.d.pwW b).1, (sameW_getD H.p.d.pwW b).2]
  refine RS.bind (rs_plane H _ _ _ _ _ _ hpt _) fun _ _ _ =>
    RS.bind (rs_plane H _ _ _ _ _ _ hpt _) fun _ _ _ => RS.bind (RS.lin _ _) fun _ _ _ =>
    RS.bind (rs_readGroup H _ _ _ _ _ _ H.p.d.zcW _) fun _ _ _ => RS.linYield _ _

theorem rs_claim6 (H : Same i i') : RS K Any (P.Runs.claim6 i) (P.Runs.claim6 i') := by
  unfold P.Runs.claim6
  dsimp only
  rw [H.t.tVM, H.t.qVM, H.t.tVD, H.t.qVD]
  exact RS.bind (RS.lin _ _) fun _ _ _ => RS.bind (rs_valueProduct H _ _ _ _ _ H.t.ptM _ _)
    fun _ _ _ => rs_valueProduct H _ _ _ _ _ H.t.ptD _ _

theorem rc_size (H : Same i i') : (i.p.x.rc i'.g).size = (i'.p.x.rc i'.g).size := by
  unfold P.MaxP.rc
  rw [Array.size_extract, Array.size_extract, H.p.rF]

theorem rs_claim7 (H : Same i i') : RS K Any (P.Runs.claim7 i) (P.Runs.claim7 i') := by
  unfold P.Runs.claim7
  dsimp only
  rw [H.g, H.t.hT, H.t.qF, H.t.qKx, H.t.hPi]
  refine RS.bind (R := Any) (RS.forIn1 (fun b => ?_) _) fun _ _ _ => ?_
  · exact RS.bind (rs_readMaximum H _ _ _ _ _) fun _ _ _ => RS.linYield _ _
  refine RS.bind (RS.lin _ _) fun _ _ _ => ?_
  refine RS.bind (R := Any) (RS.forIn1 (fun b => ?_) _) fun _ _ _ => ?_
  · exact RS.bind (rs_readHead H _ _ _ _ _ _ (rc_size H) _ _) fun _ _ _ => RS.linYield _ _
  refine RS.bind (RS.lin _ _) fun _ _ _ => ?_
  refine RS.bind (R := Any) (RS.forIn1 (fun lam => ?_) _) fun _ _ _ => ?_
  · exact RS.bind (rs_readGroup H _ _ _ _ _ _ (rc_size H) _) fun _ _ _ => RS.linYield _ _
  refine RS.bind (R := Any) (RS.forIn1 (fun b => ?_) _) fun _ _ _ => RS.pure trivial
  refine RS.bind (R := Any) (RS.forIn1 (fun k => ?_) _) fun _ _ _ =>
    RS.bind (R := Any) (RS.pure trivial) fun _ _ _ => RS.yield
  exact RS.bind (rs_readIndexBit H _ _ _ _ _ _) fun _ _ _ => RS.linYield _ _

theorem rs_claim8 (H : Same i i') : RS K Any (P.Runs.claim8 i) (P.Runs.claim8 i') := by
  unfold P.Runs.claim8
  dsimp only
  rw [H.g, H.t.hR2]
  refine RS.bind (RS.lin _ _) fun _ _ _ => RS.bind (R := Any) (RS.forIn1 (fun b => ?_) _)
    fun _ _ _ => RS.pure trivial
  refine RS.bind (RS.lin _ _) fun _ _ _ => ?_
  refine RS.bind (R := Any) ?_ fun _ _ _ => RS.linYield _ _
  refine RS.foldlM1 (R := Any) (fun _ _ k _ => ?_) _ trivial
  exact RS.bind (rs_readIndexBit H _ _ _ _ _ _) fun _ _ _ => RS.pure trivial

end K5Law
