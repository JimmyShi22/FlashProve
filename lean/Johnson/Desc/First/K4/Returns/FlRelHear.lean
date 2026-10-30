-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRelHear.lean: TWO RUNS OF ONE TEXT (FlRel,
Johnson/Desc/First/K4/Returns/FlRel.lean): THE FOUR PARTS OF K4's HEARING
(OnBytes/Desc/First/K4/Hear.lean, at the engine of plain functions). General laws: nothing is
evaluated.

  FlRel.none, enPoint, getAny, get, getRel   the engine's own spellings.
  normsStart_rel, NormsAlike, **hearNorms_rel**   the norms: at two lookup's records of one shape.
  **hearTerms_rel**   the second token sumcheck.
  NormsAlike.tT, parts_fold_rel, **joinStart_rel**   the start form of the batched sumcheck.
  plainRounds_rel, StackAlike, **hearStack_rel**   the batched sumcheck and its end.
  **hearGated_rel**   the gated products.
Each: where both runs return, what they leave has one shape (normsSh, stackSh, levelSh:
Johnson/Desc/First/Shape/Own.lean), and so have the ledgers and the tapes behind.

Limits. The weak form of the frame. joinStart_rel and hearStack_rel ask EnvSame of the two
environments because joinPart_rel (JoinShape.lean) does; of its fields they read keys alone
themselves: see that file's Limits on sc and g. "attribute [local irreducible] OnBytes.Flat.OptRel"
stands in the middle of the file: it bears on how the later proofs elaborate, on no statement.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelParts
import Johnson.Desc.First.K4.Returns.JoinShape
import Johnson.Desc.First.K4.Returns.PanelsShape
import Johnson.Desc.First.K4.Returns.Points
import Johnson.Desc.First.K4.Returns.JoinSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Flat (All2 OptRel mapM_opt_rel)
open VerifiableInference.Desc.First.Shape

/-! ## The engine's own spellings -/

theorem FlRel.none {α β : Type} (R : α → β → Prop) :
    FlRel R (fun _ _ => Option.none : Fl α) (fun _ _ => Option.none : Fl β) := by
  intro F F' t t' a G u a' G' u' _ _ h1 _
  cases h1

theorem FlRel.enPoint (r : RoundName) (n : Nat) :
    FlRel SameSize (engFl.point r n) (engFl.point r n) := by
  show FlRel SameSize (if r == .batSigma then fun _ _ => Option.none else Fl.point r n)
    (if r == .batSigma then fun _ _ => Option.none else Fl.point r n)
  exact FlRel.ite (FlRel.none _) (FlRel.point r n)

/-- A value that may be missing, of which nothing is said. -/
theorem FlRel.getAny {α β : Type} (x : Option α) (x' : Option β) :
    FlRel (fun _ _ => True) (engFl.get x) (engFl.get x') :=
  FlRel.need fun _ _ _ _ => trivial

theorem FlRel.get {α β : Type} {R : α → β → Prop} {x : Option α} {x' : Option β}
    (h : ∀ a b, x = some a → x' = some b → R a b) : FlRel R (engFl.get x) (engFl.get x') :=
  FlRel.need h

/-- From two values in OptRel. -/
theorem FlRel.getRel {α : Type} {R : α → α → Prop} {x x' : Option α} (h : OptRel R x x') :
    FlRel R (engFl.get x) (engFl.get x') :=
  FlRel.need fun a b ha hb => by
    rw [ha, hb] at h
    exact h

/-! ## The norms -/

theorem normsStart_rel (y : Lay) (sW : Nat) (gp gp' rhoI rhoI' PV PV' : Array E) :
    SameSh (normsStart y sW gp rhoI PV).1 (normsStart y sW gp' rhoI' PV').1 := by
  unfold normsStart
  dsimp only
  refine foldl_rel _ _ _ (SameSh.refl _) fun i a b hab => ?_
  exact foldl_rel _ _ _ hab fun s c d hcd => SameSh.addMul hcd (SameSh.refl _) _ _

/-- Two records of the norms and the token sumchecks of one shape. -/
def NormsAlike (H H' : Heard) : Prop := normsSh H = normsSh H'

theorem hearNorms_rel (P : Pub) (g : Nat) {fo fo' : Forest.Heard}
    (hfo : heardAll fo = heardAll fo') :
    FlRel NormsAlike (hearNorms engFl P g fo) (hearNorms engFl P g fo') := by
  unfold hearNorms
  dsimp only
  refine FlRel.bind (FlRel.enPoint _ _) fun PV PV' hPV => ?_
  -- what stands behind the two points of the first group, at any two pairs of one size each
  have tail : ∀ (ZE ZE' tkh tkh' : Array E), SameSize ZE ZE' → SameSize tkh tkh' →
      FlRel NormsAlike
        (do
          engFl.mustAs "forest-depth-G" (decide (P.y.h.la ≤ fo.shape.dT))
          let Z ← engFl.get (lastOf fo.zx P.y.h.la).toOption
          let ends ← engFl.get (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption)
          engFl.check (ofGroup g "internal-g-merged-point") (ends.all (· == Z))
          let ztF ← engFl.get (lastOf fo.zx P.y.h.lt).toOption
          let sW ← engFl.claimsIn (ledNS P.y.h.xl * P.y.NI)
          let gp ← engFl.batch (ledNS P.y.h.xl)
          let rhoI ← engFl.point .join P.rd.lNI
          let wpl ← engFl.levelIn P.rd.muV (normsStart P.y sW gp rhoI PV).2
            (normsStart P.y sW gp rhoI PV).1 (orderDefault P.rd.muV)
          let sPv ← engFl.claimsIn (ledNP P.y.h.xl * P.y.NI)
          let omV ← engFl.batch (ledNP P.y.h.xl * P.y.NI)
          let tV ← engFl.tscIn PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2
          pure ({ fo := fo, PV := PV, ZE := ZE, tkh := tkh, ztF := ztF, sW := sW, gp := gp,
                  wpl := wpl, sPv := sPv, omV := omV, tV := tV } : Heard))
        (do
          engFl.mustAs "forest-depth-G" (decide (P.y.h.la ≤ fo'.shape.dT))
          let Z ← engFl.get (lastOf fo'.zx P.y.h.la).toOption
          let ends ← engFl.get (fo'.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption)
          engFl.check (ofGroup g "internal-g-merged-point") (ends.all (· == Z))
          let ztF ← engFl.get (lastOf fo'.zx P.y.h.lt).toOption
          let sW ← engFl.claimsIn (ledNS P.y.h.xl * P.y.NI)
          let gp ← engFl.batch (ledNS P.y.h.xl)
          let rhoI ← engFl.point .join P.rd.lNI
          let wpl ← engFl.levelIn P.rd.muV (normsStart P.y sW gp rhoI PV').2
            (normsStart P.y sW gp rhoI PV').1 (orderDefault P.rd.muV)
          let sPv ← engFl.claimsIn (ledNP P.y.h.xl * P.y.NI)
          let omV ← engFl.batch (ledNP P.y.h.xl * P.y.NI)
          let tV ← engFl.tscIn PV' P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2
          pure ({ fo := fo', PV := PV', ZE := ZE', tkh := tkh', ztF := ztF, sW := sW, gp := gp,
                  wpl := wpl, sPv := sPv, omV := omV, tV := tV } : Heard)) := by
    intro ZE ZE' tkh tkh' hZE htkh
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (FlRel.getAny _ _) fun Z Z' _ => ?_
    refine FlRel.bind (FlRel.getAny _ _) fun ends ends' _ => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := SameSize) (FlRel.get fun a b ha hb => by
      show a.size = b.size
      rw [lastOf_size ha, lastOf_size hb]) fun ztF ztF' hzt => ?_
    refine FlRel.bind (FlRel.claimsIn _) fun sW sW' hsW => ?_
    subst hsW
    refine FlRel.bind (FlRel.batch _) fun gp gp' hgp => ?_
    refine FlRel.bind (FlRel.enPoint _ _) fun rhoI rhoI' _ => ?_
    refine FlRel.bind (FlRel.levelIn _ _ _ (normsStart_rel P.y sW gp gp' rhoI rhoI' PV PV') _)
      fun wpl wpl' hw => ?_
    refine FlRel.bind (FlRel.claimsIn _) fun sPv sPv' hsP => ?_
    subst hsP
    refine FlRel.bind (FlRel.batch _) fun omV omV' hom => ?_
    refine FlRel.bind (FlRel.tscIn hPV _ _ _) fun tV tV' htV => ?_
    refine FlRel.pure ?_
    show NormsSh.mk (heardAll fo) PV.size ZE.size tkh.size ztF.size sW gp.size (levelSh wpl) sPv
        omV.size (tscSh tV) none (affSh {}) =
      NormsSh.mk (heardAll fo') PV'.size ZE'.size tkh'.size ztF'.size sW gp'.size (levelSh wpl')
        sPv omV'.size (tscSh tV') none (affSh {})
    rw [hfo, hPV, hZE, htkh, hzt, hgp, hw, hom, htV]
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true]
    refine FlRel.bind (FlRel.enPoint _ _) fun ZE ZE' hZE => ?_
    refine FlRel.bind (FlRel.enPoint _ _) fun tkh tkh' htkh => ?_
    exact tail ZE ZE' tkh tkh' hZE htkh
  · simp only [hg, if_false, Bool.false_eq_true, pure_bind]
    exact tail #[] #[] #[] #[] rfl rfl

/-! ## The second token sumcheck -/

theorem hearTerms_rel (P : Pub) {H H' : Heard} (h : NormsAlike H H') :
    FlRel NormsAlike (hearTerms engFl P H) (hearTerms engFl P H') := by
  unfold hearTerms
  have hz : SameSize H.ztF H'.ztF := congrArg NormsSh.ztF h
  refine FlRel.bind (FlRel.tscIn hz _ _ _) fun tT tT' ht => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  have hp : PscAlike tT.p tT'.p := congrArg TscSh.p ht
  refine FlRel.bind (FlRel.pscRow hp zeroE zeroE (SameSh.refl {})) fun x x' hx => ?_
  obtain ⟨row, p⟩ := x
  obtain ⟨row', p'⟩ := x'
  refine FlRel.pure ?_
  show NormsSh.mk (heardAll H.fo) H.PV.size H.ZE.size H.tkh.size H.ztF.size H.sW H.gp.size
      (levelSh H.wpl) H.sPv H.omV.size (tscSh H.tV)
      (some (TscSh.mk tT.sCl tT.sEnd tT.r.size (pscSh p) (affSh tT.rowU)))
      (affSh (row.scale (negE (invE tT.p.eps)))) =
    NormsSh.mk (heardAll H'.fo) H'.PV.size H'.ZE.size H'.tkh.size H'.ztF.size H'.sW H'.gp.size
      (levelSh H'.wpl) H'.sPv H'.omV.size (tscSh H'.tV)
      (some (TscSh.mk tT'.sCl tT'.sEnd tT'.r.size (pscSh p') (affSh tT'.rowU)))
      (affSh (row'.scale (negE (invE tT'.p.eps))))
  have a1 : heardAll H.fo = heardAll H'.fo := congrArg NormsSh.fo h
  have a2 : H.PV.size = H'.PV.size := congrArg NormsSh.PV h
  have a3 : H.ZE.size = H'.ZE.size := congrArg NormsSh.ZE h
  have a4 : H.tkh.size = H'.tkh.size := congrArg NormsSh.tkh h
  have a5 : H.sW = H'.sW := congrArg NormsSh.sW h
  have a6 : H.gp.size = H'.gp.size := congrArg NormsSh.gp h
  have a7 : levelSh H.wpl = levelSh H'.wpl := congrArg NormsSh.wpl h
  have a8 : H.sPv = H'.sPv := congrArg NormsSh.sPv h
  have a9 : H.omV.size = H'.omV.size := congrArg NormsSh.omV h
  have b1 : tscSh H.tV = tscSh H'.tV := congrArg NormsSh.tV h
  have c1 : tT.sCl = tT'.sCl := congrArg TscSh.sCl ht
  have c2 : tT.sEnd = tT'.sEnd := congrArg TscSh.sEnd ht
  have c3 : tT.r.size = tT'.r.size := congrArg TscSh.r ht
  have c4 : affSh tT.rowU = affSh tT'.rowU := congrArg TscSh.rowU ht
  have c5 : pscSh p = pscSh p' := hx.2
  have c6 : affSh (row.scale (negE (invE tT.p.eps))) = affSh (row'.scale (negE (invE tT'.p.eps))) :=
    SameSh.scale hx.1 _ _
  rw [a1, a2, a3, a4, hz, a5, a6, a7, a8, a9, b1, c1, c2, c3, c4, c5, c6]

/-! ## The start form of the batched sumcheck -/

theorem NormsAlike.tT {H H' : Heard} (h : NormsAlike H H') : OptRel TscAlike H.tT H'.tT := by
  have e : H.tT.map tscSh = H'.tT.map tscSh := congrArg NormsSh.tT h
  cases h1 : H.tT <;> cases h2 : H'.tT <;> rw [h1, h2] at e
  · trivial
  · cases e
  · cases e
  · exact Option.some.inj e

/-- The parts of the join under the calls' weights. -/
theorem parts_fold_rel (e e' : Array E) {l l' : List Aff} (h : All2 SameSh l l') :
    ∀ (k : Nat) (a a' : Aff), SameSh a a' →
      SameSh ((l.zipIdx k).foldl (fun (a : Aff) x => a.addMul x.1 (e.getD x.2 zeroE)) a)
        ((l'.zipIdx k).foldl (fun (a : Aff) x => a.addMul x.1 (e'.getD x.2 zeroE)) a') := by
  induction h with
  | nil => exact fun _ _ _ h => h
  | cons h0 _ ih =>
    intro k a a' ha
    rw [List.zipIdx_cons, List.zipIdx_cons, List.foldl_cons, List.foldl_cons]
    exact ih (k + 1) _ _ (SameSh.addMul ha h0 _ _)

/- From here on the relation on two values that may be missing is not unfolded: a unifier that
unfolds it evaluates the functions that it compares. -/
attribute [local irreducible] OnBytes.Flat.OptRel

theorem joinStart_rel {v v' : Env} (S : EnvSame v v') {H H' : Heard} (h : NormsAlike H H')
    (om om' : Array E) :
    FlRel SameSh (joinStart engFl v H om) (joinStart engFl v' H' om') := by
  unfold joinStart
  dsimp only
  have hw : v.weighedOf = v'.weighedOf := funext fun c => weighedOf_y S.keys.y c
  rw [S.keys.y, hw]
  refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
    rw [ha] at hb
    exact Option.some.inj hb) fun weighed weighed' hwe => ?_
  subst hwe
  refine FlRel.bind (FlRel.getRel (mapM_opt_rel (R := SameSh)
    (f := fun x : (CallD × Array Bool) × Nat =>
      v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2)
    (f' := fun x : (CallD × Array Bool) × Nat =>
      v'.joinPart H'.fo.alpha H'.fo.theta x.2 x.1.1 x.1.2)
    (fun x => joinPart_rel S H.fo.alpha H.fo.theta H'.fo.alpha H'.fo.theta x.2 x.1.1 x.1.2 x.1.2)
    _)) fun parts parts' hp => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.getAny _ _) fun laid laid' _ => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.getRel h.tT) fun tT tT' ht => ?_
  refine FlRel.pure ?_
  have c1 : tT.sCl = tT'.sCl := congrArg TscSh.sCl ht
  have c2 : SameSh H.fo.cEnd H'.fo.cEnd :=
    congrArg HeardAll.cEnd (congrArg NormsSh.fo h : heardAll H.fo = heardAll H'.fo)
  have c3 : SameSh H.KT H'.KT := congrArg NormsSh.KT h
  rw [c1]
  exact SameSh.addMul (SameSh.sub (SameSh.sub (SameSh.add
    (parts_fold_rel _ _ hp 0 _ _ (SameSh.refl _)) (SameSh.const _ _)) (SameSh.refl _)) c2) c3 _ _

/-! ## The batched sumcheck -/

theorem plainRounds_rel {st st' : Stack} (hl : st.lam = st'.lam) (hp : PscAlike st.p st'.p) :
    FlRel (fun s s' : Stack => SameSize s.rs s'.rs ∧ PscAlike s.p s'.p)
      (plainRounds engFl st) (plainRounds engFl st') := by
  unfold plainRounds
  rw [hl]
  refine FlRel.bind (S := fun x x' : Array E × Psc => SameSize x.1 x'.1 ∧ PscAlike x.2 x'.2)
    (FlRel.foldlM (fun z s s' hs => ?_) _ _ _ ⟨rfl, hp⟩) fun x x' hx => ?_
  · refine FlRel.bind (FlRel.roundIn .sum2 hs.2 z.1 z.1 z.2) fun y y' hy => ?_
    obtain ⟨r, q⟩ := y
    obtain ⟨r', q'⟩ := y'
    exact FlRel.pure ⟨by
      show (s.1.push r).size = (s'.1.push r').size
      rw [Array.size_push, Array.size_push, hs.1], hy⟩
  · obtain ⟨r, q⟩ := x
    obtain ⟨r', q'⟩ := x'
    exact FlRel.pure ⟨by
      show r.reverse.size = r'.reverse.size
      rw [Array.size_reverse, Array.size_reverse, hx.1], hx.2⟩

/-- Two records of the batched sumcheck of one shape. -/
def StackAlike (K K' : HeardStack) : Prop := stackSh K = stackSh K'

theorem hearStack_rel (P : Pub) {v v' : Env} (S : EnvSame v v') {H H' : Heard}
    (h : NormsAlike H H') (lamS NCLp : Nat) :
    FlRel StackAlike (hearStack engFl P v H lamS NCLp) (hearStack engFl P v' H' lamS NCLp) := by
  unfold hearStack
  dsimp only
  refine FlRel.bind (FlRel.batch 2) fun om om' _ => ?_
  refine FlRel.bind (FlRel.getRel h.tT) fun tT tT' ht => ?_
  refine FlRel.bind (FlRel.shownAll _ _ _) fun shownT shownT' _ => ?_
  refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
    rw [ha] at hb
    exact Option.some.inj hb) fun TS TS' hTS => ?_
  subst hTS
  refine FlRel.bind (FlRel.getRel (panels_shp (W := False)
    (p := { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y })
    (p₀ := { v := v', e := H'.fo.e, shownT := shownT', zt := H'.ztF, stubO := stubO P.y })
    S.keys (fun f => f.elim) TS)) fun pans pans' hpans => ?_
  obtain ⟨hbl, hplaces⟩ := placePanels_shp hpans.bl
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (joinStart_rel S h om om') fun C C' hC => ?_
  refine FlRel.bind (FlRel.pscBegin hC) fun p p' hp => ?_
  refine FlRel.bind (plainRounds_rel (st := { lam := lamS, p := p })
    (st' := { lam := lamS, p := p' }) rfl hp) fun st st' hst => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.pscEnds hst.2 2 _) fun x x' hx => ?_
  obtain ⟨sA0, q⟩ := x
  obtain ⟨sA0', q'⟩ := x'
  obtain ⟨rfl, hq⟩ : sA0 = sA0' ∧ PscAlike q q' := hx
  refine FlRel.bind (FlRel.shownAll _ _ _) fun sh1 sh1' _ => ?_
  refine FlRel.bind (FlRel.shownAll _ _ _) fun sh2 sh2' _ => ?_
  refine FlRel.bind (FlRel.shown _ _) fun a a' _ => ?_
  refine FlRel.bind (FlRel.shown _ _) fun b b' _ => ?_
  refine FlRel.bind (FlRel.getRel (stackEnd_shp (W := False) P.y lamS om sh1 sh2 om' sh1' sh2'
    a b a' b' hbl hst.1)) fun fin fin' hfin => ?_
  refine FlRel.bind (FlRel.pscRow hq _ _ (SameSh.refl {})) fun z z' hz => ?_
  obtain ⟨rowS, q2⟩ := z
  obtain ⟨rowS', q2'⟩ := z'
  refine FlRel.pure ?_
  show StackSh.mk st.rs.size sA0 (sA0 + 1) (sA0 + 1 + (1 + P.y.LamM))
      (sA0 + 1 + (1 + P.y.LamM) + 1) (affSh fin.Alin) (affSh fin.Blin) fin.wD (affSh rowS) =
    StackSh.mk st'.rs.size sA0 (sA0 + 1) (sA0 + 1 + (1 + P.y.LamM))
      (sA0 + 1 + (1 + P.y.LamM) + 1) (affSh fin'.Alin) (affSh fin'.Blin) fin'.wD (affSh rowS')
  rw [hst.1, hfin.1, hfin.2.1, hfin.2.2, hz.1]

/-! ## The gated products -/

theorem hearGated_rel (P : Pub) {H H' : Heard} (h : NormsAlike H H') {K K' : HeardStack}
    (hK : StackAlike K K') :
    FlRel (fun x x' : Level × Level => LevelAlike x.1 x'.1 ∧ LevelAlike x.2 x'.2)
      (hearGated engFl P H K) (hearGated engFl P H' K') := by
  unfold hearGated
  dsimp only
  have k1 : K.sH1 = K'.sH1 := congrArg StackSh.sH1 hK
  rw [k1]
  have hC : ∀ e e' : Array E,
      SameSh ((List.range P.y.LamM).foldl
          (fun (C : Aff) lm => C.addMul (Aff.slot (K'.sH1 + 1 + lm)) (e.getD lm zeroE)) aff0)
        ((List.range P.y.LamM).foldl
          (fun (C : Aff) lm => C.addMul (Aff.slot (K'.sH1 + 1 + lm)) (e'.getD lm zeroE)) aff0) :=
    fun e e' => foldl_rel _ _ _ (SameSh.refl _) fun lm a b hab =>
      SameSh.addMul hab (SameSh.refl _) _ _
  refine FlRel.bind (FlRel.levelIn _ _ _ (SameSh.refl (Aff.slot K'.sH1)) _) fun hd hd' hhd => ?_
  refine FlRel.bind (FlRel.getRel h.tT) fun tT tT' _ => ?_
  refine FlRel.bind (FlRel.enPoint _ _) fun rhoM rhoM' _ => ?_
  refine FlRel.bind (FlRel.levelIn _ _ _ (hC (eqTab rhoM) (eqTab rhoM')) _)
    fun hd2 hd2' hhd2 => ?_
  exact FlRel.pure ⟨hhd, hhd2⟩

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.FlRel.none
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.enPoint
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.getAny
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.get
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.getRel
#print axioms OnBytes.Desc.First.K4.Rt.normsStart_rel
#print axioms OnBytes.Desc.First.K4.Rt.hearNorms_rel
#print axioms OnBytes.Desc.First.K4.Rt.hearTerms_rel
#print axioms OnBytes.Desc.First.K4.Rt.NormsAlike.tT
#print axioms OnBytes.Desc.First.K4.Rt.parts_fold_rel
#print axioms OnBytes.Desc.First.K4.Rt.joinStart_rel
#print axioms OnBytes.Desc.First.K4.Rt.plainRounds_rel
#print axioms OnBytes.Desc.First.K4.Rt.hearStack_rel
#print axioms OnBytes.Desc.First.K4.Rt.hearGated_rel
#print axioms OnBytes.Desc.First.K4.Rt.NormsAlike
#print axioms OnBytes.Desc.First.K4.Rt.StackAlike
