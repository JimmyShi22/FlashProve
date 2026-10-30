-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsClaims.lean: THE THREE RUNS OF AN ATTENTION SEGMENT's CLAIMS
(firstRun, keysRun, secondRun: Johnson/Desc/First/Att/RunsP.lean) AT TWO INPUTS THAT MEET `ShIn`
(Johnson/Desc/K5/Honest/Law/RunsReaders.lean): THEY REFUSE TOGETHER, OR RETURN LISTS OF FORMS OF ONE
SHAPE, FORM BY FORM. After the library's Johnson/Desc/First/Att/Claims/SameClaims.lean and
Claims/Returns.lean, lemma for lemma. Definitions, and statements with their proofs.

Main names:
  `sameF_refl`, `same_forms`   a tactic: two forms made alike of parts of one shape have one shape
  `JSh`, `JSh.set`   two lists of key forms: one array of counts, forms of one shape
  `sameF_a`, `sameF_b`, `sameF_ite`, `sameF_keyKR`, `sameF_keyKFD`, `sameF_remForm`,
    `sameF_indexForm`, `sameF_keyWL`, `sameF_keyIX`, `sameF_keyWH`, `joinR16_JSh`   the key forms
  `sh_linPlanes` .. `sh_claim8`   the routines of claims 3 to 8
  `gather_sh`, `first_shapes`, `second_shapes`   **the runs "first" and "second": one list of
    shapes**; "first" hands on key forms of one shape
  `keys_shapes`   "keys" refuses at both, or hands these key forms on; it states no claim

Every statement is conditional on `ShIn`; `keys_shapes` on one set of the place's numbers, one input
of the lookup's at both, and `JSh`.
Limits. No field element is compared. Nothing says that a run returns anywhere, nor that two inputs
meet `ShIn`.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsReaders
import Johnson.Desc.First.Att.Claims.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP MaxP Pts SumP TablesP ScoreT Geo Ten
  CallG)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)
open VerifiableInference.Desc.First.Shape (AffSh affSh)
open K5Law (Any OptRel Same SameW SameRem SameScore optRel_refl forall₂_getElem? forall₂_zipIdx
  sameW_getD foldl_rel rc_size)

variable {K : ℕ} {i i' : In}

theorem sameF_refl (f : Aff) : SameF f f := rfl

/-- Two forms made alike of parts of one shape have one shape. Each rule is tried on the goal's own
signs alone (with_reducible): no definition is unfolded. Without that the unifier unfolds the
forms' operations to try a rule that does not fit, and runs out of heartbeats. -/
macro "same_forms" : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact sameF_const _ _
    | with_reducible exact sameF_refl _
    | with_reducible assumption
    | with_reducible apply sameF_add
    | with_reducible apply sameF_sub
    | with_reducible apply sameF_scale
    | with_reducible apply sameF_addMul))

/-! ## 1 The key forms -/

/-- Two lists of key forms: one array of counts; forms of one shape. -/
def JSh (j j' : JoinsP) : Prop := j.joined = j'.joined ∧ formsSh j.kf = formsSh j'.kf

theorem JSh.set {j j' : JoinsP} (h : JSh j j') (q : ℕ) {v v' : Aff} (hv : SameF v v') :
    JSh (j.set q v) (j'.set q v') := by
  obtain ⟨h1, h2⟩ := h
  unfold formsSh at h2
  unfold JSh JoinsP.set formsSh
  dsimp only
  refine ⟨by rw [h1], ?_⟩
  have hv' : affSh v = affSh v' := hv
  rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds, List.map_set, List.map_set, h2, hv']

theorem sameF_a {s s' : SumP} (h : ShSum s s') (b : ℕ) : SameF (s.a b) (s'.a b) := by
  unfold SumP.a
  rw [h.ends]
  exact rfl

theorem sameF_b {s s' : SumP} (h : ShSum s s') (b : ℕ) : SameF (s.b b) (s'.b b) := by
  unfold SumP.b
  rw [h.ends]
  exact rfl

theorem sameF_ite (c : Bool) {a a' b b' : Aff} (ha : SameF a a') (hb : SameF b b') :
    SameF (if c then a else b) (if c then a' else b') := by
  cases c
  · exact hb
  · exact ha

theorem sameF_keyKR {pc pc' : RemP} (h : pc.s0 = pc'.s0) :
    SameF (P.Runs.keyKR pc) (P.Runs.keyKR pc') := by
  unfold P.Runs.keyKR
  dsimp only
  rw [h]
  same_forms

theorem sameF_keyKFD (gC gOm : ℕ) {k k' : ScoreP} (h : k.s0 = k'.s0) :
    SameF (P.Runs.keyKFD gC gOm k) (P.Runs.keyKFD gC gOm k') := by
  unfold P.Runs.keyKFD
  dsimp only
  rw [h]
  same_forms

theorem sameF_remForm {d d' : DivP} (h : d.s5 = d'.s5) :
    SameF (P.Runs.remForm d) (P.Runs.remForm d') := by
  unfold P.Runs.remForm DivP.sACC DivP.sZC DivP.sZO
  rw [h]
  same_forms

theorem sameF_indexForm {d d' : DivP} (h : d.sIB = d'.sIB) (lt : ℕ) :
    SameF (P.Runs.indexForm d lt) (P.Runs.indexForm d' lt) := by
  unfold P.Runs.indexForm
  rw [h]
  exact sameF_refl _

theorem sameF_keyWL {d d' : DivP} (h : d.s5 = d'.s5) :
    SameF (P.Runs.keyWL d) (P.Runs.keyWL d') := by
  have hr := sameF_remForm h
  unfold P.Runs.keyWL DivP.sRH DivP.sZC DivP.sRHP
  dsimp only
  rw [h]
  same_forms

theorem sameF_keyIX (S : Geo) {d d' : DivP} (h : d.sIB = d'.sIB) :
    SameF (P.Runs.keyIX S d) (P.Runs.keyIX S d') := by
  have hi := sameF_indexForm h S.lt
  unfold P.Runs.keyIX
  same_forms

theorem sameF_keyWH {d d' : DivP} (h : d.s5h = d'.s5h) :
    SameF (P.Runs.keyWH d) (P.Runs.keyWH d') := by
  unfold P.Runs.keyWH
  dsimp only
  rw [h]
  same_forms

theorem joinR16_JSh (S : Geo) {d d' : DivP} (h5 : d.s5 = d'.s5) (hI : d.sIB = d'.sIB)
    {j j' : JoinsP} (hj : JSh j j') : JSh (P.Runs.joinR16 S d j) (P.Runs.joinR16 S d' j') := by
  have hW := sameF_keyWL h5
  have hX := sameF_keyIX S hI
  unfold P.Runs.joinR16
  dsimp only
  refine foldl_rel (R := JSh) (fun s s' x h => ?_) _ hj
  split
  · refine h.set _ ?_
    have e1 : SameF
        (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL d else Aff.ofConst zeroE)
        (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL d' else Aff.ofConst zeroE) :=
      sameF_ite _ (sameF_add (sameF_const _ _) hW) (sameF_const _ _)
    exact sameF_ite _ (sameF_add e1 hX) e1
  · exact h

/-! ## 2 Claim 3 -/

theorem sh_linPlanes (H : ShIn i i') {pc pc' : RemP} (h : ShRem pc pc') :
    RSh K Any (P.Runs.linPlanes i pc) (P.Runs.linPlanes i' pc') := by
  unfold P.Runs.linPlanes
  rw [h.same.np, h.s0]
  refine RSh.forM1 (fun x => RSh.bind (R := SameF)
    (sh_lessPieces rfl h.same.pw _ _ fun w w' hl ha => ?_) fun _ _ hf => RSh.lin hf) _
  rw [hl, ha, H.same.t.tA, h.same.isD]
  exact sh_plane H _ _ _ _ _ _ h.same.z _

theorem sh_callKR (H : ShIn i i') (q : ℕ) :
    RSh K SameF (P.Runs.callKR i q) (P.Runs.callKR i' q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  refine RSh.foldlM₂ (R := SameF) (P := ShRem) (fun _ _ pc pc' hv h => ?_) H.planes
    (sameF_const _ _)
  rw [h.same.call]
  exact RSh.ite Iff.rfl
    (RSh.bind (sh_linPlanes H h) fun _ _ _ => RSh.pure (sameF_add hv (sameF_keyKR h.s0)))
    (RSh.pure hv)

theorem sh_claim3 (H : ShIn i i') {j j' : JoinsP} (hj : JSh j j') :
    RSh K JSh (P.Runs.claim3 i j) (P.Runs.claim3 i' j') := by
  unfold P.Runs.claim3
  rw [H.same.g]
  refine RSh.foldlM1 (R := JSh) (fun j j' x hj => ?_) _ hj
  exact RSh.ite Iff.rfl (RSh.bind (sh_callKR H x.2) fun _ _ hv => RSh.pure (hj.set _ hv))
    (RSh.pure hj)

/-! ## 3 Claim 4 -/

theorem sh_endValues (H : ShIn i i') {k k' : ScoreP} (hk : ShScore k k') (tb : ScoreT)
    (rc rc' : Array E) (hrc : rc.size = rc'.size) (b : ℕ) {w w' : W1} (hl : w.lam = w'.lam)
    (ha : w.a = w'.a) :
    RSh K Any (P.Runs.endValues i k tb rc b w) (P.Runs.endValues i' k' tb rc' b w') := by
  unfold P.Runs.endValues
  rw [hl, ha, H.same.g]
  exact RSh.bind (sh_readHead H _ _ _ _ _ _ hrc _ _) fun _ _ hq =>
    RSh.bind (RSh.lin (sameF_sub (sameF_a hk.sc b) hq)) fun _ _ _ =>
    RSh.bind (sh_readGroup H _ _ _ _ _ _ hrc _) fun _ _ hx =>
    RSh.lin (sameF_sub (sameF_b hk.sc b) hx)

theorem sh_unitKFD (H : ShIn i i') (n : ℕ) {k k' : ScoreP} (hk : ShScore k k') :
    RSh K Any (P.Runs.unitKFD i n k) (P.Runs.unitKFD i' n k') := by
  unfold P.Runs.unitKFD
  dsimp only
  rw [H.same.t.score, H.same.g, hk.same.claim, hk.s0]
  refine RSh.bind (RSh.need (optRel_refl _)) fun tb tb' e => ?_
  subst e
  refine RSh.bind (R := ShRem) (RSh.need ?_) fun pc pc' hpc => ?_
  · rw [← Array.getElem?_toList, ← Array.getElem?_toList]
    exact forall₂_getElem? H.planes _
  refine RSh.bind (sh_linPlanes H hpc) fun _ _ _ => ?_
  refine RSh.bind (R := SameF) (sh_lessPieces rfl hk.same.pw _ _ fun w w' hl ha => ?_)
    fun _ _ hf => ?_
  · rw [hl, ha]
    exact sh_readMaximum H _ _ _ _ _
  refine RSh.bind (RSh.lin hf) fun _ _ _ => RSh.bind (RSh.lin hk.sc.row) fun _ _ _ => ?_
  refine RSh.forM₂ (fun x x' h => ?_) (forall₂_zipIdx hk.same.pw 0)
  rw [h.2]
  exact sh_endValues H hk _ _ _ (by rw [Array.size_extract, Array.size_extract, hk.same.r]) _
    h.1.1 h.1.2

theorem sh_callKFD (H : ShIn i i') (q : ℕ) (c : CallG) :
    RSh K SameF (P.Runs.callKFD i q c) (P.Runs.callKFD i' q c) := by
  unfold P.Runs.callKFD
  rw [H.same.g]
  refine RSh.foldlM₂ (R := SameF) (fun _ _ x x' hv h => ?_) (forall₂_zipIdx H.scores 0)
    (sameF_const _ _)
  rw [h.1.same.call, h.2]
  exact RSh.ite Iff.rfl
    (RSh.bind (sh_unitKFD H _ h.1) fun _ _ _ =>
      RSh.pure (sameF_add hv (sameF_keyKFD _ _ h.1.s0)))
    (RSh.pure hv)

theorem sh_claim4 (H : ShIn i i') {j j' : JoinsP} (hj : JSh j j') :
    RSh K JSh (P.Runs.claim4 i j) (P.Runs.claim4 i' j') := by
  unfold P.Runs.claim4
  rw [H.same.g]
  refine RSh.foldlM1 (R := JSh) (fun j j' x hj => ?_) _ hj
  exact RSh.ite Iff.rfl (RSh.bind (sh_callKFD H x.2 x.1) fun _ _ hv => RSh.pure (hj.set _ hv))
    (RSh.pure hj)

/-! ## 4 Claim 5 -/

theorem sh_endValuesE (H : ShIn i i') (b : ℕ) {w w' : W1} (hl : w.lam = w'.lam)
    (ha : w.a = w'.a) : RSh K Any (P.Runs.endValuesE i b w) (P.Runs.endValuesE i' b w') := by
  unfold P.Runs.endValuesE
  dsimp only
  rw [hl, ha, H.same.g, H.same.t.hE, H.same.t.qO]
  exact RSh.bind (sh_readDenominator H _ _ _ _ _) fun _ _ hz =>
    RSh.bind (RSh.lin (sameF_sub (sameF_a H.scE b) hz)) fun _ _ _ =>
    RSh.bind (sh_readHead H _ _ _ _ _ _ H.same.p.d.zcW _ _) fun _ _ ho =>
    RSh.lin (sameF_sub (sameF_b H.scE b) ho)

theorem sh_claim5 (H : ShIn i i') {j j' : JoinsP} (hj : JSh j j') :
    RSh K JSh (P.Runs.claim5 i j) (P.Runs.claim5 i' j') := by
  unfold P.Runs.claim5 DivP.sZC DivP.sRH DivP.sRHP
  dsimp only
  rw [H.same.g, H.same.t.hW, H.same.t.tO, H.same.t.hX, H.same.p.d.qWH, H.s5, H.s5h, H.sIB]
  refine RSh.bind (R := SameF) (sh_lessPieces rfl H.same.p.d.pwW _ _ fun w w' hl ha => ?_)
    fun _ _ h1 => ?_
  · rw [hl, ha]; exact sh_readDenominator H _ _ _ _ _
  refine RSh.bind (R := SameF) (sh_lessPieces rfl H.same.p.d.pwW _ _ fun w w' hl ha => ?_)
    fun _ _ h2 => ?_
  · rw [hl, ha]; exact sh_readHead H _ _ _ _ _ _ H.same.p.d.zcW _ _
  refine RSh.bind (R := SameF) (sh_lessPieces rfl H.same.p.d.pwW _ _ fun w w' hl ha => ?_)
    fun _ _ h3 => ?_
  · rw [hl, ha]; exact sh_readHead H _ _ _ _ _ _ H.same.p.d.zcW _ _
  refine RSh.bind (R := SameF) (sh_lessPieces rfl H.same.p.d.pwH _ _ fun w w' hl ha => ?_)
    fun _ _ h4 => ?_
  · rw [hl, ha]; exact sh_readHead H _ _ _ _ _ _ H.same.p.d.zcH _ _
  refine RSh.bind (R := SameF) (sh_lessPieces rfl H.same.p.d.pwH _ _ fun w w' hl ha => ?_)
    fun _ _ h5 => ?_
  · rw [hl, ha]; exact sh_readHead H _ _ _ _ _ _ H.same.p.d.zcH _ _
  refine RSh.bind (RSh.lin h1) fun _ _ _ => RSh.bind (RSh.lin h2) fun _ _ _ =>
    RSh.bind (RSh.lin h3) fun _ _ _ => ?_
  refine RSh.bind (R := Any) (RSh.forIn1 (fun k => ?_) _) fun _ _ _ => ?_
  · refine RSh.bind (R := SameF) (sh_lessPieces rfl H.same.p.d.pwX _ _ fun w w' hl ha => ?_)
      fun _ _ hf => RSh.linYield hf
    rw [hl, ha]; exact sh_readIndexBit H _ _ _ _ _ _
  refine RSh.bind (RSh.lin h4) fun _ _ _ => RSh.bind (RSh.lin h5) fun _ _ _ =>
    RSh.bind (RSh.lin H.scE.row) fun _ _ _ => ?_
  refine RSh.bind (R := Any) (RSh.forIn1 (fun b => ?_) _) fun _ _ _ => ?_
  · exact RSh.bind
      (sh_endValuesE H b (sameW_getD H.same.p.d.pwW b).1 (sameW_getD H.same.p.d.pwW b).2)
      fun _ _ _ => RSh.yield
  exact RSh.pure ((joinR16_JSh _ H.s5 H.sIB hj).set _ (sameF_keyWH H.s5h))

/-! ## 5 Claims 6, 7, 8 -/

theorem sh_valueProduct (H : ShIn i i') {sc sc' : SumP} (hs : ShSum sc sc') (tS : ℕ)
    (pt pt' : Array E) (hpt : pt.size = pt'.size) (isD : Bool) (tV : ℕ) :
    RSh K Any (P.Runs.valueProduct i sc tS pt isD tV)
      (P.Runs.valueProduct i' sc' tS pt' isD tV) := by
  unfold P.Runs.valueProduct
  rw [H.same.g]
  refine RSh.bind (RSh.lin hs.row) fun _ _ _ => RSh.bind (R := Any) (RSh.forIn1 (fun b => ?_) _)
    fun _ _ _ => RSh.pure trivial
  dsimp only
  rw [(sameW_getD H.same.p.d.pwW b).1, (sameW_getD H.same.p.d.pwW b).2]
  refine RSh.bind (sh_plane H _ _ _ _ _ _ hpt _) fun _ _ h3 =>
    RSh.bind (sh_plane H _ _ _ _ _ _ hpt _) fun _ _ h4 =>
    RSh.bind (RSh.lin (sameF_sub (sameF_a hs b)
      (sameF_add (sameF_add h3 (sameF_const _ _)) (sameF_scale h4 _ _)))) fun _ _ _ =>
    RSh.bind (sh_readGroup H _ _ _ _ _ _ H.same.p.d.zcW _) fun _ _ hv =>
    RSh.linYield (sameF_sub (sameF_b hs b) (sameF_add (sameF_const _ _) hv))

theorem sh_claim6 (H : ShIn i i') : RSh K Any (P.Runs.claim6 i) (P.Runs.claim6 i') := by
  unfold P.Runs.claim6 DivP.sACC DivP.sZC
  dsimp only
  rw [H.same.t.tVM, H.same.t.qVM, H.same.t.tVD, H.same.t.qVD, H.sCl, H.s5]
  refine RSh.bind (RSh.lin ?_) fun _ _ _ =>
    RSh.bind (sh_valueProduct H H.vpm _ _ _ H.same.t.ptM _ _) fun _ _ _ =>
    sh_valueProduct H H.vpd _ _ _ H.same.t.ptD _ _
  same_forms

theorem sh_claim7 (H : ShIn i i') : RSh K Any (P.Runs.claim7 i) (P.Runs.claim7 i') := by
  unfold P.Runs.claim7 MaxP.sKC MaxP.sIb
  dsimp only
  rw [H.same.g, H.same.t.hT, H.same.t.qF, H.same.t.qKx, H.same.t.hPi, H.sM6, H.scd.ends]
  refine RSh.bind (R := Any) (RSh.forIn1 (fun b => ?_) _) fun _ _ _ => ?_
  · exact RSh.bind (sh_readMaximum H _ _ _ _ _) fun _ _ hm => RSh.linYield (sameF_sub rfl hm)
  refine RSh.bind (RSh.lin H.scF.row) fun _ _ _ => ?_
  refine RSh.bind (R := Any) (RSh.forIn1 (fun b => ?_) _) fun _ _ _ => ?_
  · exact RSh.bind (sh_readHead H _ _ _ _ _ _ (rc_size H.same) _ _) fun _ _ hq =>
      RSh.linYield (sameF_sub (sameF_a H.scF b) hq)
  refine RSh.bind (RSh.lin H.scd.row) fun _ _ _ => ?_
  refine RSh.bind (R := Any) (RSh.forIn1 (fun lam => ?_) _) fun _ _ _ => ?_
  · exact RSh.bind (sh_readGroup H _ _ _ _ _ _ (rc_size H.same) _) fun _ _ hk =>
      RSh.linYield (sameF_sub rfl hk)
  refine RSh.bind (R := Any) (RSh.forIn1 (fun b => ?_) _) fun _ _ _ => RSh.pure trivial
  refine RSh.bind (R := Any) (RSh.forIn1 (fun k => ?_) _) fun _ _ _ =>
    RSh.bind (R := Any) (RSh.pure trivial) fun _ _ _ => RSh.yield
  exact RSh.bind (sh_readIndexBit H _ _ _ _ _ _) fun _ _ hb => RSh.linYield (sameF_sub rfl hb)

theorem sh_claim8 (H : ShIn i i') : RSh K Any (P.Runs.claim8 i) (P.Runs.claim8 i') := by
  unfold P.Runs.claim8
  dsimp only
  rw [H.same.g, H.same.t.hR2]
  refine RSh.bind (RSh.lin H.scH.row) fun _ _ _ => RSh.bind (R := Any) (RSh.forIn1 (fun b => ?_) _)
    fun _ _ _ => RSh.pure trivial
  refine RSh.bind (RSh.lin (sameF_add (sameF_sub (sameF_b H.scH b) (sameF_a H.scH b))
    (sameF_const _ _))) fun _ _ _ => ?_
  refine RSh.bind (R := SameF) ?_ fun _ _ hf => RSh.linYield hf
  refine RSh.foldlM1 (R := SameF) (fun _ _ k hs => ?_) _ (sameF_a H.scH b)
  exact RSh.bind (sh_readIndexBit H _ _ _ _ _ _) fun _ _ hb => RSh.pure (sameF_addMul hs hb _ _)

/-! ## 6 The runs -/

/-- From no form: both refuse, or both return related values and lists of forms of one shape. -/
theorem gather_sh {α α' : Type} {R : α → α' → Prop} {r : W α} {r' : W α'} (h : RSh K R r r') :
    OptRel (fun x x' => R x.1 x'.1 ∧ x.2.map affSh = x'.2.map affSh) (P.Runs.gather K r)
      (P.Runs.gather K r') := by
  unfold P.Runs.gather
  have h0 := h #[] #[] rfl
  have e : (r.run K).run #[] = r K #[] := rfl
  have e' : (r'.run K).run #[] = r' K #[] := rfl
  rw [e, e']
  cases h1 : r K #[] <;> cases h2 : r' K #[] <;> rw [h1, h2] at h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact h0

/-- **"first": both refuse, or both return: one list of shapes, and key forms of one shape.**
CONDITIONAL on `ShIn`. -/
theorem first_shapes (H : ShIn i i') (K : ℕ) :
    OptRel (fun x x' => x.1.map affSh = x'.1.map affSh ∧ JSh x.2 x'.2) (P.Runs.firstRun i K)
      (P.Runs.firstRun i' K) := by
  unfold P.Runs.firstRun
  refine K5Law.OptRel.map (R := fun x x' => JSh x.1 x'.1 ∧ x.2.map affSh = x'.2.map affSh)
    (gather_sh ?_) _ _ fun _ _ h => ⟨h.2, h.1⟩
  rw [H.same.g]
  exact RSh.bind (sh_claim3 H ⟨rfl, rfl⟩) fun _ _ h3 => RSh.bind (sh_claim4 H h3) fun _ _ h4 =>
    sh_claim5 H h4

/-- **"second": both refuse, or both return one list of shapes.** CONDITIONAL on `ShIn`. -/
theorem second_shapes (H : ShIn i i') (K : ℕ) :
    OptRel (fun x x' => x.map affSh = x'.map affSh) (P.Runs.secondRun i K)
      (P.Runs.secondRun i' K) := by
  unfold P.Runs.secondRun
  refine K5Law.OptRel.map (R := fun x x' => Any x.1 x'.1 ∧ x.2.map affSh = x'.2.map affSh)
    (gather_sh ?_) _ _ fun _ _ h => h.2
  exact RSh.bind (sh_claim6 H) fun _ _ _ => RSh.bind (sh_claim7 H) fun _ _ _ => sh_claim8 H

/-- **"keys": both refuse, or both hand on key forms of one shape.** It states no claim. CONDITIONAL
on: one set of the place's numbers; ONE input k3 of the lookup's at both (public numbers and a
function on them); key forms that meet `JSh`. -/
theorem keys_shapes (hg : i.g = i'.g) (k3 : P.Runs.PadIn) {j j' : JoinsP} (hj : JSh j j') :
    OptRel (fun x x' => formsSh x = formsSh x') (P.Runs.keysRun i k3 j)
      (P.Runs.keysRun i' k3 j') := by
  have e := K5Law.keys_together i i' k3 j j' hg hj.1
  cases h1 : P.Runs.keysRun i k3 j with
  | none =>
    cases h2 : P.Runs.keysRun i' k3 j' with
    | none => trivial
    | some x' =>
      rw [h1, h2] at e
      cases e
  | some x =>
    cases h2 : P.Runs.keysRun i' k3 j' with
    | none =>
      rw [h1, h2] at e
      cases e
    | some x' =>
      show formsSh x = formsSh x'
      rw [K5Law.keys_is _ _ _ _ h1, K5Law.keys_is _ _ _ _ h2]
      exact hj.2

end H2K5.Honest

#print axioms H2K5.Honest.sameF_refl
#print axioms H2K5.Honest.JSh.set
#print axioms H2K5.Honest.sameF_a
#print axioms H2K5.Honest.sameF_b
#print axioms H2K5.Honest.sameF_ite
#print axioms H2K5.Honest.sameF_keyKR
#print axioms H2K5.Honest.sameF_keyKFD
#print axioms H2K5.Honest.sameF_remForm
#print axioms H2K5.Honest.sameF_indexForm
#print axioms H2K5.Honest.sameF_keyWL
#print axioms H2K5.Honest.sameF_keyIX
#print axioms H2K5.Honest.sameF_keyWH
#print axioms H2K5.Honest.joinR16_JSh
#print axioms H2K5.Honest.sh_linPlanes
#print axioms H2K5.Honest.sh_callKR
#print axioms H2K5.Honest.sh_claim3
#print axioms H2K5.Honest.sh_endValues
#print axioms H2K5.Honest.sh_unitKFD
#print axioms H2K5.Honest.sh_callKFD
#print axioms H2K5.Honest.sh_claim4
#print axioms H2K5.Honest.sh_endValuesE
#print axioms H2K5.Honest.sh_claim5
#print axioms H2K5.Honest.sh_valueProduct
#print axioms H2K5.Honest.sh_claim6
#print axioms H2K5.Honest.sh_claim7
#print axioms H2K5.Honest.sh_claim8
#print axioms H2K5.Honest.gather_sh
#print axioms H2K5.Honest.first_shapes
#print axioms H2K5.Honest.second_shapes
#print axioms H2K5.Honest.keys_shapes
