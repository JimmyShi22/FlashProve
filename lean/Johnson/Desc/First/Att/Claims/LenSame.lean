-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LenSame.lean: kind K5: at two records that agree in what is public
(Same, Johnson/Desc/First/Att/Claims/Same.lean) the kind's runs "first" and "second" gather lists of
one length.

How made: Johnson/Desc/First/Att/Claims/RS.lean's relation RS says of two routines: from whatever
was gathered, both refuse, or both return related values. Here the same relation also carries the
number of forms gathered: from equally many forms, both refuse, or both return related values and
have gathered equally many. The lemmas on the ways of putting routines together are proved anew for
it; the lemmas rs_… on the kind's routines are those of Johnson/Desc/First/Att/Claims/Same.lean and
Johnson/Desc/First/Att/Claims/SameClaims.lean, statement and proof word for word, in the namespace
K5Law.Len, where the names RS and rs_… mean the new ones.
Main names (namespace K5Law.Len): `ORel`, `RS`; `RS.pure` … `RS.linYield`; `rs_uEnt` … `rs_claim8`;
`gather_len`; `first_len`, `second_len`: Same i i', both runs return: the two lists have one length.
So, at every record that agrees with the blank one in what is public, the number of claims of
"first" and of "second" is that of the dry run on blank points: a number of the plan. That a record
made of what was heard agrees with the blank one in what is public is not shown in this file. "keys"
gathers none and "join" one, by their definitions.
Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem on such a
routine's return; the runs spoken of are the kind's own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SameClaims
import Johnson.Desc.First.Att.Claims.Returns

set_option autoImplicit false

namespace K5Law.Len
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP MaxP Pts SumP TablesP ScoreT Geo Ten CallG)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)
open VerifiableInference.Desc.First.Att.P.Runs (W)
open VerifiableInference.Desc.First.Att

variable {α α' β β' σ σ' : Type} {K : ℕ}

/-- Both refuse, or both return, the values are related and equally many forms are gathered. -/
def ORel (R : α → α' → Prop) : Option (α × Array Aff) → Option (α' × Array Aff) → Prop
  | some x, some x' => R x.1 x'.1 ∧ x.2.size = x'.2.size
  | none, none => True
  | _, _ => False

/-- At K, from equally many forms gathered: both refuse, or both return related values and have gathered equally many. -/
def RS (K : ℕ) (R : α → α' → Prop) (r : W α) (r' : W α') : Prop :=
  ∀ acc acc', acc.size = acc'.size → ORel R (r K acc) (r' K acc')

theorem RS.pure {R : α → α' → Prop} {a : α} {a' : α'} (h : R a a') :
    RS K R (Pure.pure a : W α) (Pure.pure a' : W α') := fun _ _ hs => ⟨h, hs⟩

theorem RS.fail {R : α → α' → Prop} : RS K R (failure : W α) (failure : W α') := fun _ _ _ => trivial

theorem RS.bind {R : α → α' → Prop} {Q : β → β' → Prop} {r : W α} {r' : W α'} {k : α → W β}
    {k' : α' → W β'} (h1 : RS K R r r') (h2 : ∀ a a', R a a' → RS K Q (k a) (k' a')) :
    RS K Q (r >>= k) (r' >>= k') := by
  intro acc acc' hs
  have h := h1 acc acc' hs
  cases hr : r K acc with
  | none =>
    cases hr' : r' K acc' with
    | none => rw [bind_none hr, bind_none hr']; trivial
    | some x' => rw [hr, hr'] at h; exact h.elim
  | some x =>
    cases hr' : r' K acc' with
    | none => rw [hr, hr'] at h; exact h.elim
    | some x' =>
      rw [hr, hr'] at h
      rw [bind_some hr, bind_some hr']
      exact h2 _ _ h.1 _ _ h.2

theorem RS.mono {R Q : α → α' → Prop} {r : W α} {r' : W α'} (h : RS K R r r')
    (hRQ : ∀ a a', R a a' → Q a a') : RS K Q r r' := by
  intro acc acc' hs
  have h := h acc acc' hs
  cases hr : r K acc <;> cases hr' : r' K acc' <;> rw [hr, hr'] at h
  · trivial
  · exact h.elim
  · exact h.elim
  · exact ⟨hRQ _ _ h.1, h.2⟩

theorem RS.ite {R : α → α' → Prop} {p q : Prop} [Decidable p] [Decidable q] (hpq : p ↔ q)
    {x y : W α} {x' y' : W α'} (hx : RS K R x x') (hy : RS K R y y') :
    RS K R (if p then x else y) (if q then x' else y') := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq.1 hp)]; exact hx
  · rw [if_neg hp, if_neg (fun h => hp (hpq.2 h))]; exact hy

theorem RS.read : RS K Eq (read : W ℕ) (read : W ℕ) := fun _ _ hs => ⟨rfl, hs⟩

theorem RS.lin (f f' : Aff) : RS K Any (W.lin f) (W.lin f') := fun acc acc' hs => by
  show Any _ _ ∧ (acc.push f).size = (acc'.push f').size
  exact ⟨trivial, by rw [Array.size_push, Array.size_push, hs]⟩

theorem RS.mustAs (n n' : String) {b b' : Bool} (h : b = b') :
    RS K Any (P.Runs.mustAs n b) (P.Runs.mustAs n' b') := by
  subst h
  unfold P.Runs.mustAs
  split
  · exact RS.pure trivial
  · exact RS.fail

theorem RS.refuse {R : α → α' → Prop} (n n' : String) :
    RS K R (P.Runs.refuse n : W α) (P.Runs.refuse n' : W α') := RS.fail

theorem RS.need {R : α → α' → Prop} {x : Option α} {x' : Option α'} (h : OptRel R x x') :
    RS K R (W.need x) (W.need x') := by
  cases x <;> cases x'
  · exact RS.fail
  · exact h.elim
  · exact h.elim
  · exact RS.pure h

theorem RS.foldlM₂ {P : α → α' → Prop} {R : σ → σ' → Prop} {f : σ → α → W σ} {f' : σ' → α' → W σ'}
    (hf : ∀ s s' a a', R s s' → P a a' → RS K R (f s a) (f' s' a')) :
    ∀ {xs : List α} {xs' : List α'}, List.Forall₂ P xs xs' → ∀ {s : σ} {s' : σ'}, R s s' →
      RS K R (xs.foldlM f s) (xs'.foldlM f' s')
  | _, _, .nil, _, _, hs => by
    simp only [List.foldlM_nil]
    exact RS.pure hs
  | _, _, .cons ha hl, _, _, hs => by
    simp only [List.foldlM_cons]
    exact RS.bind (hf _ _ _ _ hs ha) fun _ _ h => RS.foldlM₂ hf hl h

theorem RS.foldlM1 {R : σ → σ' → Prop} {f : σ → α → W σ} {f' : σ' → α → W σ'}
    (hf : ∀ s s' a, R s s' → RS K R (f s a) (f' s' a)) (xs : List α) {s : σ} {s' : σ'}
    (hs : R s s') : RS K R (xs.foldlM f s) (xs.foldlM f' s') :=
  RS.foldlM₂ (P := Eq) (fun s s' a _ h e => e ▸ hf s s' a h) (forall₂_same (fun _ => rfl) xs) hs

theorem RS.forM₂ {P : α → α' → Prop} {f : α → W PUnit} {f' : α' → W PUnit}
    (hf : ∀ a a', P a a' → RS K Any (f a) (f' a')) :
    ∀ {xs : List α} {xs' : List α'}, List.Forall₂ P xs xs' → RS K Any (xs.forM f) (xs'.forM f')
  | _, _, .nil => RS.pure trivial
  | _, _, .cons ha hl => RS.bind (hf _ _ ha) fun _ _ _ => RS.forM₂ hf hl

theorem RS.forM1 {f f' : α → W PUnit} (hf : ∀ a, RS K Any (f a) (f' a)) (xs : List α) :
    RS K Any (xs.forM f) (xs.forM f') :=
  RS.forM₂ (P := Eq) (fun a _ e => e ▸ hf a) (forall₂_same (fun _ => rfl) xs)

theorem RS.forIn1 {f f' : α → PUnit → W (ForInStep PUnit)}
    (hf : ∀ a, RS K Yield (f a PUnit.unit) (f' a PUnit.unit)) :
    ∀ xs : List α, RS K Any (forIn xs PUnit.unit f) (forIn xs PUnit.unit f')
  | [] => by
    rw [List.forIn_nil, List.forIn_nil]
    exact RS.pure trivial
  | x :: xs => by
    rw [List.forIn_cons, List.forIn_cons]
    refine RS.bind (hf x) fun a a' h => ?_
    obtain ⟨rfl, rfl⟩ := h
    exact RS.forIn1 hf xs

theorem RS.yield : RS K Yield (Pure.pure (ForInStep.yield PUnit.unit) : W (ForInStep PUnit))
    (Pure.pure (ForInStep.yield PUnit.unit)) := RS.pure ⟨rfl, rfl⟩

/-- A step that ends in one form. -/
theorem RS.linYield (f f' : Aff) :
    RS K Yield (W.lin f >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _))
      (W.lin f' >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _)) :=
  RS.bind (RS.lin f f') fun _ _ _ => RS.yield

/-! ### the readers: Johnson/Desc/First/Att/Claims/Same.lean's, word for word -/

open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP MaxP Pts SumP TablesP Geo Ten CallG)

theorem rs_uEnt (t t' x : ℕ) : RS K Any (P.Runs.uEnt t x) (P.Runs.uEnt t' x) := by
  unfold P.Runs.uEnt
  refine RS.bind RS.read fun a a' e => ?_
  subst e
  exact RS.bind (RS.mustAs _ _ rfl) fun _ _ _ => RS.pure trivial

variable {i i' : In}

theorem rs_u3at (H : Same i i') (t n : ℕ) : RS K Any (P.Runs.u3at i t n) (P.Runs.u3at i' t n) := by
  unfold P.Runs.u3at
  rw [H.t.tabLen]
  exact RS.bind (RS.mustAs _ _ rfl) fun _ _ _ => rs_uEnt _ _ _

theorem rs_weighted (n : ℕ) (w w' : Array E) (f f' : ℕ → W Aff) (hf : ∀ k, RS K Any (f k) (f' k)) :
    RS K Any (P.Runs.weighted n w f) (P.Runs.weighted n w' f') := by
  unfold P.Runs.weighted
  exact RS.foldlM1 (fun _ _ k _ => RS.bind (hf k) fun _ _ _ => RS.pure trivial) _ trivial

theorem rs_plane (H : Same i i') (t x lam a : ℕ) (z z' : Array E) (hz : z.size = z'.size)
    (isD : Bool) : RS K Any (P.Runs.plane i t x lam a z isD) (P.Runs.plane i' t x lam a z' isD) := by
  unfold P.Runs.plane
  dsimp only
  rw [H.g, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract, hz]
  exact rs_weighted _ _ _ _ _ fun _ => rs_u3at H _ _

theorem rs_shV (H : Same i i') (t off nl J lam j : ℕ) :
    RS K Any (P.Runs.shV i t off nl J lam j) (P.Runs.shV i' t off nl J lam j) := by
  unfold P.Runs.shV
  rw [H.g]
  exact rs_weighted _ _ _ _ _ fun _ => rs_u3at H _ _

theorem rs_overG (H : Same i i') (zg zg' : Array E) (f f' : ℕ → W Aff)
    (hf : ∀ k, RS K Any (f k) (f' k)) : RS K Any (P.Runs.overG i zg f) (P.Runs.overG i' zg' f') := by
  unfold P.Runs.overG
  rw [H.g]
  exact rs_weighted _ _ _ _ _ hf

theorem rs_readDenominator (H : Same i i') (t : ℕ) (zg zg' : Array E) (lam a : ℕ) :
    RS K Any (P.Runs.readDenominator i t zg lam a) (P.Runs.readDenominator i' t zg' lam a) := by
  unfold P.Runs.readDenominator
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_shV H _ _ _ _ _ _

theorem rs_readMaximum (H : Same i i') (t : ℕ) (zg zg' : Array E) (lam a : ℕ) :
    RS K Any (P.Runs.readMaximum i t zg lam a) (P.Runs.readMaximum i' t zg' lam a) := by
  unfold P.Runs.readMaximum
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_shV H _ _ _ _ _ _

theorem rs_readIndexBit (H : Same i i') (t : ℕ) (zg zg' : Array E) (lam a k : ℕ) :
    RS K Any (P.Runs.readIndexBit i t zg lam a k) (P.Runs.readIndexBit i' t zg' lam a k) := by
  unfold P.Runs.readIndexBit
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_shV H _ _ _ _ _ _

theorem rs_xl (H : Same i i') (t : ℕ) (X : Ten) (lam hd : ℕ) (zc zc' : Array E)
    (hz : zc.size = zc'.size) : RS K Any (P.Runs.xl i t X lam hd zc) (P.Runs.xl i' t X lam hd zc') := by
  unfold P.Runs.xl
  dsimp only
  rw [H.g]
  have hc := cutLast_rel (zc.extract 0 i'.g.ldh) (zc'.extract 0 i'.g.ldh)
    (by rw [Array.size_extract, Array.size_extract, hz]) i'.g.ls
  cases h1 : P.cutLast (zc.extract 0 i'.g.ldh) i'.g.ls <;>
    cases h2 : P.cutLast (zc'.extract 0 i'.g.ldh) i'.g.ls <;> rw [h1, h2] at hc
  · exact RS.refuse _ _
  · exact hc.elim
  · exact hc.elim
  · dsimp only
    cases P.headFeat X hd i'.g.dh with
    | none => exact RS.refuse _ _
    | some j0 =>
      dsimp only
      rw [eqTab_size, eqTab_size, hc]
      exact rs_weighted _ _ _ _ _ fun _ => rs_weighted _ _ _ _ _ fun _ => rs_u3at H _ _

theorem rs_readHead (H : Same i i') (t : ℕ) (X : Ten) (zg zg' zc zc' : Array E)
    (hz : zc.size = zc'.size) (lam a : ℕ) :
    RS K Any (P.Runs.readHead i t X zg zc lam a) (P.Runs.readHead i' t X zg' zc' lam a) := by
  unfold P.Runs.readHead
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_xl H _ _ _ _ _ _ hz

theorem rs_readGroup (H : Same i i') (t : ℕ) (X : Ten) (zg zg' zc zc' : Array E)
    (hz : zc.size = zc'.size) (lam : ℕ) :
    RS K Any (P.Runs.readGroup i t X zg zc lam) (P.Runs.readGroup i' t X zg' zc' lam) := by
  unfold P.Runs.readGroup
  exact rs_overG H _ _ _ _ fun g => rs_xl H _ _ _ _ _ _ hz

theorem rs_lessPieces (s s' : Aff) {pw pw' : Array W1} (hp : SameW pw pw') (f f' : W1 → W Aff)
    (hf : ∀ w w' : W1, w.lam = w'.lam → w.a = w'.a → RS K Any (f w) (f' w')) :
    RS K Any (P.Runs.lessPieces s pw f) (P.Runs.lessPieces s' pw' f') := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact RS.foldlM₂ (fun _ _ w w' _ h => RS.bind (hf w w' h.1 h.2) fun _ _ _ => RS.pure trivial)
    hp trivial

/-! ### the claims: Johnson/Desc/First/Att/Claims/SameClaims.lean's, word for word -/

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

/-! ### the lengths -/

theorem gather_len {R : α → α' → Prop} {r : W α} {r' : W α'} (h : RS K R r r') {x : α × List Aff}
    {x' : α' × List Aff} (h1 : P.Runs.gather K r = some x) (h2 : P.Runs.gather K r' = some x') :
    x.2.length = x'.2.length := by
  unfold P.Runs.gather at h1 h2
  have h0 := h #[] #[] rfl
  have e : (r.run K).run #[] = r K #[] := rfl
  have e' : (r'.run K).run #[] = r' K #[] := rfl
  rw [e] at h1
  rw [e'] at h2
  cases a1 : r K #[] with
  | none => rw [a1] at h1; cases h1
  | some y =>
    cases a2 : r' K #[] with
    | none => rw [a2] at h2; cases h2
    | some y' =>
      rw [a1, a2] at h0
      rw [a1] at h1
      rw [a2] at h2
      rw [← Option.some.inj h1, ← Option.some.inj h2]
      show y.2.toList.length = y'.2.toList.length
      rw [Array.length_toList, Array.length_toList]
      exact h0.2

/-- **"first" gathers equally many forms at two records that agree in what is public.** -/
theorem first_len (H : Same i i') {l l' : List Aff} {j j' : JoinsP}
    (h1 : P.Runs.firstRun i K = some (l, j)) (h2 : P.Runs.firstRun i' K = some (l', j')) :
    l.length = l'.length := by
  unfold P.Runs.firstRun at h1 h2
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h1 h2
  obtain ⟨x, g1, rfl, -⟩ := h1
  obtain ⟨x', g2, rfl, -⟩ := h2
  refine gather_len (R := JR) ?_ g1 g2
  rw [H.g]
  exact RS.bind (rs_claim3 H rfl) fun _ _ h3 => RS.bind (rs_claim4 H h3) fun _ _ h4 => rs_claim5 H h4

/-- **So does "second".** -/
theorem second_len (H : Same i i') {l l' : List Aff}
    (h1 : P.Runs.secondRun i K = some l) (h2 : P.Runs.secondRun i' K = some l') :
    l.length = l'.length := by
  unfold P.Runs.secondRun at h1 h2
  simp only [Option.map_eq_some_iff] at h1 h2
  obtain ⟨x, g1, rfl⟩ := h1
  obtain ⟨x', g2, rfl⟩ := h2
  exact gather_len (R := Any)
    (RS.bind (rs_claim6 H) fun _ _ _ => RS.bind (rs_claim7 H) fun _ _ _ => rs_claim8 H) g1 g2

/-- A record agrees with itself in what is public. -/
theorem same_refl (i : In) : Same i i := by
  have w : ∀ a : Array W1, SameW a a := fun a => forall₂_same (fun _ => ⟨rfl, rfl⟩) _
  exact ⟨rfl, ⟨forall₂_same (fun c => ⟨rfl, rfl, rfl, w _, rfl⟩) _,
    forall₂_same (fun k => ⟨rfl, rfl, w _, rfl⟩) _, ⟨w _, w _, w _, rfl, rfl, rfl⟩, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The numbers of claims of "first" and "second" are numbers of the plan**: where the dry run on blank points says yes there are two numbers that the lists' lengths are at every record that agrees with the blank one in what is public. -/
theorem lens_of_dry (c : P.ParC) (K : ℕ) (k3 : P.Runs.PadIn) (planesOk : Bool) (nzx : ℕ)
    (h : P.claimsOk c K k3 planesOk nzx = true) :
    ∃ (p0 : Pts) (t0 : TablesP) (n₁ n₂ : ℕ), P.blankPts c.geo = some p0 ∧
      P.tablesP c.geo c.mats c.nW (Spec.blankLook c.geo planesOk nzx) p0 = some t0 ∧
      ∀ i : In, Same i (Spec.blankIn c p0 t0) →
        (∀ l j, P.Runs.firstRun i K = some (l, j) → l.length = n₁) ∧
        ∀ l, P.Runs.secondRun i K = some l → l.length = n₂ := by
  obtain ⟨p0, t0, hp, ht, hall⟩ := dry_gives c K k3 planesOk nzx h
  obtain ⟨l₁, j, kf, l₂, h1, -, h2⟩ := hall _ (same_refl _)
  exact ⟨p0, t0, l₁.length, l₂.length, hp, ht, fun i H =>
    ⟨fun l j' hl => first_len H hl h1, fun l hl => second_len H hl h2⟩⟩

end K5Law.Len
