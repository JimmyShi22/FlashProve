-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lay/PlanList.lean: the whole list of rounds that the planner lays for a layers'
sub-proof's own rounds, as a closed function of the sub-proof's sizes, proved of the planner's own
routine.

Params.planLayerOwn takes a record of sizes (Params.LayerRounds). Here the entries of the rounds
that it lays are written as one list, `ownList`, the concatenation of fifteen named stretches in the
routine's order: two points that are drawn; the norms' squares (a batch with scalars, a join, a
product layer); the row products (a batch with scalars, a token sumcheck); the terms (a token
sumcheck); the inner products (a batch, a sumcheck); the gated products (a product layer); the
routed experts' (a join, a product layer); the weights (a batch, a merge).

Main names:
  `eDraw`, `eBat`, `lPsc`, `lLayer`: the entries of a round in which the verifier alone speaks; of a
    batching round; the list of a sumcheck; of a product layer.
  `ptToken` ... `merge`, `ownList`: the fifteen stretches; the whole list.
  `Adds s b b' x L`: from a state with b bytes open the routine x leaves one with b' bytes open and
    adds rounds with the entries L. `adds_*`: this of the planner's routines, one by one.
  `own_adds`: Adds s 0 0 (planLayerOwn x) (ownList w x), for every setting and every record of
    sizes.
  `planLayerOwn_entries`, `own_finish`: the same read off the returned state; off a whole plan that
    finish accepts.

Limits: nothing is said on whether finish accepts, nor, here, on the rounds' errors.

-/
import OnBytes.Tie.Pv.Lay.PlanMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params

/-! ### the closed lists -/

/-- a round that draws n elements of E, none of them barred from 0, with b bytes sent -/
def eDraw (name : String) (w b n : Nat) : Fmt.Entry :=
    { name := name, work := w, msg := b, drawE := n }

/-- a batch of rows, with b bytes sent in its own round -/
def eBat (w b rows : Nat) : Fmt.Entry :=
    { name := "BAT-sigma", work := w, msg := b, drawE := 1, rows := rows }

/-- a masked sumcheck on n variables of degree 2, with b more bytes in the message that holds the
sum of the hiding polynomial (the plan does not say in which order); dy scalars in the round of the
further variable; vals end values -/
def lPsc (w b n dy vals : Nat) : List Fmt.Entry :=
  [eDraw "PSC epsilon" w (b + 24) 1] ++ List.replicate n (eDraw "PSC round" w 48 1) ++
  [{ name := "PSC Y", work := w, msg := 24 * dy, drawE := 1, drawNZ := 1 },
      { name := "PSC values", msg := 24 * vals }]

/-- a product layer on v variables: a sumcheck with two end values, then the line's point -/
def lLayer (w v : Nat) : List Fmt.Entry := lPsc w 0 v 2 2 ++ [eDraw "LINE" w 0 1]

def ptToken (w : Nat) (x : LayerRounds) : List Fmt.Entry := [eDraw "ZERO" w 0 x.lt]
def ptFirst (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  if x.firstGroup then [eDraw "ZERO" w 0 (x.ls + x.lt), eDraw "ZERO" w 0 (x.lPd - x.ls)] else []
def batLimbs (w : Nat) (x : LayerRounds) : List Fmt.Entry := [eBat w (24 * (x.NS * x.NI)) x.NS]
def joinNorms (w : Nat) (x : LayerRounds) : List Fmt.Entry := if x.lNI != 0 then [eDraw "JOIN" w 0
    x.lNI] else []
/-- the sumcheck of the sums of squares: a product layer -/
def squares (w : Nat) (x : LayerRounds) : List Fmt.Entry := lLayer w (x.lNI + x.lPd + x.lt)
/-- opens the sumcheck of the row products: the NP · NI products are sent in the batch's own
message -/
def batProducts (w : Nat) (x : LayerRounds) : List Fmt.Entry := [eBat w (24 * (x.NP * x.NI)) (x.NP
    * x.NI)]
/-- the sumcheck of the row products -/
def rowProducts (w : Nat) (x : LayerRounds) : List Fmt.Entry := lPsc w 24 x.lt 2 (x.NO * x.NI)
/-- the sumcheck of the terms -/
def terms (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  if x.withTerms then lPsc w 24 x.lt 1 x.shownByTheTerms else []
/-- the element that combines what the sumcheck of the terms leaves with the lookup's join: in the
planner's text it stands with the terms (Params/SubRounds.lean:153), in the verifier's routine it
opens the inner products' sumcheck (Model/Layer.lean:244, hearStack) -/
def batTwo (w : Nat) (x : LayerRounds) : List Fmt.Entry := if x.withTerms then [eBat w 0 2] else []
/-- the batched sumcheck of the inner products -/
def inner (w : Nat) (x : LayerRounds) : List Fmt.Entry := lPsc w 0 x.lamS 2 (2 + x.neverSent +
    x.weightClaims)
/-- the sumcheck of the gated products: a product layer -/
def gated (w : Nat) (x : LayerRounds) : List Fmt.Entry := lLayer w (x.ll + x.lPf + x.lt)
/-- opens the sumcheck of the routed experts' gated products -/
def joinRouted (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  if x.routed then (if 1 < x.ll then [eDraw "JOIN" w 0 (x.ll - 1)] else []) else []
/-- the sumcheck of the routed experts' gated products: a product layer -/
def routed (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  if x.routed then lLayer w (x.ll - 1 + x.lfe + x.lt) else []
/-- opens the merge of the weight claims: the merge's own routine draws it (Model/Merge.lean:73-75,
wsForkMerge); the first group's one scalar is read outside it (Model/Layer.lean:563) -/
def batWeights (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  [eBat w (if x.firstGroup then 24 else 0) (x.weightClaims + (if x.firstGroup then 1 else 0))]
/-- the merge of the weight claims -/
def merge (w : Nat) (x : LayerRounds) : List Fmt.Entry := lPsc w 0 x.lkW 1 1

/-- THE WHOLE LIST. -/
def ownList (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  ptToken w x ++ ptFirst w x ++ batLimbs w x ++ joinNorms w x ++ squares w x ++ batProducts w x ++
      rowProducts w x ++
    terms w x ++ batTwo w x ++ inner w x ++ gated w x ++ joinRouted w x ++ routed w x ++ batWeights
        w x ++ merge w x

/-- the closed list of OnBytes/Tie/Pv/Lay/PlanAt.lean is the opening batch and S2 -/
theorem stretch_eq (w : Nat) (x : LayerRounds) :
    stretch w x.lt x.NI x.NP x.NO = batProducts w x ++ rowProducts w x := by
  simp [stretch, batProducts, rowProducts, lPsc, eBat, eDraw]

/-! ### the calculus -/

/-- x, from b open bytes, ends well only with b' open bytes, and has added just the entries L -/
def Adds (s : Setting) (b b' : Nat) (x : Planning Unit) (L : List Fmt.Entry) : Prop :=
  ∀ p q, At s b p → x p = .ok ((), q) →
    At s b' q ∧ ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧ l.map shapeOf = L

theorem Adds.bind {s : Setting} {b b' b'' : Nat} {x y : Planning Unit} {L L' : List Fmt.Entry}
    (hx : Adds s b b' x L) (hy : Adds s b' b'' y L') : Adds s b b'' (x >>= fun _ => y) (L ++ L') :=
  fun p q hp h => by
    obtain ⟨_, r, h1, h2⟩ := bind_ok h
    obtain ⟨a1, l1, e1, c1⟩ := hx p r hp h1
    obtain ⟨a2, l2, e2, c2⟩ := hy r q a1 h2
    exact ⟨a2, l1 ++ l2, by rw [e2, e1]; simp, by rw [List.map_append, c1, c2]⟩

theorem Adds.pure (s : Setting) (b : Nat) : Adds s b b (pure ()) [] := fun p q hp h => by
  obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨hp, [], by simp, rfl⟩

theorem Adds.ite {s : Setting} {b b' : Nat} {c : Prop} [Decidable c] {x y : Planning Unit}
    {L L' : List Fmt.Entry}
    (hx : Adds s b b' x L) (hy : Adds s b b' y L') :
    Adds s b b' (if c then x else y) (if c then L else L') := by
  split
  · exact hx
  · exact hy

theorem Adds.cast {s : Setting} {b b' c c' : Nat} {x : Planning Unit} {L L' : List Fmt.Entry}
    (h : Adds s b b' x L) (e1 : b = c) (e2 : b' = c') (e3 : L = L') : Adds s c c' x L' := by
  subst e1 e2 e3
  exact h

theorem adds_scalars (s : Setting) (b n : Nat) : Adds s b (b + 24 * n) (planScalars n) [] := fun p
    q hp h => by
  obtain ⟨m, e, a, r⟩ := scalars_at hp n
  rw [e] at h
  obtain rfl : m = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨a, [], by rw [r]; simp, rfl⟩

/-- a routine that reads the setting and closes a round of the field's kind -/
theorem adds_close (s : Setting) (b : Nat) (name : String) (e : Setting → Bound) (d : Draws) :
    Adds s b 0 (theSetting >>= fun s' => close name .field (e s') d)
      [entryOf name (s.workOf .field .request) b d] := fun p q hp h => by
  obtain ⟨s2, m2, g2, h2⟩ := bind_ok h
  obtain ⟨rfl, rfl⟩ : p.set = s2 ∧ p = m2 := Prod.mk.inj (Except.ok.inj g2)
  obtain ⟨a2, r, er, sr⟩ := close_at hp _ _ _ h2
  exact ⟨a2, [r], by rw [er]; simp, by rw [List.map_cons, sr]; rfl⟩

theorem adds_zero (s : Setting) (v : Nat) : Adds s 0 0 (planZero v) [eDraw "ZERO" (s.workOf .field
    .request) 0 v] :=
  adds_close s 0 "ZERO" (fun s' => fieldError s' v) { drawE := v, priced := .roundItself }

theorem adds_join (s : Setting) (v : Nat) : Adds s 0 0 (planJoin v) [eDraw "JOIN" (s.workOf .field
    .request) 0 v] :=
  adds_close s 0 "JOIN" (fun s' => fieldError s' v) { drawE := v, priced := .roundItself }

theorem adds_line (s : Setting) : Adds s 0 0 planLine [eDraw "LINE" (s.workOf .field .request) 0 1]
    :=
  adds_close s 0 "LINE" (fun s' => fieldError s' 1) { drawE := 1, priced := .settingAlone }

theorem adds_bat (s : Setting) (b rows : Nat) :
    Adds s b 0 (planBatSigma rows) [eBat (s.workOf .field .request) b rows] :=
  adds_close s b "BAT-sigma" (fun s' => powersError s' rows)
      { drawE := 1, rows := rows, priced := .asSaid }

/-- THE MASKED SUMCHECK, with b bytes already open -/
theorem adds_psc (s : Setting) (b n dy vals : Nat) :
    Adds s b 0 (planPsc { degree := List.replicate n 3, degreeY := dy, values := vals })
      (lPsc (s.workOf .field .request) b n dy vals) := fun p q hp h => by
  have h' : (theSetting >>= fun s' =>
      planScalars 1 >>= fun _ =>
      close "PSC epsilon" .field (fieldError s' 1) { drawE := 1, priced := .settingAlone } >>= fun
          _ =>
      planPscRounds s' (List.replicate n 3) >>= fun _ =>
      planScalars dy >>= fun _ =>
      close "PSC Y" .field (fieldErrorNonzero s' dy)
          { drawE := 1, drawNZ := 1, priced := .roundItself } >>= fun _ =>
      planScalars vals >>= fun _ =>
      closeNone "PSC values") p = .ok ((), q) := h
  obtain ⟨s4, m4, g4, k4⟩ := bind_ok h'
  obtain ⟨rfl, rfl⟩ : p.set = s4 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  obtain ⟨_, m5, h5, k5⟩ := bind_ok k4
  obtain ⟨n5, e5, a5, r5⟩ := scalars_at hp 1
  rw [e5] at h5
  obtain rfl : n5 = m5 := (Prod.mk.inj (Except.ok.inj h5)).2
  obtain ⟨_, m6, h6, k6⟩ := bind_ok k5
  obtain ⟨a6, x6, er6, sh6⟩ := close_at a5 _ _ _ h6
  obtain ⟨_, m7, h7, k7⟩ := bind_ok k6
  rw [hp.set] at h7
  obtain ⟨a7, l7, el7, sl7⟩ := rounds_at n a6 h7
  obtain ⟨_, m8, h8, k8⟩ := bind_ok k7
  obtain ⟨n8, e8, a8, r8⟩ := scalars_at a7 dy
  rw [e8] at h8
  obtain rfl : n8 = m8 := (Prod.mk.inj (Except.ok.inj h8)).2
  obtain ⟨_, m9, h9, k9⟩ := bind_ok k8
  obtain ⟨a9, x9, er9, sh9⟩ := close_at a8 _ _ _ h9
  obtain ⟨_, m10, h10, k10⟩ := bind_ok k9
  obtain ⟨n10, e10, a10, r10⟩ := scalars_at a9 vals
  rw [e10] at h10
  obtain rfl : n10 = m10 := (Prod.mk.inj (Except.ok.inj h10)).2
  obtain ⟨a11, x11, er11, sh11⟩ := none_at a10 _ k10
  refine ⟨a11, [x6] ++ l7 ++ [x9, x11], ?_, ?_⟩
  · rw [er11, r10, er9, r8, el7, er6, r5]
    simp
  · simp only [List.map_append, List.map_cons, List.map_nil, sl7, sh6, sh9, sh11, lPsc, eDraw,
      entryOf]
    simp

theorem adds_layer (s : Setting) (v : Nat) :
    Adds s 0 0 (planProductLayer v) (lLayer (s.workOf .field .request) v) :=
  Adds.bind (adds_psc s 0 v 2 2) (adds_line s)

theorem adds_token (s : Setting) (lt dy shown : Nat) :
    Adds s 0 0 (planTokenSumcheck lt dy shown) (lPsc (s.workOf .field .request) 24 lt dy shown) :=
  (Adds.bind (adds_scalars s 0 1) (adds_psc s (0 + 24 * 1) lt dy shown)).cast rfl rfl (by simp)

/-! ### planLayerOwn -/

theorem adds_after (s : Setting) (x : LayerRounds) : Adds s 0 0 (afterOwn x)
    (terms (s.workOf .field .request) x ++ batTwo (s.workOf .field .request) x ++ inner (s.workOf
        .field .request) x ++
      gated (s.workOf .field .request) x ++ joinRouted (s.workOf .field .request) x ++
      routed (s.workOf .field .request) x ++ batWeights (s.workOf .field .request) x ++ merge
          (s.workOf .field .request) x) := by
  rw [after_eq]
  have hT : Adds s 0 0 (if x.withTerms then (planTokenSumcheck x.lt 1 x.shownByTheTerms >>= fun _
      => planBatSigma 2) else pure ())
      (terms (s.workOf .field .request) x ++ batTwo (s.workOf .field .request) x) :=
    (Adds.ite (Adds.bind (adds_token s x.lt 1 x.shownByTheTerms) (adds_bat s 0 2)) (Adds.pure s
        0)).cast rfl rfl (by
      unfold terms batTwo
      split <;> simp)
  have hR : Adds s 0 0 (if x.routed then ((if 1 < x.ll then planJoin (x.ll - 1) else pure ()) >>=
      fun _ =>
        planProductLayer (x.ll - 1 + x.lfe + x.lt)) else pure ())
      (joinRouted (s.workOf .field .request) x ++ routed (s.workOf .field .request) x) :=
    (Adds.ite (Adds.bind (Adds.ite (adds_join s (x.ll - 1)) (Adds.pure s 0)) (adds_layer s _))
        (Adds.pure s 0)).cast rfl rfl (by
      unfold joinRouted routed
      split <;> simp)
  have hW : Adds s 0 0 ((if x.firstGroup then planScalars 1 else pure ()) >>= fun _ =>
        planBatSigma (x.weightClaims + (if x.firstGroup then 1 else 0))) (batWeights (s.workOf
            .field .request) x) := by
    unfold batWeights
    by_cases hf : x.firstGroup = true
    · simp only [hf, if_true]
      exact (Adds.bind (adds_scalars s 0 1) (adds_bat s (0 + 24 * 1) _)).cast rfl rfl (by simp)
    · simp only [hf, if_false, Bool.false_eq_true]
      exact (Adds.bind (Adds.pure s 0) (adds_bat s 0 _)).cast rfl rfl (by simp)
  have h := Adds.bind hT (Adds.bind (adds_psc s 0 x.lamS 2 (2 + x.neverSent + x.weightClaims))
    (Adds.bind (adds_layer s (x.ll + x.lPf + x.lt)) (Adds.bind hR (Adds.bind hW (adds_psc s 0 x.lkW
        1 1)))))
  intro p q hp hq
  refine (h.cast rfl rfl ?_) p q hp ?_
  · simp only [inner, gated, merge, List.append_assoc]
  · simpa only [bind_assoc] using hq

/-- The planner's own planLayerOwn adds just ownList. -/
theorem own_adds (s : Setting) (x : LayerRounds) :
    Adds s 0 0 (planLayerOwn x) (ownList (s.workOf .field .request) x) := by
  rw [own_eq]
  have hF : Adds s 0 0 (if x.firstGroup then (planZero (x.ls + x.lt) >>= fun _ => planZero (x.lPd -
      x.ls)) else pure ())
      (ptFirst (s.workOf .field .request) x) :=
    Adds.ite (Adds.bind (adds_zero s _) (adds_zero s _)) (Adds.pure s 0)
  have hJ : Adds s 0 0 (if x.lNI != 0 then planJoin x.lNI else pure ()) (joinNorms (s.workOf .field
      .request) x) :=
    Adds.ite (adds_join s x.lNI) (Adds.pure s 0)
  have hL : Adds s 0 0 (planScalars (x.NS * x.NI) >>= fun _ => planBatSigma x.NS) (batLimbs
      (s.workOf .field .request) x) :=
    (Adds.bind (adds_scalars s 0 (x.NS * x.NI)) (adds_bat s (0 + 24 * (x.NS * x.NI)) x.NS)).cast
        rfl rfl (by simp [batLimbs])
  have hS : Adds s 0 0 (rowProductsL x.lt x.NI x.NP x.NO)
      (batProducts (s.workOf .field .request) x ++ rowProducts (s.workOf .field .request) x) :=
    fun p q hp hq => stretch_eq (s.workOf .field .request) x ▸ rowProducts_at x.lt x.NI x.NP x.NO
        hp hq
  have h := Adds.bind (adds_zero s x.lt) (Adds.bind hF (Adds.bind hL (Adds.bind hJ
    (Adds.bind (adds_layer s (x.lNI + x.lPd + x.lt)) (Adds.bind hS (adds_after s x))))))
  intro p q hp hq
  refine (h.cast rfl rfl ?_) p q hp ?_
  · simp only [ownList, ptToken, squares, List.append_assoc]
  · simpa only [rowProductsL, bind_assoc] using hq

/-- written out -/
theorem planLayerOwn_entries (s : Setting) (x : LayerRounds) (p q : PlanState) (hp : At s 0 p)
    (h : planLayerOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      l.map (·.entry) = ownList (s.workOf .field .request) x :=
  (own_adds s x p q hp h).2

/-- of the planner's finish -/
theorem own_finish (s : Setting) (x : LayerRounds) (P : Planned)
    (h : finish s .request (planLayerOwn x) = .ok P) :
    P.set = s ∧ P.rounds.map (·.entry) = ownList (s.workOf .field .request) x := by
  unfold finish at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      obtain ⟨_, l, el, sl⟩ := own_adds s x { set := s, scope := .request } q ⟨rfl, rfl, rfl, rfl,
          rfl⟩ hq
      refine ⟨rfl, ?_⟩
      show q.rounds.toList.map (·.entry) = _
      rw [el, ← sl]
      simp [shapeOf]

theorem lPsc_length (w b n dy vals : Nat) : (lPsc w b n dy vals).length = n + 3 := by simp [lPsc]
theorem lLayer_length (w v : Nat) : (lLayer w v).length = v + 4 := by simp [lLayer, lPsc]

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.stretch_eq
#print axioms OnBytes.Tie.Pv.Lay.lPsc_length
#print axioms OnBytes.Tie.Pv.Lay.lLayer_length
#print axioms OnBytes.Tie.Pv.Lay.own_adds
#print axioms OnBytes.Tie.Pv.Lay.planLayerOwn_entries
#print axioms OnBytes.Tie.Pv.Lay.own_finish
