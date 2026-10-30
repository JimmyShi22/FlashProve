-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/OwnPlan.lean: the own rounds of a layers' sub-proof as one chain
(Cb/Pv/Lay/Own.lean) against the planner's list of the same rounds: the rounds' shapes and the
errors.

The planner's routine `planLayerOwn x` adds the rounds with the entries `ownList w x`
(OnBytes/Tie/Pv/Lay/PlanList.lean) and the bounds `ownBounds s x`, which are the pairs `ownRatios
s.cardE x` (PlanBounds.lean, Errs.lean). The chain has letters for its numbers. Where these are
the numbers of the record x, the chain's rounds are an instance of the whole list, and its list of
errors is made of the numerators of the plan's pairs or, at the draw of a point, of the count with
the same quotient.

Main names:
  `StgIs S n k dy vals`: the numbers of one sumcheck. `TailIs T x`: the numbers of all stages from
    the limbs' scalars on are those of x. `Full x`: the record has terms, routed experts and both
    joins.
  `fit_stg`, `fit_one`, `fit_pt`, `fit_sent`, `tail_fit`: the entries fit the chain, stage by
    stage (`Fit`, OnBytes/Tie/Pv/Att/ChainShape.lean).
  `ownList_later`, `ownList_first`: the planner's list, written out, for a sub-proof that is not
    the first and for the first.
  `own_shape`, `ownFirst_shape`: the shape of the chain's reduction is an instance of `ownList w
    x` (`ShapeIs`, OnBytes/G4/RoundIs.lean): round by round the number of scalars sent, of
    elements drawn, and of these how many are never 0.
  `own_planned`, `ownFirst_planned`: so whenever `planLayerOwn x` ends well from a state `At s 0`,
    the chain's rounds are an instance of the entries of the rounds that it has added.
  `CountIs q e o`: a number e of bad draws against a pair o of the plan: e is the numerator; or,
    where a point is drawn at once, e * q = g * q ^ g for the numerator g: the same quotient.
    `TailErrs T x q`: the chain's bounds on the bad draws are the plan's.
  `tailCounts q x`, `own_errs`, `ownFirst_errs`: the chain's list of errors, written out, one by
    one: at the draw of a point of g coordinates g * q ^ (g - 1), at every other round the plan's
    numerator.
  `own_counts`, `ownFirst_counts`: that list meets `ownRatios c x`, round by round (`CountIs`).

Limits: `ShapeIs` counts: it does not compare names, kinds, work or rows, nor does it say which
scalar of a message is which or in which order they stand; at a draw that never gives 0 any set of
|E| - 1 elements passes. `TailIs` and `TailErrs` are conditions on the letters: no value is built
here. At the rounds outside the sumchecks, but for the three last draws (whose bound 1 is fixed in
the chain), the chain's bounds are letters, so there `own_errs` says what its premises
(`TailErrs`, and the like for the points) say; at the sumchecks' rounds the numbers come from the
records. Numerators alone are compared: c is a free letter. The pairs are the bounds before the
planner multiplies them by the number of instances. `CountIs` alone does not say which of its two
cases holds at which round: `own_errs` does. That q is the number of elements of E is not shown.
Records without terms, without routed experts or without a join are not covered. Nothing is said
on the rounding of the planner's quotients.
-/
import OnBytes.Tie.Pv.Att.ChainShape
import OnBytes.Tie.Pv.Lay.Errs
import Cb.Pv.Lay.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params OnBytes.G4 Iop Cb Cb.Pv.Att Cb.Pv.Lay TWhole
open OnBytes.Tie.Pv.Att (Fit pscEntries)

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-! ### The steps -/

theorem lPsc_entries (w n k dy vals : Nat) :
    lPsc w (24 * n) k dy vals = pscEntries w n (List.replicate k 2) dy vals := by
  simp [lPsc, pscEntries, eDraw]

/-- The numbers of one sumcheck: further scalars, variables (each of degree 2), the degree in the
further variable, end values. -/
structure StgIs {X : Type} (S : Stg E M X) (n k dy vals : Nat) : Prop where
  hn : S.n = n
  hk : S.L.S.k = k
  hd : ∀ i, S.L.M.n i = 2
  hy : S.L.M.DY = dy
  hv : Fintype.card S.L.S.A = vals

theorem StgIs.degs {X : Type} {S : Stg E M X} {n k dy vals : Nat} (h : StgIs S n k dy vals) :
    List.ofFn S.L.M.n = List.replicate k 2 := by
  rw [show S.L.M.n = fun _ => 2 from funext h.hd, List.ofFn_const, h.hk]

theorem fit_stg {X : Type} (S : Stg E M X) {n k dy vals : Nat} (hS : StgIs S n k dy vals) (w : Nat)
    (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (S.stage Ow next) (lPsc w (24 * n) k dy vals ++ ds) :=
  ⟨w, S.L.S.k, S.L.M.n, S.L.M.DY, ds, rfl, by
    rw [lPsc_entries, hS.degs, hS.hn, hS.hy]
    exact congrArg (fun v => pscEntries w n (List.replicate k 2) dy v ++ ds) hS.hv.symm, h⟩

theorem fit_one {X : Type} (e : Fmt.Entry) (h1 : e.drawE = 1) (h0 : e.msg = 0) (hz : e.drawNZ = 0)
    (err : Nat) (P : X → M → Prop) (next : Ch E M (X × E)) (ds : List Fmt.Entry)
    (h : Fit next ds) : Fit (Ch.draw (dE E) err P next) (e :: ds) :=
  ⟨e, ds, ⟨by rw [h1]; exact (Equiv.funUnique (Fin 1) E).symm⟩, h0, hz, rfl, h⟩

theorem fit_pt {X : Type} (name : String) (w g v : Nat) (hg : g = v) (err : Nat)
    (P : X → M → Prop) (next : Ch E M (X × (Fin g → E))) (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (Ch.draw (dPt E g) err P next) (eDraw name w 0 v :: ds) :=
  ⟨eDraw name w 0 v, ds, ⟨by subst hg; exact Equiv.refl _⟩, rfl, rfl, rfl, h⟩

theorem fit_sent {X : Type} (w b n rows : Nat) (hb : b = 24 * n) (err : Nat) (P : X → M → Prop)
    (L : X → (Fin n → E) → M → Prop) (next : Ch E M ((X × (Fin n → E)) × E))
    (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (Ch.send n (dE E) err P L next) (eBat w b rows :: ds) :=
  ⟨eBat w b rows, ds, ⟨(Equiv.funUnique (Fin 1) E).symm⟩, hb, rfl, rfl, h⟩

/-! ### The stages behind the first points -/

/-- The numbers of the stages are those of a record of the planner. -/
structure TailIs {X : Type} (T : LayTail E M X) (x : LayerRounds) : Prop where
  nL : T.nL = x.NS * x.NI
  gN : T.gN = x.lNI
  s1 : StgIs T.s1 0 (x.lNI + x.lPd + x.lt) 2 2
  nP : T.nP = x.NP * x.NI
  s2 : StgIs T.s2 1 x.lt 2 (x.NO * x.NI)
  s3 : StgIs T.s3 1 x.lt 1 x.shownByTheTerms
  s4 : StgIs T.s4 0 x.lamS 2 (2 + x.neverSent + x.weightClaims)
  s5 : StgIs T.s5 0 (x.ll + x.lPf + x.lt) 2 2
  gR : T.gR = x.ll - 1
  s6 : StgIs T.s6 0 (x.ll - 1 + x.lfe + x.lt) 2 2
  nW : T.nW = if x.firstGroup then 1 else 0
  s7 : StgIs T.s7 0 x.lkW 1 1

/-- The entries of these stages, in the order of the chain. -/
def tailList (w : Nat) (x : LayerRounds) : List Fmt.Entry :=
  eBat w (24 * (x.NS * x.NI)) x.NS :: eDraw "JOIN" w 0 x.lNI ::
    (lPsc w (24 * 0) (x.lNI + x.lPd + x.lt) 2 2 ++ (eDraw "LINE" w 0 1 ::
      eBat w (24 * (x.NP * x.NI)) (x.NP * x.NI) ::
        (lPsc w (24 * 1) x.lt 2 (x.NO * x.NI) ++ (lPsc w (24 * 1) x.lt 1 x.shownByTheTerms ++
          (eBat w 0 2 :: (lPsc w (24 * 0) x.lamS 2 (2 + x.neverSent + x.weightClaims) ++
            (lPsc w (24 * 0) (x.ll + x.lPf + x.lt) 2 2 ++ (eDraw "LINE" w 0 1 ::
              eDraw "JOIN" w 0 (x.ll - 1) ::
                (lPsc w (24 * 0) (x.ll - 1 + x.lfe + x.lt) 2 2 ++ (eDraw "LINE" w 0 1 ::
                  eBat w (if x.firstGroup then 24 else 0)
                    (x.weightClaims + (if x.firstGroup then 1 else 0)) ::
                    (lPsc w (24 * 0) x.lkW 1 1 ++ [])))))))))))

theorem tail_fit {X : Type} (T : LayTail E M X) (x : LayerRounds) (h : TailIs T x) (w : Nat) :
    Fit T.ch (tailList w x) :=
  fit_sent w _ _ _ (by rw [h.nL]) _ _ _ _ _ <|
  fit_pt "JOIN" w _ _ h.gN _ _ _ _ <|
  fit_stg T.s1 h.s1 w _ _ _ <|
  fit_one _ rfl rfl rfl _ _ _ _ <|
  fit_sent w _ _ _ (by rw [h.nP]) _ _ _ _ _ <|
  fit_stg T.s2 h.s2 w _ _ _ <|
  fit_stg T.s3 h.s3 w _ _ _ <|
  fit_one _ rfl rfl rfl _ _ _ _ <|
  fit_stg T.s4 h.s4 w _ _ _ <|
  fit_stg T.s5 h.s5 w _ _ _ <|
  fit_one _ rfl rfl rfl _ _ _ _ <|
  fit_pt "JOIN" w _ _ h.gR _ _ _ _ <|
  fit_stg T.s6 h.s6 w _ _ _ <|
  fit_one _ rfl rfl rfl _ _ _ _ <|
  fit_sent w _ _ _ (by rw [h.nW]; split <;> rfl) _ _ _ _ _ <|
  fit_stg T.s7 h.s7 w _ _ _ rfl

/-- The record has terms, routed experts and both joins. -/
structure Full (x : LayerRounds) : Prop where
  terms : x.withTerms = true
  routed : x.routed = true
  norms : (x.lNI != 0) = true
  layers : 1 < x.ll

theorem ownList_later (w : Nat) (x : LayerRounds) (hx : Full x) (hf : x.firstGroup = false) :
    ownList w x = eDraw "ZERO" w 0 x.lt :: tailList w x := by
  simp [ownList, tailList, ptToken, ptFirst, batLimbs, joinNorms, squares, batProducts,
    rowProducts, terms, batTwo, inner, gated, joinRouted, routed, batWeights, merge, lLayer,
    hx.terms, hx.routed, hx.norms, hx.layers, hf]

theorem ownList_first (w : Nat) (x : LayerRounds) (hx : Full x) (hf : x.firstGroup = true) :
    ownList w x = eDraw "ZERO" w 0 x.lt :: eDraw "ZERO" w 0 (x.ls + x.lt) ::
      eDraw "ZERO" w 0 (x.lPd - x.ls) :: tailList w x := by
  simp [ownList, tailList, ptToken, ptFirst, batLimbs, joinNorms, squares, batProducts,
    rowProducts, terms, batTwo, inner, gated, joinRouted, routed, batWeights, merge, lLayer,
    hx.terms, hx.routed, hx.norms, hx.layers, hf]

/-! ### The whole -/

/-- The rounds of the chain are an instance of the planner's list. -/
theorem own_shape {X : Type} (A : LayOwn E M X) (x : LayerRounds) (hx : Full x)
    (hf : x.firstGroup = false) (hT : A.gT = x.lt) (h : TailIs A.tail x) (w : Nat) (Ex : ExtSpec) :
    ShapeIs E (A.ch.R Ex).shape (ownList w x) := by
  rw [ownList_later w x hx hf]
  exact OnBytes.Tie.Pv.Att.Ch.shapeIs_R Ex A.ch _
    (fit_pt "ZERO" w _ _ hT _ _ _ _ (tail_fit A.tail x h w))

theorem ownFirst_shape {X : Type} (A : LayOwnFirst E M X) (x : LayerRounds) (hx : Full x)
    (hf : x.firstGroup = true) (hT : A.gT = x.lt) (hA : A.gA = x.ls + x.lt)
    (hB : A.gB = x.lPd - x.ls) (h : TailIs A.tail x) (w : Nat) (Ex : ExtSpec) :
    ShapeIs E (A.ch.R Ex).shape (ownList w x) := by
  rw [ownList_first w x hx hf]
  exact OnBytes.Tie.Pv.Att.Ch.shapeIs_R Ex A.ch _
    (fit_pt "ZERO" w _ _ hT _ _ _ _ (fit_pt "ZERO" w _ _ hA _ _ _ _
      (fit_pt "ZERO" w _ _ hB _ _ _ _ (tail_fit A.tail x h w))))

/-- So whenever the planner's routine for the own rounds ends well, the chain's rounds are an
instance of the entries of the rounds that it has added. -/
theorem own_planned {X : Type} (A : LayOwn E M X) (x : LayerRounds) (hx : Full x)
    (hf : x.firstGroup = false) (hT : A.gT = x.lt) (h : TailIs A.tail x) (Ex : ExtSpec)
    (s : Setting) (p q : PlanState) (hp : At s 0 p) (hq : planLayerOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (A.ch.R Ex).shape (l.map (·.entry)) := by
  obtain ⟨l, h1, h2⟩ := planLayerOwn_entries s x p q hp hq
  exact ⟨l, h1, by rw [h2]; exact own_shape A x hx hf hT h _ Ex⟩

theorem ownFirst_planned {X : Type} (A : LayOwnFirst E M X) (x : LayerRounds) (hx : Full x)
    (hf : x.firstGroup = true) (hT : A.gT = x.lt) (hA : A.gA = x.ls + x.lt)
    (hB : A.gB = x.lPd - x.ls) (h : TailIs A.tail x) (Ex : ExtSpec)
    (s : Setting) (p q : PlanState) (hp : At s 0 p) (hq : planLayerOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (A.ch.R Ex).shape (l.map (·.entry)) := by
  obtain ⟨l, h1, h2⟩ := planLayerOwn_entries s x p q hp hq
  exact ⟨l, h1, by rw [h2]; exact ownFirst_shape A x hx hf hT hA hB h _ Ex⟩

/-! ### The errors -/

/-- A number of bad draws against a pair of the plan: it is the numerator; or, where a point of as
many coordinates as the numerator says is drawn at once, the count with the same quotient. -/
def CountIs (q e : Nat) (o : Option (Nat × Nat)) : Prop :=
  e = (o.map (·.1)).getD 0 ∨ e * q = (o.map (·.1)).getD 0 * q ^ (o.map (·.1)).getD 0

theorem countIs_nums (q : Nat) : ∀ l : List (Option (Nat × Nat)),
    List.Forall₂ (CountIs q) (numsOf l) l
  | [] => List.Forall₂.nil
  | _ :: l => List.Forall₂.cons (Or.inl rfl) (countIs_nums q l)

theorem countIs_one (q n c : Nat) : List.Forall₂ (CountIs q) [n] [some (n, c)] :=
  List.Forall₂.cons (Or.inl rfl) List.Forall₂.nil

theorem countIs_pt (q g c : Nat) : List.Forall₂ (CountIs q) [g * q ^ (g - 1)] [some (g, c)] :=
  List.Forall₂.cons (Or.inr (by
    show g * q ^ (g - 1) * q = g * q ^ g
    rcases g with _ | k
    · simp
    · simp [pow_succ, Nat.mul_assoc])) List.Forall₂.nil

theorem StgIs.nums {X : Type} {S : Stg E M X} {n k dy vals : Nat} (h : StgIs S n k dy vals)
    (c : Nat) : S.nums = numsOf (qPsc c k dy) := by
  rw [nums_psc, Stg.nums, h.degs, h.hy]
  simp

/-- The bounds on the bad draws are the plan's. q: the number of elements of the field. -/
structure TailErrs {X : Type} (T : LayTail E M X) (x : LayerRounds) (q : Nat) : Prop where
  eL : T.eL = x.NS - 1
  eN : T.eN = x.lNI * q ^ (x.lNI - 1)
  eP : T.eP = x.NP * x.NI - 1
  n4 : T.n4 = 2
  eR : T.eR = (x.ll - 1) * q ^ (x.ll - 1 - 1)
  eW : T.eW = x.weightClaims + (if x.firstGroup then 1 else 0) - 1

/-- The pairs of these stages, in the order of the chain. -/
def tailRatios (c : Nat) (x : LayerRounds) : List (Option (Nat × Nat)) :=
  [some (x.NS - 1, c)] ++ ([some (x.lNI, c)] ++ (qPsc c (x.lNI + x.lPd + x.lt) 2 ++
    ([some (1, c)] ++ ([some (x.NP * x.NI - 1, c)] ++ (qPsc c x.lt 2 ++ (qPsc c x.lt 1 ++
      ([some (2 - 1, c)] ++ (qPsc c x.lamS 2 ++ (qPsc c (x.ll + x.lPf + x.lt) 2 ++
        ([some (1, c)] ++ ([some (x.ll - 1, c)] ++ (qPsc c (x.ll - 1 + x.lfe + x.lt) 2 ++
          ([some (1, c)] ++ ([some (x.weightClaims + (if x.firstGroup then 1 else 0) - 1, c)] ++
            (qPsc c x.lkW 1 ++ [])))))))))))))))

/-- The numbers of bad draws of these stages, written out: at a join a count among the points, at
every other round the plan's numerator. -/
def tailCounts (q : Nat) (x : LayerRounds) : List Nat :=
  [x.NS - 1] ++ ([x.lNI * q ^ (x.lNI - 1)] ++ (numsOf (qPsc 0 (x.lNI + x.lPd + x.lt) 2) ++
    ([1] ++ ([x.NP * x.NI - 1] ++ (numsOf (qPsc 0 x.lt 2) ++ (numsOf (qPsc 0 x.lt 1) ++
      ([2 - 1] ++ (numsOf (qPsc 0 x.lamS 2) ++ (numsOf (qPsc 0 (x.ll + x.lPf + x.lt) 2) ++
        ([1] ++ ([(x.ll - 1) * q ^ (x.ll - 1 - 1)] ++
          (numsOf (qPsc 0 (x.ll - 1 + x.lfe + x.lt) 2) ++ ([1] ++
            ([x.weightClaims + (if x.firstGroup then 1 else 0) - 1] ++
              (numsOf (qPsc 0 x.lkW 1) ++ [])))))))))))))))

/-- The chain's numbers are these, one by one. -/
theorem tail_nums {X : Type} (T : LayTail E M X) (x : LayerRounds) (h : TailIs T x) (q : Nat)
    (he : TailErrs T x q) : T.nums = tailCounts q x := by
  unfold LayTail.nums tailCounts
  rw [he.eL, he.eN, he.eP, he.n4, he.eR, he.eW, h.s1.nums 0, h.s2.nums 0, h.s3.nums 0,
    h.s4.nums 0, h.s5.nums 0, h.s6.nums 0, h.s7.nums 0]

theorem nums_free (c n dy : Nat) : numsOf (qPsc 0 n dy) = numsOf (qPsc c n dy) := by
  rw [nums_psc, nums_psc]

theorem tail_counts (x : LayerRounds) (q c : Nat) :
    List.Forall₂ (CountIs q) (tailCounts q x) (tailRatios c x) := by
  unfold tailCounts tailRatios
  simp only [nums_free c]
  exact List.rel_append (countIs_one q _ c) <| List.rel_append (countIs_pt q _ c) <|
    List.rel_append (countIs_nums q _) <| List.rel_append (countIs_one q _ c) <|
    List.rel_append (countIs_one q _ c) <| List.rel_append (countIs_nums q _) <|
    List.rel_append (countIs_nums q _) <| List.rel_append (countIs_one q _ c) <|
    List.rel_append (countIs_nums q _) <| List.rel_append (countIs_nums q _) <|
    List.rel_append (countIs_one q _ c) <| List.rel_append (countIs_pt q _ c) <|
    List.rel_append (countIs_nums q _) <| List.rel_append (countIs_one q _ c) <|
    List.rel_append (countIs_one q _ c) <| List.rel_append (countIs_nums q _) List.Forall₂.nil

theorem ownRatios_later (c : Nat) (x : LayerRounds) (hx : Full x) (hf : x.firstGroup = false) :
    ownRatios c x = some (x.lt, c) :: tailRatios c x := by
  simp [ownRatios, tailRatios, qLayer, hx.terms, hx.routed, hx.norms, hx.layers, hf]

theorem ownRatios_first (c : Nat) (x : LayerRounds) (hx : Full x) (hf : x.firstGroup = true) :
    ownRatios c x = some (x.lt, c) :: some (x.ls + x.lt, c) :: some (x.lPd - x.ls, c) ::
      tailRatios c x := by
  simp [ownRatios, tailRatios, qLayer, hx.terms, hx.routed, hx.norms, hx.layers, hf]

/-- The chain's errors, written out. -/
theorem own_errs {X : Type} (A : LayOwn E M X) (x : LayerRounds) (h : TailIs A.tail x) (q : Nat)
    (hT : A.eT = x.lt * q ^ (x.lt - 1)) (he : TailErrs A.tail x q) (Ex : ExtSpec) :
    TWhole.errList (A.ch.eps Ex) = [x.lt * q ^ (x.lt - 1)] ++ tailCounts q x := by
  rw [A.errs Ex, hT, tail_nums A.tail x h q he]
  rfl

theorem ownFirst_errs {X : Type} (A : LayOwnFirst E M X) (x : LayerRounds) (h : TailIs A.tail x)
    (q : Nat) (hT : A.eT = x.lt * q ^ (x.lt - 1))
    (hA : A.eA = (x.ls + x.lt) * q ^ (x.ls + x.lt - 1))
    (hB : A.eB = (x.lPd - x.ls) * q ^ (x.lPd - x.ls - 1)) (he : TailErrs A.tail x q)
    (Ex : ExtSpec) :
    TWhole.errList (A.ch.eps Ex) = [x.lt * q ^ (x.lt - 1)] ++
      ([(x.ls + x.lt) * q ^ (x.ls + x.lt - 1)] ++
        ([(x.lPd - x.ls) * q ^ (x.lPd - x.ls - 1)] ++ tailCounts q x)) := by
  rw [A.errs Ex, hT, hA, hB, tail_nums A.tail x h q he]
  rfl

/-- The chain's errors, round by round, against the plan's pairs. -/
theorem own_counts {X : Type} (A : LayOwn E M X) (x : LayerRounds) (hx : Full x)
    (hf : x.firstGroup = false) (h : TailIs A.tail x) (q : Nat)
    (hT : A.eT = x.lt * q ^ (x.lt - 1)) (he : TailErrs A.tail x q) (c : Nat) (Ex : ExtSpec) :
    List.Forall₂ (CountIs q) (TWhole.errList (A.ch.eps Ex)) (ownRatios c x) := by
  rw [own_errs A x h q hT he Ex, ownRatios_later c x hx hf]
  exact List.rel_append (countIs_pt q _ c) (tail_counts x q c)

theorem ownFirst_counts {X : Type} (A : LayOwnFirst E M X) (x : LayerRounds) (hx : Full x)
    (hf : x.firstGroup = true) (h : TailIs A.tail x) (q : Nat)
    (hT : A.eT = x.lt * q ^ (x.lt - 1)) (hA : A.eA = (x.ls + x.lt) * q ^ (x.ls + x.lt - 1))
    (hB : A.eB = (x.lPd - x.ls) * q ^ (x.lPd - x.ls - 1)) (he : TailErrs A.tail x q) (c : Nat)
    (Ex : ExtSpec) :
    List.Forall₂ (CountIs q) (TWhole.errList (A.ch.eps Ex)) (ownRatios c x) := by
  rw [ownFirst_errs A x h q hT hA hB he Ex, ownRatios_first c x hx hf]
  exact List.rel_append (countIs_pt q _ c) <| List.rel_append (countIs_pt q _ c) <|
    List.rel_append (countIs_pt q _ c) (tail_counts x q c)

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.own_errs
#print axioms OnBytes.Tie.Pv.Lay.ownFirst_errs
#print axioms OnBytes.Tie.Pv.Lay.own_counts
#print axioms OnBytes.Tie.Pv.Lay.ownFirst_counts
#print axioms OnBytes.Tie.Pv.Lay.tail_fit
#print axioms OnBytes.Tie.Pv.Lay.own_shape
#print axioms OnBytes.Tie.Pv.Lay.ownFirst_shape
#print axioms OnBytes.Tie.Pv.Lay.own_planned
#print axioms OnBytes.Tie.Pv.Lay.ownFirst_planned
