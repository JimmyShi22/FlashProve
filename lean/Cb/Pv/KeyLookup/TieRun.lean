-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/TieRun.lean: what the verifier of the lookup's head (the first draw and the tie)
puts out at the short sumcheck is a plain function, in closed form, of what is sent and drawn.

Definitions, statements and proofs. The head is A.headK (Cb/Pv/KeyLookup/TieM.lean): the draw of al;
the tie of Cb/Pv/Lookup/Blocks/TieF.lean, steps 0, .., n, each a sumcheck without variable of degree
3; a map back into the flat state. The steps are read by Cb/Pv/KeyLookup/NoVar.lean, the statement
has the form Flat.Runs of Cb/Pv/KeyLookup/Flat.lean. No honest side is named.

A step reads three flat rounds f: (μ | ε), (q₁, q₂, q₃ | β), (the values | nothing). With the open
claim (form mf, target tg) it leaves the row
    β, β², β³ at the places w (inl 0), w (inl 1), w (inl 2), 1 at w (inr ()), and ε · mf;
    target (μ + ε tg) + q₁ β + q₂ β² + q₃ β³ - ε · (the summand at the values).
Step 0 shows three values v₀, v₁, v₂, in this order: for the product of all roots, for the power
that is taken up, for plane 0; its summand is v₀ - a · (v₁² · v₂), a the public factor; mf = 0.
A later step l shows two: for the next power, for plane l; its summand is v₀² · v₁.
Each value's claim has the form "β at that value's own place".

Main names:
  TieR.TAcc: what the steps carry, flat: the open claim, the claim on the product of all roots, the
    planes' claims, the rows.
  TieR.step0, TieR.stepN: a step, flat. TieR.accT: the steps 0, .., n. TieR.fmT n: their formats.
  A.tieRun L n, A.headRun L n: the tie and the head as functions of state and flat rounds. They
    are not marked noncomputable.
  tieK_runs A L Ex n : Flat.Runs (A.tieK L (SK₀ E Ex) n) (TieR.fmT n) (A.tieRun L n).
  headK_runs A L Ex n : Flat.Runs (A.headK L (SK₀ E Ex) n) (⟨0, 1, false⟩ :: TieR.fmT n)
    (A.headRun L n): for all st y τ: the verifier's output is some (A.headRun L n st (view τ)).

Limits: no premise but a decidable equality on E. Nothing on soundness.

-/
import Cb.Pv.KeyLookup.NoVar
import Cb.Pv.KeyLookup.TieTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers Flat NoVar

namespace TieR

/-- What the steps carry, flat. -/
structure TAcc (E J : Type) where
  mf : J → E
  tg : E
  all : SCl E J
  planes : ℕ → SCl E J
  rows : List (Row E J)

/-- The order of step 0's three values. -/
def e3 : Option Bool ≃ Fin 3 where
  toFun := fun x =>
    match x with
    | none => 0
    | some false => 1
    | some true => 2
  invFun := fun i =>
    match i with
    | 0 => none
    | 1 => some false
    | 2 => some true
  left_inv := fun x => by rcases x with _ | _ | _ <;> rfl
  right_inv := fun i => by fin_cases i <;> rfl

def fm0 : List Fm := [⟨1, 1, false⟩, ⟨3, 1, true⟩, ⟨3, 0, false⟩]
def fmN : List Fm := [⟨1, 1, false⟩, ⟨3, 1, true⟩, ⟨2, 0, false⟩]

/-- The formats of the steps 0, .., n. -/
def fmT : ℕ → List Fm
  | 0 => fm0
  | n + 1 => fmT n ++ fmN

section
variable {E J : Type} [Field E] [Fintype E] [DecidableEq J]

/-- Step 0, flat. -/
def step0 (a : E) (w : PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J) (cZ cf ct : J)
    (s : TAcc E J) (f : List (RV E)) : TAcc E J where
  mf := one cf (chl f 1)
  tg := snt f 2 1
  all := ⟨one cZ (chl f 1), snt f 2 0⟩
  planes := fun j => if j = 0 then ⟨one ct (chl f 1), snt f 2 2⟩ else s.planes j
  rows := s.rows ++ [⟨rowF 3 w s.mf f,
    finF 3 s.tg f - chl f 0 * (snt f 2 0 - a * (snt f 2 1 ^ 2 * snt f 2 2))⟩]

/-- A later step l, flat. -/
def stepN (w : PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J) (cf ct : J) (l : ℕ)
    (s : TAcc E J) (f : List (RV E)) : TAcc E J where
  mf := one cf (chl f 1)
  tg := snt f 2 0
  all := s.all
  planes := fun j => if j = l then ⟨one ct (chl f 1), snt f 2 1⟩ else s.planes j
  rows := s.rows ++ [⟨rowF 3 w s.mf f, finF 3 s.tg f - chl f 0 * (snt f 2 0 ^ 2 * snt f 2 1)⟩]

/-- The steps 0, .., n, flat. -/
def accT (a : E) (w : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J) (cZ : J)
    (c : ℕ → Bool → J) : (n : ℕ) → TAcc E J → List (RV E) → TAcc E J
  | 0 => step0 a (w 0) cZ (c 0 false) (c 0 true)
  | n + 1 => seqRun (fmT n).length (accT a w cZ c n)
      (stepN (w (n + 1)) (c (n + 1) false) (c (n + 1) true) (n + 1))

end

section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] (Ex : ExtSpec) (D : TieF E)

/-- How step l's three rounds are read flat. -/
noncomputable def rdStep : (l : ℕ) → RdS E (D.stepK (SK₀ E Ex) l).R.shape
  | 0 => rd0V D.St0 D.J (Option Bool) (fun st m a => D.TS.F st m a ()) (fun st v => D.TS.S0 st () v)
      3 D.TS.slS D.TS.wAt D.TS.cAt e3
  | l + 1 => rd0V (D.lv l).T.par.Out D.J Bool (fun o m b => (D.TN l (D.lv l)).F o m b ())
      (fun o v => (D.TN l (D.lv l)).S0 o () v) 3 (D.TN l (D.lv l)).slS (D.wAt (l + 1))
      (D.cAt (l + 1)) finTwoEquiv.symm

theorem rdStep_zero : (rdStep Ex D 0).fms = fm0 := rfl
theorem rdStep_succ (l : ℕ) : (rdStep Ex D (l + 1)).fms = fmN := rfl

/-- The short sumcheck's value at step l; the typed value of step l. -/
noncomputable def outV (l : ℕ) (x : E × (D.lv l).T.St) (τ : Tr (D.stepK (SK₀ E Ex) l).R.shape) :
    (D.lv l).T.par.Out :=
  TWhole.shortV (D.lv l).T.par (TWhole.F₀ (D.lv l).T.par) x τ
noncomputable def stepV (l : ℕ) (x : E × (D.lv l).T.St) (τ : Tr (D.stepK (SK₀ E Ex) l).R.shape) :
    E × (D.lv (l + 1)).T.St :=
  D.nxt l (outV Ex D l x τ)

omit [DecidableEq E] in
theorem step_out (l : ℕ) (x : E × (D.lv l).T.St) (y : Ex.Str)
    (τ : Tr (D.stepK (SK₀ E Ex) l).R.shape) :
    (D.stepK (SK₀ E Ex) l).R.out x y τ = some (stepV Ex D l x τ) := by
  show (((SK₀ E Ex).full (D.lv l).T.par).R.out x y τ).bind (fun o => some (D.nxt l o)) = _
  rw [SK₀_out Ex (D.lv l).T.par (Tie.eq0 D l)]
  rfl

/-- Step 0, read off the flat view. -/
theorem facts0 (y : E × (D.lv 0).T.St) (τ : Tr (D.stepK (SK₀ E Ex) 0).R.shape) :
    (outV Ex D 0 y τ).st = y.2 ∧ D.be 0 (outV Ex D 0 y τ) = chl ((rdStep Ex D 0).view τ) 1 ∧
      (∀ a : Option Bool, (outV Ex D 0 y τ).vals a = snt ((rdStep Ex D 0).view τ) 2 (e3 a).val) ∧
      rowUof (D.lv 0).T (D.emB 0) (D.lv 0).toJ (outV Ex D 0 y τ) =
        ⟨rowF 3 (D.wAt 0) (fun _ => 0) ((rdStep Ex D 0).view τ),
          finF 3 y.1 ((rdStep Ex D 0).view τ) - chl ((rdStep Ex D 0).view τ) 0 *
            (snt ((rdStep Ex D 0).view τ) 2 0 - D.a y.2 *
              (snt ((rdStep Ex D 0).view τ) 2 1 ^ 2 * snt ((rdStep Ex D 0).view τ) 2 2))⟩ :=
  facts D.St0 D.J (Option Bool) (fun st m a => D.TS.F st m a ()) (fun st v => D.TS.S0 st () v)
    3 D.TS.slS D.TS.wAt D.TS.cAt (D.emB 0) e3 y τ _ rfl _ rfl

/-- A later step, read off the flat view. -/
theorem factsN (l : ℕ) (y : E × (D.lv (l + 1)).T.St)
    (τ : Tr (D.stepK (SK₀ E Ex) (l + 1)).R.shape) :
    (outV Ex D (l + 1) y τ).st = y.2 ∧
      D.be (l + 1) (outV Ex D (l + 1) y τ) = chl ((rdStep Ex D (l + 1)).view τ) 1 ∧
      (∀ b : Bool, (outV Ex D (l + 1) y τ).vals b =
        snt ((rdStep Ex D (l + 1)).view τ) 2 (finTwoEquiv.symm b).val) ∧
      rowUof (D.lv (l + 1)).T (D.emB (l + 1)) (D.lv (l + 1)).toJ (outV Ex D (l + 1) y τ) =
        ⟨rowF 3 (D.wAt (l + 1)) ((D.lv (l + 1)).T.slS y.2) ((rdStep Ex D (l + 1)).view τ),
          finF 3 y.1 ((rdStep Ex D (l + 1)).view τ) - chl ((rdStep Ex D (l + 1)).view τ) 0 *
            (snt ((rdStep Ex D (l + 1)).view τ) 2 0 ^ 2 *
              snt ((rdStep Ex D (l + 1)).view τ) 2 1)⟩ :=
  facts (D.lv l).T.par.Out D.J Bool (fun o m b => (D.TN l (D.lv l)).F o m b ())
    (fun o v => (D.TN l (D.lv l)).S0 o () v) 3 (D.TN l (D.lv l)).slS (D.wAt (l + 1))
    (D.cAt (l + 1)) (D.emB (l + 1)) finTwoEquiv.symm y τ _ rfl _ rfl

omit [DecidableEq E] in
/-- The form of the claim that the next step takes up. -/
theorem slS_one (k : ℕ) (o : (D.lv k).T.par.Out) :
    (D.lv (k + 1)).T.slS o = one (D.cAt k false) (D.be k o) := by
  cases k <;> rfl

/-- The typed state after the steps 0, .., k and the flat one say the same. -/
structure Rel (k : ℕ) (x0 : D.St0) (rows0 : List (Row E D.J)) (y : E × (D.lv (k + 1)).T.St)
    (s : TAcc E D.J) : Prop where
  base : (D.lv (k + 1)).base y.2 = x0
  tg : s.tg = y.1
  mf : s.mf = one (D.cAt k false) (D.be k y.2)
  all : s.all = ⟨one D.cZ (D.bK k y.2).1, (D.bK k y.2).2⟩
  planes : ∀ j, j < k + 1 → s.planes j = ⟨one (D.cAt j true) (D.bT k y.2 j).1, (D.bT k y.2 j).2⟩
  rows : s.rows = rows0 ++ (D.rowsAt (k + 1) y.2).reverse

theorem rel_zero (y : E × (D.lv 0).T.St) (s : TAcc E D.J) (h1 : s.tg = y.1)
    (h2 : s.mf = fun _ => 0) (τ : Tr (D.stepK (SK₀ E Ex) 0).R.shape) :
    Rel D 0 y.2 s.rows (stepV Ex D 0 y τ)
      (step0 (D.a y.2) (D.wAt 0) D.cZ (D.cAt 0 false) (D.cAt 0 true) s
        ((rdStep Ex D 0).view τ)) := by
  obtain ⟨f1, f2, f3, f4⟩ := facts0 Ex D y τ
  refine ⟨f1, (f3 (some false)).symm, ?_, ?_, fun j hj => ?_, ?_⟩
  · show one (D.cAt 0 false) _ = one (D.cAt 0 false) (D.be 0 (outV Ex D 0 y τ))
    rw [f2]
  · show (⟨one D.cZ _, _⟩ : SCl E D.J) =
      ⟨one D.cZ (D.be 0 (outV Ex D 0 y τ)), (outV Ex D 0 y τ).vals none⟩
    rw [f2, f3 none]
    rfl
  · have hj0 : j = 0 := by omega
    subst hj0
    show (⟨one (D.cAt 0 true) _, _⟩ : SCl E D.J) =
      ⟨one (D.cAt 0 true) (D.be 0 (outV Ex D 0 y τ)), (outV Ex D 0 y τ).vals (some true)⟩
    rw [f2, f3 (some true)]
    rfl
  · show s.rows ++ [_] = s.rows ++ [rowUof (D.lv 0).T (D.emB 0) (D.lv 0).toJ (outV Ex D 0 y τ)]
    rw [f4, h1, h2]

theorem rel_succ (k : ℕ) (x0 : D.St0) (rows0 : List (Row E D.J)) (y : E × (D.lv (k + 1)).T.St)
    (s : TAcc E D.J) (τ : Tr (D.stepK (SK₀ E Ex) (k + 1)).R.shape) (h : Rel D k x0 rows0 y s) :
    Rel D (k + 1) x0 rows0 (stepV Ex D (k + 1) y τ)
      (stepN (D.wAt (k + 1)) (D.cAt (k + 1) false) (D.cAt (k + 1) true) (k + 1) s
        ((rdStep Ex D (k + 1)).view τ)) := by
  obtain ⟨f1, f2, f3, f4⟩ := factsN Ex D k y τ
  refine ⟨?_, (f3 false).symm, ?_, ?_, fun j hj => ?_, ?_⟩
  · show (D.lv (k + 1)).base (outV Ex D (k + 1) y τ).st = x0
    rw [f1]
    exact h.base
  · show one (D.cAt (k + 1) false) _ =
      one (D.cAt (k + 1) false) (D.be (k + 1) (outV Ex D (k + 1) y τ))
    rw [f2]
  · show s.all = ⟨one D.cZ (D.bK k (outV Ex D (k + 1) y τ).st).1,
      (D.bK k (outV Ex D (k + 1) y τ).st).2⟩
    rw [f1]
    exact h.all
  · by_cases hk : j = k + 1
    · subst hk
      have e : D.bT (k + 1) (outV Ex D (k + 1) y τ) (k + 1) =
          (D.be (k + 1) (outV Ex D (k + 1) y τ), (outV Ex D (k + 1) y τ).vals true) := if_pos rfl
      show (if k + 1 = k + 1 then (⟨one (D.cAt (k + 1) true) _, _⟩ : SCl E D.J) else _) =
        ⟨one (D.cAt (k + 1) true) (D.bT (k + 1) (outV Ex D (k + 1) y τ) (k + 1)).1,
          (D.bT (k + 1) (outV Ex D (k + 1) y τ) (k + 1)).2⟩
      rw [if_pos rfl, e, f2, f3 true]
      rfl
    · have e : D.bT (k + 1) (outV Ex D (k + 1) y τ) j = D.bT k y.2 j :=
        (if_neg hk : D.bT (k + 1) (outV Ex D (k + 1) y τ) j =
          D.bT k (outV Ex D (k + 1) y τ).st j).trans (by rw [f1])
      show (if j = k + 1 then _ else s.planes j) =
        ⟨one (D.cAt j true) (D.bT (k + 1) (outV Ex D (k + 1) y τ) j).1,
          (D.bT (k + 1) (outV Ex D (k + 1) y τ) j).2⟩
      rw [if_neg hk, e]
      exact h.planes j (by omega)
  · have e : D.rowsAt (k + 2) (stepV Ex D (k + 1) y τ).2 =
        rowUof (D.lv (k + 1)).T (D.emB (k + 1)) (D.lv (k + 1)).toJ (outV Ex D (k + 1) y τ) ::
          D.rowsAt (k + 1) (outV Ex D (k + 1) y τ).st := rfl
    show s.rows ++ [_] = rows0 ++ (D.rowsAt (k + 2) (stepV Ex D (k + 1) y τ).2).reverse
    rw [e, List.reverse_cons, f1, f4, h.rows, List.append_assoc, slS_one, ← h.mf, ← h.tg]

/-- The typed run: the value at the typed transcript that the flat one spells. -/
noncomputable def runT : (n : ℕ) → E × (D.lv 0).T.St → List (RV E) → E × (D.lv (n + 1)).T.St
  | 0 => fun x f => stepV Ex D 0 x ((rdStep Ex D 0).mk f)
  | n + 1 => seqRun (fmT n).length (runT n)
      fun x f => stepV Ex D (n + 1) x ((rdStep Ex D (n + 1)).mk f)

noncomputable def runsT : (n : ℕ) → Runs (D.tieK (SK₀ E Ex) n) (fmT n) (runT Ex D n)
  | 0 => (Runs.ofOut (rdStep Ex D 0) (stepV Ex D 0) (step_out Ex D 0)).fmEq (rdStep_zero Ex D)
  | n + 1 => (runsT n).seq
      ((Runs.ofOut (rdStep Ex D (n + 1)) (stepV Ex D (n + 1)) (step_out Ex D (n + 1))).fmEq
        (rdStep_succ Ex D n))

theorem rel_chain (y : E × (D.lv 0).T.St) (s : TAcc E D.J) (h1 : s.tg = y.1)
    (h2 : s.mf = fun _ => 0) : ∀ (n : ℕ) (f : List (RV E)), fitsAll (fmT n) f = true →
      Rel D n y.2 s.rows (runT Ex D n y f) (accT (D.a y.2) D.wAt D.cZ D.cAt n s f)
  | 0, f, hf => by
    have h := rel_zero Ex D y s h1 h2 ((rdStep Ex D 0).mk f)
    rw [(rdStep Ex D 0).view_mk f (by rw [rdStep_zero]; exact hf)] at h
    exact h
  | n + 1, f, hf => by
    obtain ⟨g1, g2⟩ := fitsAll_app (fmT n) fmN f hf
    have h := rel_succ Ex D n y.2 s.rows _ _ ((rdStep Ex D (n + 1)).mk (f.drop (fmT n).length))
      (rel_chain y s h1 h2 n (f.take (fmT n).length) g1)
    rw [(rdStep Ex D (n + 1)).view_mk _ (by rw [rdStep_succ]; exact g2)] at h
    exact h

end
end TieR

section
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (L : TiePl E A.J)

/-- The tie's verifier, flat and in closed form. -/
def Dat.tieRun (n : ℕ) (x : A.XS) (f : List (RV E)) : A.XS :=
  { x with
    all := (TieR.accT (A.fac x.st x.al) L.wAt L.cZ L.cAt n
      ⟨fun _ => 0, 0, x.all, x.planes, x.rows⟩ f).all
    planes := fun j =>
      if j < n + 1 then (TieR.accT (A.fac x.st x.al) L.wAt L.cZ L.cAt n
        ⟨fun _ => 0, 0, x.all, x.planes, x.rows⟩ f).planes j
      else ⟨(TieR.accT (A.fac x.st x.al) L.wAt L.cZ L.cAt n
          ⟨fun _ => 0, 0, x.all, x.planes, x.rows⟩ f).mf,
        (TieR.accT (A.fac x.st x.al) L.wAt L.cZ L.cAt n
          ⟨fun _ => 0, 0, x.all, x.planes, x.rows⟩ f).tg⟩
    rows := (TieR.accT (A.fac x.st x.al) L.wAt L.cZ L.cAt n
      ⟨fun _ => 0, 0, x.all, x.planes, x.rows⟩ f).rows }

/-- The head's verifier, flat and in closed form: the draw, then the tie. -/
def Dat.headRun (n : ℕ) : A.St → List (RV E) → A.XS :=
  seqRun 1 (fun st f => A.ini st ((f.headD ([], [])).2.headD 0)) (A.tieRun L n)

theorem Dat.back_eq (n : ℕ) (x : A.XS) (y : E × ((A.tie L).lv (n + 1)).T.St)
    (s : TieR.TAcc E A.J) (h : TieR.Rel (A.tie L) n x x.rows y s) :
    A.back L n y =
      { x with
        all := s.all
        planes := fun j => if j < n + 1 then s.planes j else ⟨s.mf, s.tg⟩
        rows := s.rows } := by
  have hold : A.old L n y = x := h.base
  have hall : (⟨at1 L.cZ ((A.tie L).bK n y.2).1, ((A.tie L).bK n y.2).2⟩ : SCl E A.J) = s.all :=
    h.all.symm
  have hpl : (fun j => if j < n + 1 then
        (⟨at1 (L.cAt j true) ((A.tie L).bT n y.2 j).1, ((A.tie L).bT n y.2 j).2⟩ : SCl E A.J)
      else ⟨at1 (L.cAt n false) ((A.tie L).be n y.2), y.1⟩) =
      fun j => if j < n + 1 then s.planes j else ⟨s.mf, s.tg⟩ := by
    funext j
    by_cases hj : j < n + 1
    · rw [if_pos hj, if_pos hj]
      exact (h.planes j hj).symm
    · rw [if_neg hj, if_neg hj]
      exact congrArg₂ SCl.mk h.mf.symm h.tg.symm
  have hrows : (A.old L n y).rows ++ A.tieRows L n y = s.rows := by
    rw [hold]
    exact h.rows.symm
  unfold Dat.back
  rw [hall, hpl, hrows, hold]

variable [DecidableEq E] (Ex : ExtSpec)

/-- For all transcripts: the tie's verifier at the short sumcheck puts out A.tieRun of the view. -/
noncomputable def tieK_runs (n : ℕ) :
    Runs (A.tieK L (SK₀ E Ex) n) (TieR.fmT n) (A.tieRun L n) :=
  (((TieR.runsT Ex (A.tie L) n).preM fun x : A.XS => ((0 : E), x)).postM (A.back L n)).congr
    fun x f hf => A.back_eq L n x _ _
      (TieR.rel_chain Ex (A.tie L) ((0 : E), x) ⟨fun _ => 0, 0, x.all, x.planes, x.rows⟩ rfl rfl
        n f hf)

/-- For all transcripts: the head's verifier at the short sumcheck puts out A.headRun of the
view. -/
noncomputable def headK_runs (n : ℕ) :
    Runs (A.headK L (SK₀ E Ex) n) (⟨0, 1, false⟩ :: TieR.fmT n) (A.headRun L n) :=
  (Runs.draw A.ini (A.allKeys - 1) rdE (fun l => l.headD 0) fun _ => rfl).seq (tieK_runs A L Ex n)

end
end Lk6

#print axioms Lk6.TieR.rel_zero
#print axioms Lk6.TieR.rel_succ
#print axioms Lk6.TieR.rel_chain
#print axioms Lk6.tieK_runs
#print axioms Lk6.headK_runs
