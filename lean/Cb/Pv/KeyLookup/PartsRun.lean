-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsRun.lean: what the verifier of the parts' steps puts out at the short sumcheck
is a plain function, in closed form, of what is sent and drawn.

Definitions, statements and proofs. The stretch is A.partsXK (Cb/Pv/KeyLookup/PartsK.lean) at SK₀
(Cb/Pv/KeyLookup/Short0.lean); the statement has the form Flat.Runs of Cb/Pv/KeyLookup/Flat.lean. No
honest side is named.

Main names:
  Parts.one i c: the form "c at the entry i, 0 elsewhere", by a decidable equality on the entries.
  Parts.stepAcc: one step, flat. From the open claim (form mf, target tg) and the three rounds
    ([μ] | [ε]), ([q₁, q₂] | [β]), ([v₀, v₁] | []):
      the row: β at w₁, β² at w₂, 1 at w₀, and ε · mf; target (μ + ε tg) + q₁ β + q₂ β² - ε v₀ v₁;
      the root's claim: β at c₀; target v₀; the next open claim: β at c₁; target v₁.
                       (w₀ := wP l i0, the hiding polynomial's constant;
                       w₁, w₂ := wP l i1 | i2, of Y | Y²; c₀, c₁ := cP l false | true.)
  A.partsRun wP cP: the m - 1 steps from (x.all.mf, x.all.tg); x with roots and rows turned:
    A.XS → List (RV E) → A.XS. It is not marked noncomputable.
  Parts.fmK k: the formats of k steps: (1 | 1), (2 | 1, not 0), (2 | 0) a step.
  mkT_value: the short verifier's value (TWhole.shortV at the pick F₀) at a transcript of a sumcheck
    without variable on a product of two values, written out.
  mkT_row              the library's row on the hiding coefficients (rowUof),
                       COEFFICIENT BY COEFFICIENT.
  step_rel, rel_chain: the typed state after k steps and the flat one say the same (Rel: first
    state, target, open form, the roots' claims, the rows).
  partsXK_runs A wP cP Ex : Flat.Runs (A.partsXK wP cP (SK₀ E Ex)) (Parts.fmK (A.m - 1))
    (A.partsRun wP cP): for all x y τ the verifier's output is some (A.partsRun wP cP x (view τ)).
  partsXK_total_short: for all x y τ the verifier puts out some state.

How the proof goes, for the like of it elsewhere: how the block's shape is read flat (rdFull);
"out = some (typed value)" from SK₀_out under Eq0, then Runs.ofOut, Runs.seq, Runs.postM; a relation
between the typed state and the flat one that a step keeps for every typed τ, the flat step taken at
the view of τ; Runs.congr.

Limits: partsXK_runs asks a decidable equality on E and nothing else; partsXK_total_short has no
premise. Nothing on soundness.

-/
import Cb.Pv.KeyLookup.Flat
import Cb.Pv.KeyLookup.PartsShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers Flat

namespace Parts

/-- c at the entry i, 0 elsewhere. -/
def one {E J : Type} [Zero E] [DecidableEq J] (i : J) (c : E) : J → E :=
  fun j => if j = i then c else 0

theorem ite_one {E J : Type} [Zero E] [DecidableEq J] (i j : J) (c : E) (inst : Decidable (i = j)) :
    @ite E (i = j) inst c 0 = one i c j := by
  unfold one
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun e => h e.symm]

theorem ite_one' {E J : Type} [Zero E] [DecidableEq J] (i j : J) (c : E)
    (inst : Decidable (j = i)) :
    @ite E (j = i) inst c 0 = one i c j := by
  unfold one
  by_cases h : j = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- What the steps carry, flat. -/
structure Acc (E J : Type) where
  mf : J → E
  tg : E
  roots : ℕ → SCl E J
  rows : List (Row E J)

/-- One step, flat. -/
def stepAcc {E J : Type} [Field E] [DecidableEq J] (w0 w1 w2 c0 c1 : J) (l : ℕ) (a : Acc E J) :
    List (RV E) → Acc E J
  | [([mu], [eps]), ([q1, q2], [be]), ([v0, v1], [])] =>
    { mf := one c1 be
      tg := v1
      roots := fun i => if i = l then ⟨one c0 be, v0⟩ else a.roots i
      rows := a.rows ++ [⟨fun j => one w1 be j + one w2 (be ^ 2) j + one w0 1 j + eps * a.mf j,
        mu + eps * a.tg + q1 * be + q2 * be ^ 2 - eps * (v0 * v1)⟩] }
  | _ => a

def fmStep : List Fm := [⟨1, 1, false⟩, ⟨2, 1, true⟩, ⟨2, 0, false⟩]

def fmK : ℕ → List Fm
  | 0 => []
  | k + 1 => fmK k ++ fmStep

section
variable {E : Type} [Field E] [Fintype E]

/-- The sumcheck without variable on a product of two values: all that a step of the chain is. -/
noncomputable def mkT (St J : Type) [Fintype J] (F : St → (J → E) → Bool → E) (sl : St → J → E)
    (w : PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → J) (c : Bool → J) : PscOur E where
  St := St
  J := J
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun st m b _ => F st m b
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false * v true
  S1 := fun _ _ _ b => b.elim
  DY := 2
  slS := sl
  wAt := w
  cAt := c

/-- The names of a step's three hiding coefficients: the constant; of Y; of Y². -/
def i0 : PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) := (Sum.inr () : Fin 2 ⊕ Unit)
def i1 : PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) := (Sum.inl 0 : Fin 2 ⊕ Unit)
def i2 : PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) := (Sum.inl 1 : Fin 2 ⊕ Unit)

/-- Y's polynomial completed at the constant, at the draw. -/
theorem fill_dummy (σ β : E) (q : Fin 2 → E) :
    hev (hFill ((pDummy E 2).var (pDummyD E 2)) ((0 : Fin 3), (1 : E)) σ q) β =
      σ + q 0 * β + q 1 * β ^ 2 := by
  have h0 : ((pDummy E 2).var (pDummyD E 2)).phi
      ((0 : Fin 3).insertNth (α := fun _ => E) 0 q) = 0 := by
    show ∑ _s : Unit, (1 : E) • ∑ t : Fin 3, (0 : E) ^ (t : ℕ) •
      ((0 : Fin 3).insertNth (α := fun _ => E) 0 q) t = 0
    simp [Fin.sum_univ_succ]
  show hev ((0 : Fin 3).insertNth (α := fun _ => E) ((1 : E) • (σ -
    ((pDummy E 2).var (pDummyD E 2)).phi ((0 : Fin 3).insertNth (α := fun _ => E) 0 q))) q) β = _
  rw [h0]
  show ∑ t : Fin 3, β ^ (t : ℕ) •
    ((0 : Fin 3).insertNth (α := fun _ => E) ((1 : E) • (σ - 0)) q) t = _
  simp [Fin.sum_univ_succ]
  ring

theorem psi_dummy (β : E) : hPsi [(pDummy E 2).var (pDummyD E 2)] (β, ()) = 1 := by
  show (∑ t : Fin 3, β ^ (t : ℕ) • (if t = 0 then (1 : E) else 0)) * 1 = 1
  simp

omit [Fintype E] in
theorem sum_hidx (v : HVar E) (g : HIdx [v] → E) :
    ∑ i, g i = ∑ t : Fin v.n, g (.inl t) + g (.inr ()) := by
  show ∑ i : Fin v.n ⊕ Unit, g i = _
  rw [Fintype.sum_sum_type]
  exact congrArg (fun z => (∑ t : Fin v.n, g (.inl t)) + z)
    (Fintype.sum_unique fun a : Unit => g (.inr a))

omit [Fintype E] in
theorem pushJ_id {J : Type} [Fintype J] (c : J → E) : pushJ (id : J → J) c = c := by
  funext j
  exact (Finset.sum_eq_single j (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ j) h)).trans (if_pos rfl)

variable (St J : Type) [Fintype J] [DecidableEq J] (F : St → (J → E) → Bool → E) (sl : St → J → E)
  (w : PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → J) (c : Bool → J)

omit [DecidableEq J] in
/-- The short verifier's value at a transcript, written out. -/
theorem mkT_value (x : E × St) (mu eps : E) (q : Fin 2 → E) (be : {x : E // x ≠ 0}) (v : Bool → E) :
    TWhole.shortV (mkT St J F sl w c).par (TWhole.F₀ (mkT St J F sl w c).par) x
        (((), mu), eps, (((), q), be, (((), v), (), ()))) =
      ⟨x.2, eps, (be.1, ()), mu + eps * x.1 + q 0 * be.1 + q 1 * be.1 ^ 2, v⟩ := by
  have h := fill_dummy (mu + eps * x.1) be.1 q
  show (⟨x.2, eps, (be.1, ()),
    hev (hFill ((pDummy E 2).var (pDummyD E 2)) ((0 : Fin 3), (1 : E)) (mu + eps * x.1) q) be.1,
    v⟩ :
      (mkT St J F sl w c).par.Out) = _
  rw [h]

/-- The row on the hiding coefficients, coefficient by coefficient. -/
theorem mkT_row (h : IsEmpty (mkT St J F sl w c).par.B) (st : St) (eps be fin : E) (v : Bool → E) :
    rowUof (mkT St J F sl w c) h (id : J → J) ⟨st, eps, (be, ()), fin, v⟩ =
      ⟨fun j => one (w i1) be j + one (w i2) (be ^ 2) j + one (w i0) 1 j + eps * sl st j,
        fin - eps * (v false * v true)⟩ := by
  unfold rowUof
  refine congrArg₂ Row.mk ((pushJ_id _).trans (funext fun (j : J) => ?_)) rfl
  unfold PscPar.slU
  show (∑ i : HIdx [(pDummy E 2).var (pDummyD E 2)], _) + _ + _ = _
  rw [sum_hidx]
  show ((∑ t : Fin 2, _) + _) + _ + _ = _
  rw [Fin.sum_univ_two]
  show ((@ite E (w i1 = j) (Classical.propDecidable _) (1 * be ^ (0 + 1)) 0 +
        @ite E (w i2 = j) (Classical.propDecidable _) (1 * be ^ (1 + 1)) 0) +
      @ite E (w i0 = j) (Classical.propDecidable _) 1 0) +
    eps * hPsi [(pDummy E 2).var (pDummyD E 2)] (be, ()) * sl st j + eps * ∑ b : Empty, _ = _
  rw [psi_dummy, ite_one, ite_one, ite_one, Finset.univ_eq_empty, Finset.sum_empty]
  simp

end

/-! ### a step: the typed value against the flat one -/
section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
variable (St J : Type) [Fintype J] [DecidableEq J] (F : St → (J → E) → Bool → E) (sl : St → J → E)
  (w : PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → J) (c : Bool → J)

/-- How a step's three rounds are read flat. -/
noncomputable def rdT : RdS E (shapeS (mkT St J F sl w c).par) :=
  rdFull (mkT St J F sl w c).par ((fuDummy 2, ()) : FU (pDummy E 2) × Unit) finTwoEquiv.symm

omit [DecidableEq J] in
theorem rdT_fms : (rdT St J F sl w c).fms = fmStep := rfl

theorem mkT_step (h : IsEmpty (mkT St J F sl w c).par.B) (l : ℕ) (y : E × St) (a : Acc E J)
    (τ : Tr (shapeS (mkT St J F sl w c).par)) (h1 : a.tg = y.1) (h2 : a.mf = sl y.2)
    (o : (mkT St J F sl w c).par.Out)
    (ho : o = TWhole.shortV (mkT St J F sl w c).par (TWhole.F₀ (mkT St J F sl w c).par) y τ)
    (a' : Acc E J)
    (ha : a' = stepAcc (w i0) (w i1) (w i2) (c false) (c true) l a ((rdT St J F sl w c).view τ)) :
    o.st = y.2 ∧ a'.tg = o.vals true ∧
      a'.mf = one (c true) ((mkT St J F sl w c).lst o.st ((mkT St J F sl w c).par.hp o.st o.pt)) ∧
      a'.roots = (fun i => if i = l then
        ⟨one (c false) ((mkT St J F sl w c).lst o.st ((mkT St J F sl w c).par.hp o.st o.pt)),
          o.vals false⟩ else a.roots i) ∧
      a'.rows = a.rows ++ [rowUof (mkT St J F sl w c) h (id : J → J) o] := by
  obtain ⟨⟨_, (mu : E)⟩, (eps : E), ⟨_, (q : Fin 2 → E)⟩, (be : {x : E // x ≠ 0}),
    ⟨_, (v : Bool → E)⟩, _, _⟩ := τ
  have hv : (rdT St J F sl w c).view (((), mu), eps, (((), q), be, (((), v), (), ()))) =
      [([mu], [eps]), ([q 0, q 1], [be.1]), ([v false, v true], [])] := rfl
  have ho' := ho.trans (mkT_value St J F sl w c y mu eps q be v)
  have ha' : a' = stepAcc (w i0) (w i1) (w i2) (c false) (c true) l a
      [([mu], [eps]), ([q 0, q 1], [be.1]), ([v false, v true], [])] :=
    ha.trans (congrArg (stepAcc (w i0) (w i1) (w i2) (c false) (c true) l a) hv)
  clear ho ha
  subst ho'
  subst ha'
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [mkT_row, ← h1, ← h2]
  rfl

end

/-! ### the chain -/
section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] (Ex : ExtSpec) (D : PartsP E)
  [DecidableEq D.J]

/-- How step l's rounds are read flat. -/
noncomputable def rdStep : (l : ℕ) → RdS E (D.stepK (SK₀ E Ex) l).R.shape
  | 0 => rdT D.St0 D.J (fun st m b => if b then D.rest st m 1 else D.root st m 0) D.inc (D.wAt 0)
      (D.cAt 0)
  | l + 1 => rdT (D.lv l).T.par.Out D.J
      (fun o m b => if b then D.rest ((D.lv l).base o.st) m (l + 2)
        else D.root ((D.lv l).base o.st) m (l + 1))
      (D.lv (l + 1)).T.slS (D.wAt (l + 1)) (D.cAt (l + 1))

omit [DecidableEq D.J] in
theorem rdStep_fms : ∀ l, (rdStep Ex D l).fms = fmStep
  | 0 => rfl
  | _ + 1 => rfl

/-- The short sumcheck's value at step l; the typed value of step l. -/
noncomputable def outV (l : ℕ) (x : E × (D.lv l).T.St) (τ : Tr (D.stepK (SK₀ E Ex) l).R.shape) :
    (D.lv l).T.par.Out :=
  TWhole.shortV (D.lv l).T.par (TWhole.F₀ (D.lv l).T.par) x τ
noncomputable def stepV (l : ℕ) (x : E × (D.lv l).T.St) (τ : Tr (D.stepK (SK₀ E Ex) l).R.shape) :
    E × (D.lv (l + 1)).T.St :=
  D.nxt l (outV Ex D l x τ)

omit [DecidableEq E] [DecidableEq D.J] in
theorem step_out (l : ℕ) (x : E × (D.lv l).T.St) (y : Ex.Str)
    (τ : Tr (D.stepK (SK₀ E Ex) l).R.shape) :
    (D.stepK (SK₀ E Ex) l).R.out x y τ = some (stepV Ex D l x τ) := by
  show (((SK₀ E Ex).full (D.lv l).T.par).R.out x y τ).bind (fun o => some (D.nxt l o)) = _
  rw [SK₀_out Ex (D.lv l).T.par (parts_eq0 D l)]
  rfl

theorem step_facts (k : ℕ) (y : E × (D.lv k).T.St) (a : Acc E D.J)
    (τ : Tr (D.stepK (SK₀ E Ex) k).R.shape) (h1 : a.tg = y.1)
    (h2 : a.mf = pushJ (D.lv k).toJ ((D.lv k).T.slS y.2)) (o : (D.lv k).T.par.Out)
    (ho : o = TWhole.shortV (D.lv k).T.par (TWhole.F₀ (D.lv k).T.par) y τ) (a' : Acc E D.J)
    (ha : a' = stepAcc (D.wAt k i0) (D.wAt k i1) (D.wAt k i2) (D.cAt k false) (D.cAt k true) k a
      ((rdStep Ex D k).view τ)) :
    o.st = y.2 ∧ a'.tg = o.vals (D.lv k).nx ∧ a'.mf = one (D.cAt k true) (D.be k o) ∧
      a'.roots = (fun i => if i = k then ⟨one (D.cAt k false) (D.be k o), o.vals (D.lv k).pt⟩
        else a.roots i) ∧
      a'.rows = a.rows ++ [rowUof (D.lv k).T (D.emB k) (D.lv k).toJ o] := by
  cases k with
  | zero =>
    exact mkT_step D.St0 D.J (fun st m b => if b then D.rest st m 1 else D.root st m 0) D.inc
      (D.wAt 0) (D.cAt 0) (D.emB 0) 0 y a τ h1 (h2.trans (pushJ_id _)) o ho a' ha
  | succ k =>
    exact mkT_step (D.lv k).T.par.Out D.J
      (fun o m b => if b then D.rest ((D.lv k).base o.st) m (k + 2)
        else D.root ((D.lv k).base o.st) m (k + 1))
      (D.lv (k + 1)).T.slS (D.wAt (k + 1)) (D.cAt (k + 1)) (D.emB (k + 1)) (k + 1) y a τ h1
      (h2.trans (pushJ_id _)) o ho a' ha

/-- The typed state after k steps and the flat one say the same. -/
structure Rel (k : ℕ) (x0 : D.St0) (rows0 : List (Row E D.J)) (y : E × (D.lv k).T.St)
    (a : Acc E D.J) : Prop where
  base : (D.lv k).base y.2 = x0
  tg : a.tg = y.1
  mf : a.mf = pushJ (D.lv k).toJ ((D.lv k).T.slS y.2)
  roots : ∀ i, i < k → a.roots i = ⟨D.formAt k y i, D.tgtAt k y i⟩
  rows : a.rows = rows0 ++ (D.rowsAt k y.2).reverse

omit [DecidableEq E] in
theorem formAt_new (k : ℕ) (o : (D.lv k).T.par.Out) (t : E) :
    D.formAt (k + 1) (t, o) k = one (D.cAt k false) (D.be k o) := by
  unfold PartsP.formAt
  rw [if_pos (Nat.lt_succ_self k)]
  have e : D.bR (k + 1) o k = (D.be k o, o.vals (D.lv k).pt) := if_pos rfl
  funext j
  show @ite E (j = D.cAt k false) (Classical.propDecidable _) (D.bR (k + 1) o k).1 0 = _
  rw [e]
  exact ite_one' _ _ _ _

omit [DecidableEq E] [DecidableEq D.J] in
theorem tgtAt_new (k : ℕ) (o : (D.lv k).T.par.Out) (t : E) :
    D.tgtAt (k + 1) (t, o) k = o.vals (D.lv k).pt := by
  unfold PartsP.tgtAt
  rw [if_pos (Nat.lt_succ_self k)]
  have e : D.bR (k + 1) o k = (D.be k o, o.vals (D.lv k).pt) := if_pos rfl
  show (D.bR (k + 1) o k).2 = _
  rw [e]

omit [DecidableEq E] [DecidableEq D.J] in
theorem at_old (k : ℕ) (o : (D.lv k).T.par.Out) (t : E) (y : E × (D.lv k).T.St) (hy : o.st = y.2)
    (i : ℕ) (hi : i < k) :
    D.formAt (k + 1) (t, o) i = D.formAt k y i ∧ D.tgtAt (k + 1) (t, o) i = D.tgtAt k y i := by
  have e : D.bR (k + 1) o i = D.bR k y.2 i :=
    (if_neg (Nat.ne_of_lt hi) : D.bR (k + 1) o i = D.bR k o.st i).trans (by rw [hy])
  unfold PartsP.formAt PartsP.tgtAt
  rw [if_pos (Nat.lt_succ_of_lt hi), if_pos hi, if_pos (Nat.lt_succ_of_lt hi), if_pos hi]
  constructor
  · show (fun j =>
      @ite E (j = D.cAt i false) (Classical.propDecidable _) (D.bR (k + 1) o i).1 0) = _
    rw [e]
  · show (D.bR (k + 1) o i).2 = _
    rw [e]

theorem step_rel (k : ℕ) (x0 : D.St0) (rows0 : List (Row E D.J)) (y : E × (D.lv k).T.St)
    (a : Acc E D.J) (τ : Tr (D.stepK (SK₀ E Ex) k).R.shape) (h : Rel D k x0 rows0 y a) :
    Rel D (k + 1) x0 rows0 (stepV Ex D k y τ)
      (stepAcc (D.wAt k i0) (D.wAt k i1) (D.wAt k i2) (D.cAt k false) (D.cAt k true) k a
        ((rdStep Ex D k).view τ)) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := step_facts Ex D k y a τ h.tg h.mf (outV Ex D k y τ) rfl _ rfl
  refine ⟨?_, f2, ?_, fun i hi => ?_, ?_⟩
  · show (D.lv k).base (outV Ex D k y τ).st = x0
    rw [f1]
    exact h.base
  · rw [f3]
    refine ((pushJ_id _).trans (funext fun j => ?_)).symm
    show @ite E (j = (D.lv k).toJ ((D.lv k).T.cAt (D.lv k).nx)) (Classical.propDecidable _)
      (D.be k (outV Ex D k y τ)) 0 = _
    rw [D.cAt_nx k]
    exact ite_one' _ _ _ _
  · rw [f4]
    by_cases hk : i = k
    · subst hk
      show (if i = i then _ else _) = _
      rw [if_pos rfl]
      exact congrArg₂ SCl.mk (formAt_new D i _ _).symm (tgtAt_new D i _ _).symm
    · show (if i = k then _ else _) = _
      rw [if_neg hk, h.roots i (by omega)]
      obtain ⟨e1, e2⟩ := at_old D k (outV Ex D k y τ) ((outV Ex D k y τ).vals (D.lv k).nx) y f1 i
        (by omega)
      exact congrArg₂ SCl.mk e1.symm e2.symm
  · have e : D.rowsAt (k + 1) (stepV Ex D k y τ).2 =
        rowUof (D.lv k).T (D.emB k) (D.lv k).toJ (outV Ex D k y τ) ::
          D.rowsAt k (outV Ex D k y τ).st := rfl
    rw [f5, h.rows, List.append_assoc, e, List.reverse_cons, f1]

/-- The typed run: the value at the typed transcript that the flat one spells. -/
noncomputable def runT {X : Type} (φ : X → E × (D.lv 0).T.St) :
    (k : ℕ) → X → List (RV E) → E × (D.lv k).T.St
  | 0 => fun x _ => φ x
  | k + 1 => seqRun (fmK k).length (runT φ k) fun x f => stepV Ex D k x ((rdStep Ex D k).mk f)

noncomputable def runsT {X : Type} (φ : X → E × (D.lv 0).T.St) :
    (k : ℕ) → Runs (D.afterK (SK₀ E Ex) (mapK Ex φ) k) (fmK k) (runT Ex D φ k)
  | 0 => Runs.map φ
  | k + 1 => (runsT φ k).seq
      ((Runs.ofOut (rdStep Ex D k) (stepV Ex D k) (step_out Ex D k)).fmEq (rdStep_fms Ex D k))

end

/-- The flat run of k steps. -/
def accK {E J : Type} [Field E] [Fintype E] [DecidableEq J]
    (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → J) (cP : ℕ → Bool → J) :
    (k : ℕ) → Acc E J → List (RV E) → Acc E J
  | 0 => fun a _ => a
  | k + 1 => seqRun (fmK k).length (accK wP cP k) fun a f =>
      stepAcc (wP k i0) (wP k i1) (wP k i2) (cP k false) (cP k true) k a f

theorem rel_chain {E : Type} [Field E] [Fintype E] [DecidableEq E] (Ex : ExtSpec) (D : PartsP E)
    [DecidableEq D.J] {X : Type} (φ : X → E × (D.lv 0).T.St) (x : X) (x0 : D.St0)
    (rows0 : List (Row E D.J)) (a0 : Acc E D.J) (h0 : Rel D 0 x0 rows0 (φ x) a0) :
    ∀ (k : ℕ) (f : List (RV E)), fitsAll (fmK k) f = true →
      Rel D k x0 rows0 (runT Ex D φ k x f) (accK D.wAt D.cAt k a0 f)
  | 0, _, _ => h0
  | k + 1, f, hf => by
    obtain ⟨f1, f2⟩ := fitsAll_app (fmK k) fmStep f hf
    have h := step_rel Ex D k x0 rows0 _ _ ((rdStep Ex D k).mk (f.drop (fmK k).length))
      (rel_chain Ex D φ x x0 rows0 a0 h0 k (f.take (fmK k).length) f1)
    rw [(rdStep Ex D k).view_mk _ (by rw [rdStep_fms]; exact f2)] at h
    exact h

end Parts

/-! ### the stretch over the flat state -/
section
variable {E : Type} [Field E] [Fintype E] (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)

/-- The verifier of the parts' steps, flat and in closed form. -/
def Dat.partsRun (x : A.XS) (f : List (RV E)) : A.XS :=
  { x with
    roots := fun i =>
      if i < A.m - 1 then
        (Parts.accK wP cP (A.m - 1) ⟨x.all.mf, x.all.tg, x.roots, x.rows⟩ f).roots i
      else ⟨(Parts.accK wP cP (A.m - 1) ⟨x.all.mf, x.all.tg, x.roots, x.rows⟩ f).mf,
        (Parts.accK wP cP (A.m - 1) ⟨x.all.mf, x.all.tg, x.roots, x.rows⟩ f).tg⟩
    rows := (Parts.accK wP cP (A.m - 1) ⟨x.all.mf, x.all.tg, x.roots, x.rows⟩ f).rows }

instance Dat.partsDecJ : DecidableEq (A.partsD wP cP).J := inferInstanceAs (DecidableEq A.J)

theorem Dat.partsBack_eq (x : A.XS) (y : E × ((A.partsD wP cP).lv (A.partsD wP cP).n).T.St)
    (a : Parts.Acc E A.J) (h : Parts.Rel (A.partsD wP cP) (A.partsD wP cP).n x x.rows y a) :
    A.partsBack wP cP y =
      { x with
        roots := fun i => if i < A.m - 1 then a.roots i else ⟨a.mf, a.tg⟩
        rows := a.rows } := by
  have hold : A.partsOld wP cP y = x := h.base
  have hroots : (fun i => (⟨(A.partsD wP cP).formAt (A.partsD wP cP).n y i,
      (A.partsD wP cP).tgtAt (A.partsD wP cP).n y i⟩ : SCl E A.J)) =
      fun i => if i < A.m - 1 then a.roots i else ⟨a.mf, a.tg⟩ := by
    funext i
    by_cases hi : i < A.m - 1
    · rw [if_pos hi]
      exact (h.roots i hi).symm
    · rw [if_neg hi]
      refine congrArg₂ SCl.mk ?_ ?_
      · exact (if_neg hi : (A.partsD wP cP).formAt (A.partsD wP cP).n y i = _).trans h.mf.symm
      · exact (if_neg hi : (A.partsD wP cP).tgtAt (A.partsD wP cP).n y i = _).trans h.tg.symm
  have hrows : (A.partsOld wP cP y).rows ++ A.partsRows wP cP y = a.rows := by
    rw [hold]
    exact h.rows.symm
  unfold Dat.partsBack
  rw [hroots, hrows, hold]

variable [DecidableEq E] (Ex : ExtSpec)

/-- For all transcripts: the verifier of the parts' steps at the short sumcheck puts out A.partsRun
of the view. -/
noncomputable def partsXK_runs :
    Runs (A.partsXK wP cP (SK₀ E Ex)) (Parts.fmK (A.m - 1)) (A.partsRun wP cP) :=
  ((Parts.runsT Ex (A.partsD wP cP) (A.partsIn wP cP) (A.partsD wP cP).n).postM
    (A.partsBack wP cP)).congr fun x f hf =>
      A.partsBack_eq wP cP x _ _
        (Parts.rel_chain Ex (A.partsD wP cP) (A.partsIn wP cP) x x x.rows
          ⟨x.all.mf, x.all.tg, x.roots, x.rows⟩
          ⟨rfl, rfl, (Parts.pushJ_id _).symm, fun i hi => absurd hi (Nat.not_lt_zero i),
            (List.append_nil _).symm⟩ _ f hf)

end

/-- The verifier of the parts' steps at the short sumcheck rejects nothing: no premise. -/
theorem partsXK_total_short {E : Type} [Field E] [Fintype E] (A : Dat E)
    (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)
    (Ex : ExtSpec)
    (x : A.XS) (y : Ex.Str) (τ : Tr (A.partsXK wP cP (SK₀ E Ex)).R.shape) :
    ∃ x', (A.partsXK wP cP (SK₀ E Ex)).R.out x y τ = some x' := by
  classical
  exact ⟨_, (partsXK_runs A wP cP Ex).out x y τ⟩

end Lk6

#print axioms Lk6.partsXK_total_short
#print axioms Lk6.Parts.mkT_value
#print axioms Lk6.Parts.mkT_row
#print axioms Lk6.Parts.step_rel
#print axioms Lk6.Parts.rel_chain
#print axioms Lk6.partsXK_runs
