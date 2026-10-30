-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LevRunC.lean: the levels of a product tree with orders at the short sumcheck SK₀,
over flat transcripts: what the verifier's state holds behind the levels (the point, the open
claim's form and target, the rows
so far, in the order of time) is a plain function, in closed form, of what it held before and of
what is sent and drawn.

States:
  `Acc`, `AccO`: what is read off a level's state | off a sumcheck's output. `stepSum`, `stepLine`:
                  the two plain functions. `TreeD`: the orders and places of a tree as plain data.
  `levStep`, `treeStep`, `fmLev`, `fmT`: a level; the levels 0 .. n; their formats.
  `mkAbs`: the sumcheck of a level (`mkLev`). `sumAbs`, `lineAbs`, `levAbs`, `treeAbs`: of every
                  tree with orders D, beside any reading ρ of the state with which the tree was
                  entered.
THE RULE OF A LEVEL of k variables, rounds [μ | ε] · k × [q₁, q₂ | γ_j] · [q₁, q₂ | β] · [v₀, v₁ | ]
· [ | ρ]:
  the row: γ_j at the name of round j's first power, γ_j² at its second, β, β² at Y's, 1 at the
  constant's, and ε times the open claim's form; target fin − ε v₀ v₁;
  fin: from μ + ε · target; in round j, which binds variable σ j, the constant is (the claim so far)
  − z (q₁ + q₂), z the open point's coordinate σ j; in Y the constant is the claim so far;
  the next claim: point: coordinate t := γ of round σ⁻¹ t, then ρ; form: β (1 − ρ) at the first
  shown value's entry, β ρ at the second's; target (1 − ρ) v₀ + ρ v₁.
Under: [DecidableEq E], [DecidableEq D.J]. It names no honest side and imports no file of the port.

-/
import Cb.Pv.KeyLookup.LevRunB
import Cb.Pv.KeyLookup.LevLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Lev
open Cb Cb.LdLkp Cb.LdLkp.Kn Iop IOR Hiop Prob Johnson.L5.Layers Flat

/-- What is read off the state of a level: the point, the open claim's form and target, the rows so
far. -/
structure Acc (E J : Type) where
  pt : List E
  mf : J → E
  tg : E
  rows : List (Row E J)

/-- What is read off a sumcheck's output: the end point, Y's draw, the two shown values, the rows so
far. -/
structure AccO (E J : Type) where
  pt : List E
  be : E
  v0 : E
  v1 : E
  rows : List (Row E J)

section
variable {E J : Type} [Field E] [DecidableEq J]

def stepSum (k : ℕ) (σ : Equiv.Perm (Fin k)) (wv : ℕ → Fin 2 → J) (wc : J) (a : Acc E J) (f : List
    (RV E)) :
    AccO E J where
  pt := List.ofFn fun t : Fin k => chC f ((σ.symm t).val + 1)
  be := chC f (k + 1)
  v0 := snt f (k + 2) 0
  v1 := snt f (k + 2) 1
  rows := a.rows ++ [⟨fun i => rowF k wv wc (fun j => chC f (j + 1)) i + chC f 0 * a.mf i,
    finC k (fun j => a.pt.getD (σ j).val 0) (snt f 0 0 + chC f 0 * a.tg) f.tail -
      chC f 0 * (snt f (k + 2) 0 * snt f (k + 2) 1)⟩]

def stepLine (c0 c1 : J) (o : AccO E J) (f : List (RV E)) : Acc E J where
  pt := o.pt ++ [chC f 0]
  mf := fun i => o.be * (one c0 (1 - chC f 0) i + one c1 (chC f 0) i)
  tg := (1 - chC f 0) * o.v0 + chC f 0 * o.v1
  rows := o.rows

theorem rowF_congr : ∀ (k : ℕ) (wv : ℕ → Fin 2 → J) (wc : J) (c c' : ℕ → E), (∀ j ≤ k, c j = c' j) →
    rowF k wv wc c = rowF k wv wc c'
  | 0, wv, wc, c, c', h => by
    funext i
    show one _ (c 0) i + one _ (c 0 ^ 2) i + _ = one _ (c' 0) i + one _ (c' 0 ^ 2) i + _
    rw [h 0 (Nat.le_refl 0)]
  | k + 1, wv, wc, c, c', h => by
    funext i
    show one _ (c 0) i + one _ (c 0 ^ 2) i + rowF k _ wc (fun j => c (j + 1)) i =
      one _ (c' 0) i + one _ (c' 0 ^ 2) i + rowF k _ wc (fun j => c' (j + 1)) i
    rw [h 0 (Nat.zero_le _), rowF_congr k _ wc (fun j => c (j + 1)) (fun j => c' (j + 1))
      fun j hj => h (j + 1) (Nat.succ_le_succ hj)]

end

/-- The orders and the places of a tree, as plain data. -/
structure TreeD (J : Type) (g : ℕ) where
  sg : (l : ℕ) → Equiv.Perm (Fin (g + l))
  wv : ℕ → ℕ → Fin 2 → J
  wc : ℕ → J
  c : ℕ → Bool → J

def fmLev (k : ℕ) : List Fm := fmSum k ++ [⟨0, 1, false⟩]

def fmT (g : ℕ) : ℕ → List Fm
  | 0 => fmLev (g + 0)
  | n + 1 => fmT g n ++ fmLev (g + (n + 1))

section
variable {E J S₀ : Type} [Field E] [DecidableEq J] {g : ℕ} (P : TreeD J g)

def levStep (l : ℕ) : S₀ × Acc E J → List (RV E) → S₀ × Acc E J :=
  seqRun (fmSum (g + l)).length (fun s f => (s.1, stepSum (g + l) (P.sg l) (P.wv l) (P.wc l) s.2 f))
    fun s f => (s.1, stepLine (P.c l false) (P.c l true) s.2 f)

def treeStep : ℕ → S₀ × Acc E J → List (RV E) → S₀ × Acc E J
  | 0 => levStep P 0
  | n + 1 => seqRun (fmT g n).length (treeStep n) (levStep P (n + 1))

end

section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] {Ex : ExtSpec}

/-- The sumcheck of a level, beside readings of its state. -/
noncomputable def mkAbs (St J : Type) [Fintype J] [DecidableEq J] (k : ℕ) (z : St → Fin k → E)
    (F : (st : St) → (J → E) → Bool → HPt (pVars (List.replicate k (pfCube E 2)) (pdEqs E 2 k (z
        st))) → E)
    (sl : St → J → E) (w : PIdx (lk E k) → J) (c : Bool → J) {S₀ : Type} (root : St → S₀)
    (pnt : St → Fin k → E) (σ : Equiv.Perm (Fin k)) (hz : ∀ s j, z s j = pnt s (σ j))
    (rows : St → List (Row E J)) (gam : (mkLev St J k z F sl w c).par.Out → Fin k → E)
    (hg : ∀ o t, gam o t = ppGet (lk E k) o.pt (σ.symm t).val)
    (rowB : (st : St) → Empty → HPt ((mkLev St J k z F sl w c).par.vars st) → J → E) :
    Abs ((SK₀ E Ex).full (mkLev St J k z F sl w c).par) (fmSum k)
      (fun x => (root x.2, (⟨List.ofFn (pnt x.2), pushJ (id : J → J) (sl x.2), x.1, rows x.2⟩ : Acc
          E J)))
      (fun o => (root o.st, (⟨List.ofFn (gam o),
        (mkLev St J k z F sl w c).lst o.st ((mkLev St J k z F sl w c).par.hp o.st o.pt),
        o.vals false, o.vals true,
        rows o.st ++ [⟨pushJ (id : J → J) ((mkLev St J k z F sl w c).par.slU rowB o),
          (mkLev St J k z F sl w c).par.tU o⟩]⟩ : AccO E J)))
      (fun s f => (s.1, stepSum k σ (fun r t => w (nmV E k r t)) (w (nmC E k)) s.2 f)) where
  run := fun x f => mkV St J k z F sl w c x ((rdMk St J k z F sl w c).mk f)
  runs := (Runs.ofOut (b := (SK₀ E Ex).full (mkLev St J k z F sl w c).par) (rdMk St J k z F sl w c)
    (mkV St J k z F sl w c) (SK₀_out Ex _ (mk_eq0 St J k z F sl w c))).fmEq (fms_mk St J k z F sl w
        c)
  abs := fun x f hf => by
    have hv : (rdMk St J k z F sl w c).view ((rdMk St J k z F sl w c).mk f) = f :=
      RdS.view_mk _ f (by rw [fms_mk]; exact hf)
    generalize (rdMk St J k z F sl w c).mk f = τ at hv
    have hpt : ∀ j ≤ k, ppGet (lk E k) (mkV St J k z F sl w c x τ).pt j = chC f (j + 1) := fun j
        hj => by
      rw [mk_pt St J k z F sl w c x τ j hj, hv]
    have heps : (mkV St J k z F sl w c x τ).eps = chC f 0 := by rw [mk_eps, hv]
    have hv0 : (mkV St J k z F sl w c x τ).vals false = snt f (k + 2) 0 := by
      rw [mk_vals, hv]; rfl
    have hv1 : (mkV St J k z F sl w c x τ).vals true = snt f (k + 2) 1 := by
      rw [mk_vals, hv]; rfl
    have hfin : (mkV St J k z F sl w c x τ).fin =
        finC k (fun j => (List.ofFn (pnt x.2)).getD (σ j).val 0) (snt f 0 0 + chC f 0 * x.1)
            f.tail := by
      rw [mk_fin, hv]
      congr 1
      funext j
      rw [hz, getD_ofFn (pnt x.2) (σ j)]
    refine Prod.ext rfl ?_
    show (⟨_, _, _, _, _⟩ : AccO E J) = ⟨_, _, _, _, _⟩
    congr 1
    · exact congrArg List.ofFn (funext fun t => (hg _ t).trans (hpt _ (Nat.le_of_lt (σ.symm t).2)))
    · exact (mk_lst St J k z F sl w c _).trans (hpt k (Nat.le_refl k))
    · refine congrArg (fun r => rows x.2 ++ [r]) ?_
      rw [mk_row, mk_tU, heps, hv0, hv1, hfin, pushJ_id]
      refine congrArg₂ Row.mk (funext fun i => ?_) rfl
      rw [rowF_congr k _ _ _ (fun j => chC f (j + 1)) hpt]
      rfl

end

/-! ### the levels of a tree with orders -/
section
variable {E : Type} [Field E]

theorem chC_zero (f : List (RV E)) : chC f 0 = (f.headD ([], [])).2.headD 0 := by
  cases f <;> rfl

theorem ofFn_snoc {n : ℕ} (g : Fin n → E) (a : E) :
    List.ofFn (Fin.snoc g a : Fin (n + 1) → E) = List.ofFn g ++ [a] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

end

section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] {Ex : ExtSpec} (D : TreeP E)
  [DecidableEq D.J] {S₀ : Type} (ρ : (D.lv 0).T.St → S₀)

/-- the orders and places of D as plain data -/
def treeD : TreeD D.J D.g where
  sg := D.sg
  wv := fun l r t => D.wAt l (nmV E (D.g + l) r t)
  wc := fun l => D.wAt l (nmC E (D.g + l))
  c := D.cAt

/-- what is read off the state of level l; off the output of its sumcheck -/
noncomputable def accL (l : ℕ) (x : E × (D.lv l).T.St) : S₀ × Acc E D.J :=
  (ρ (D.root l x.2), ⟨List.ofFn ((D.lv l).pnt x.2), pushJ (D.lv l).toJ ((D.lv l).T.slS x.2), x.1,
    (D.rowsAt l x.2).reverse⟩)
noncomputable def accO (l : ℕ) (o : (D.lv l).T.par.Out) : S₀ × AccO E D.J :=
  (ρ (D.root l o.st), ⟨List.ofFn ((D.lv l).gam o),
    (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt), o.vals ((D.lv l).two false),
    o.vals ((D.lv l).two true), (D.rowsAt l o.st).reverse ++ [D.rowU l o]⟩)

theorem cAt_eq (l : ℕ) (b : Bool) : (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two b)) = D.cAt l b := by
  cases l <;> rfl

/-- The sumcheck of level l. -/
noncomputable def sumAbs : (l : ℕ) → Abs ((SK₀ E Ex).full (D.lv l).T.par) (fmSum (D.g + l))
    (accL D ρ l) (accO D ρ l)
    (fun s f => (s.1, stepSum (D.g + l) (D.sg l) ((treeD D).wv l) ((treeD D).wc l) s.2 f))
  | 0 =>
    mkAbs (D.St0 × (Fin (D.g + 0) → E)) D.J (D.g + 0) D.z0 _ (fun s => D.inc0 s.1 s.2) (D.wAt 0)
      (D.cAt 0) (fun s => ρ s) (fun s => s.2) (D.sg 0) (fun _ _ => rfl) (fun _ => [])
      (D.lv 0).gam (fun o t => b2_point D 0 o t) (fun _ b _ _ => ((D.emB 0).false b).elim)
  | l + 1 =>
    mkAbs ((D.lv l).T.par.Out × E) D.J (D.g + l + 1) (D.cube l).ptS _ (D.cube l).next.slS
      (D.wAt (l + 1)) (D.cAt (l + 1)) (fun s => ρ (D.root (l + 1) s)) (fun s => (D.cube l).pt s)
      (D.sg (l + 1)) (fun _ _ => rfl) (fun s => (D.rowsAt (l + 1) s).reverse)
      (D.lv (l + 1)).gam (fun o t => b2_point D (l + 1) o t)
      (fun _ b _ _ => ((D.emB (l + 1)).false b).elim)

/-- The line step behind level l. -/
noncomputable def lineAbs (l : ℕ) : Abs (lineK Ex D l) [⟨0, 1, false⟩] (accO D ρ l) (accL D ρ (l +
    1))
    (fun s f => (s.1, stepLine (D.cAt l false) (D.cAt l true) s.2 f)) where
  run := fun o f => (D.cube l).toLine.toIn.nxX o ((f.headD ([], [])).2.headD 0)
  runs := Runs.draw (E := E) (D := E) (fun o (r : E) => (D.cube l).toLine.toIn.nxX o r) 1 rdE
    (fun l => l.headD 0) fun _ => rfl
  abs := fun o f _ => by
    generalize hr : (f.headD ([], [])).2.headD 0 = r
    have hc : chC f 0 = r := (chC_zero f).trans hr
    refine Prod.ext rfl ?_
    show (⟨_, _, _, _⟩ : Acc E D.J) = ⟨_, _, _, _⟩
    congr 1
    · rw [hc]
      exact ofFn_snoc ((D.lv l).gam o) r
    · rw [hc]
      refine (pushJ_id (J := D.J) _).trans (funext fun (i : D.J) => ?_)
      show (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt) *
        (@ite E (i = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false))) (Classical.propDecidable _)
            (1 - r) 0 +
          @ite E (i = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true))) (Classical.propDecidable _)
            r 0) = _
      rw [ite_one' (J := D.J), ite_one' (J := D.J), cAt_eq, cAt_eq]
      rfl
    · rw [hc]
      show ∑ b : Bool, (if b then r else 1 - r) * o.vals ((D.lv l).two b) = _
      rw [Fintype.sum_bool]
      exact add_comm _ _
    · exact List.reverse_cons

/-- Level l. -/
noncomputable def levAbs (l : ℕ) : Abs (levK D (SK₀ E Ex) l) (fmLev (D.g + l)) (accL D ρ l)
    (accL D ρ (l + 1)) (levStep (treeD D) l) :=
  (sumAbs D ρ l).seq (lineAbs D ρ l)

/-- The levels 0 .. n. -/
noncomputable def treeAbs : (n : ℕ) → Abs (treeK D (SK₀ E Ex) n) (fmT D.g n) (accL D ρ 0)
    (accL D ρ (n + 1)) (treeStep (treeD D) n)
  | 0 => levAbs D ρ 0
  | n + 1 => (treeAbs n).seq (levAbs D ρ (n + 1))

end
end Lev
end Lk6
