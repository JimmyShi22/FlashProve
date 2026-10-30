-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LevRunB.lean: one level of a product tree at the short sumcheck, over flat
transcripts:
the sumcheck of a level as a value `mkLev`, what its verifier's output holds, and a small frame to
carry
«the output, seen through a reading, is a plain function of the input, seen through a reading, and
of the flat transcript» along blocks in a row.

States:
  `Abs b fm α α' step`: the block b rejects nothing and has the formats fm (Flat.lean's `Flat.Runs`,
                  at some function run), and on flat lists that fit α' (run x f) = step (α x) f.
     Rules: `Abs.seq` (step := seqRun), `Abs.preM`, `Abs.postM`, `Abs.mapIn`, `Abs.mapOut`;
     `Abs.toRuns`: with readings that are the identity up to plain maps: `Flat.Runs` at a plain
     function.
  `mkLev`: the sumcheck on k equality-weighted variables at z st and Y, summand the product of two
                  shown values.
  `mk_eq0`; `mk_eps`, `mk_fin`, `mk_pt`, `mk_vals`, `mk_st`: the fields of the short verifier's
                  output at the transcript that a flat list spells.
  `mk_row`, `mk_tU`, `mk_lst`: the row's form and target; the last coordinate.
Under: nothing. It names no honest side and imports no file of the port.

-/
import Cb.Pv.KeyLookup.LevRunA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Lev
open Cb Cb.LdLkp Cb.LdLkp.Kn Iop IOR Hiop Prob Johnson.L5.Layers Flat

/-! ### the frame -/
section
variable {E : Type} [DecidableEq E] [Zero E] {Ex : ExtSpec}

/-- The block's output, seen through α', is step of its input, seen through α, and of the flat
transcript. -/
structure Abs {X X' S S' : Type} (b : BkK X X' Ex) (fm : List Fm) (α : X → S) (α' : X' → S')
    (step : S → List (RV E) → S') where
  run : X → List (RV E) → X'
  runs : Runs b fm run
  abs : ∀ x f, fitsAll fm f = true → α' (run x f) = step (α x) f

namespace Abs
variable {X X' X'' S S' S'' : Type}

def seq {a : BkK X X' Ex} {b : BkK X' X'' Ex} {fa fb : List Fm} {α : X → S} {α' : X' → S'} {α'' :
    X'' → S''}
    {sa : S → List (RV E) → S'} {sb : S' → List (RV E) → S''} (ha : Abs a fa α α' sa) (hb : Abs b fb
        α' α'' sb) :
    Abs (a.seq b) (fa ++ fb) α α'' (seqRun fa.length sa sb) where
  run := seqRun fa.length ha.run hb.run
  runs := ha.runs.seq hb.runs
  abs := fun x f hf => by
    obtain ⟨h1, h2⟩ := fitsAll_app fa fb f hf
    show α'' (hb.run (ha.run x (f.take fa.length)) (f.drop fa.length)) =
      sb (sa (α x) (f.take fa.length)) (f.drop fa.length)
    rw [hb.abs _ _ h2, ha.abs _ _ h1]

def preM {X₀ S₀ : Type} {b : BkK X X' Ex} {fm : List Fm} {α : X → S} {α' : X' → S'}
    {step : S → List (RV E) → S'} (h : Abs b fm α α' step) (φ : X₀ → X) (α₀ : X₀ → S₀) (ψ : S₀ → S)
    (e : ∀ x, α (φ x) = ψ (α₀ x)) : Abs (b.preM φ) fm α₀ α' (fun s f => step (ψ s) f) where
  run := fun x f => h.run (φ x) f
  runs := h.runs.preM φ
  abs := fun x f hf => by rw [h.abs _ _ hf, e]

def postM {X₂ S₂ : Type} {b : BkK X X' Ex} {fm : List Fm} {α : X → S} {α' : X' → S'}
    {step : S → List (RV E) → S'} (h : Abs b fm α α' step) (φ : X' → X₂) (α₂ : X₂ → S₂) (ψ : S' →
        S₂)
    (e : ∀ x, α₂ (φ x) = ψ (α' x)) : Abs (b.postM φ) fm α α₂ (fun s f => ψ (step s f)) where
  run := fun x f => φ (h.run x f)
  runs := h.runs.postM φ
  abs := fun x f hf => by rw [e, h.abs _ _ hf]

/-- another reading of the output, a plain map of the first -/
def mapOut {S₂ : Type} {b : BkK X X' Ex} {fm : List Fm} {α : X → S} {α' : X' → S'}
    {step : S → List (RV E) → S'} (h : Abs b fm α α' step) (α₂ : X' → S₂) (ψ : S' → S₂)
    (e : ∀ x, α₂ x = ψ (α' x)) : Abs b fm α α₂ (fun s f => ψ (step s f)) where
  run := h.run
  runs := h.runs
  abs := fun x f hf => by rw [e, h.abs _ _ hf]

/-- another reading of the input, of which the first is a plain map -/
def mapIn {S₀ : Type} {b : BkK X X' Ex} {fm : List Fm} {α : X → S} {α' : X' → S'}
    {step : S → List (RV E) → S'} (h : Abs b fm α α' step) (α₀ : X → S₀) (ψ : S₀ → S)
    (e : ∀ x, α x = ψ (α₀ x)) : Abs b fm α₀ α' (fun s f => step (ψ s) f) where
  run := h.run
  runs := h.runs
  abs := fun x f hf => by rw [h.abs _ _ hf, e]

/-- the same, with the step written otherwise -/
def stepEq {b : BkK X X' Ex} {fm : List Fm} {α : X → S} {α' : X' → S'} {step step' : S → List (RV
    E) → S'}
    (h : Abs b fm α α' step) (e : ∀ s f, step s f = step' s f) : Abs b fm α α' step' where
  run := h.run
  runs := h.runs
  abs := fun x f hf => (h.abs x f hf).trans (e _ _)

def fmEq {b : BkK X X' Ex} {fm fm' : List Fm} {α : X → S} {α' : X' → S'} {step : S → List (RV E) →
    S'}
    (h : Abs b fm α α' step) (e : fm = fm') : Abs b fm' α α' step where
  run := h.run
  runs := h.runs.fmEq e
  abs := fun x f hf => h.abs x f (by rw [e]; exact hf)

/-- With the identity as both readings: the block runs the plain function. -/
def toRuns {b : BkK X X' Ex} {fm : List Fm} {step : X → List (RV E) → X'} (h : Abs b fm id id step)
    :
    Runs b fm step := h.runs.congr h.abs

end Abs
end

/-! ### the sumcheck of a level -/
section
variable {E : Type} [Field E] [Fintype E]

/-- k equality-weighted variables at z st, then Y; the summand is the product of two shown values.
-/
noncomputable def mkLev (St J : Type) [Fintype J] (k : ℕ) (z : St → Fin k → E)
    (F : (st : St) → (J → E) → Bool → HPt (pVars (List.replicate k (pfCube E 2)) (pdEqs E 2 k (z
        st))) → E)
    (sl : St → J → E) (w : PIdx (lk E k) → J) (c : Bool → J) : PscOur E where
  St := St
  J := J
  fmt := List.replicate k (pfCube E 2)
  dat := fun st => pdEqs E 2 k (z st)
  A := Bool
  B := Empty
  F := F
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false * v true
  S1 := fun _ _ _ b => b.elim
  DY := 2
  slS := sl
  wAt := w
  cAt := c

/-- false is number 0, true number 1 -/
def e2 : Bool ≃ Fin 2 := finTwoEquiv.symm

omit [Fintype E] in
theorem pushJ_id {J : Type} [Fintype J] (c : J → E) : pushJ (id : J → J) c = c := by
  funext j
  exact (Finset.sum_eq_single j (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ j) h)).trans (if_pos rfl)

theorem last_get : ∀ (k : ℕ) (z : Fin k → E) (γ : PPt (lk E k)),
    hLast (List.replicate k (pfCube E 2)) (pdEqs E 2 k z) (pDummy E 2) (pDummyD E 2)
      (pH (lk E k) (dk E k z) γ) = ppGet (lk E k) γ k
  | 0, _, _ => rfl
  | k + 1, z, γ => last_get k (fun i => z i.succ) γ.2

variable (St J : Type) [Fintype J] (k : ℕ) (z : St → Fin k → E)
  (F : (st : St) → (J → E) → Bool → HPt (pVars (List.replicate k (pfCube E 2)) (pdEqs E 2 k (z
      st))) → E)
  (sl : St → J → E) (w : PIdx (lk E k) → J) (c : Bool → J)

theorem mk_eq0 : TWhole.Eq0 (mkLev St J k z F sl w c).par :=
  TWhole.our_eq0 (mkLev St J k z F sl w c) fun st v hv => by
    have e : (mkLev St J k z F sl w c).vars st =
        List.ofFn fun j : Fin k => (pfCube E 2).var (pdEq E 2 (z st j)) := pVars_eqsB 2 k (z st)
    rw [e] at hv
    simp only [List.mem_ofFn] at hv
    obtain ⟨j, rfl⟩ := hv
    exact TWhole.mon0_eq 2 _

theorem mk_lst (o : (mkLev St J k z F sl w c).par.Out) :
    (mkLev St J k z F sl w c).lst o.st ((mkLev St J k z F sl w c).par.hp o.st o.pt) = ppGet (lk E k)
        o.pt k :=
  last_get k (z o.st) o.pt

theorem mk_tU (o : (mkLev St J k z F sl w c).par.Out) :
    (mkLev St J k z F sl w c).par.tU o = o.fin - o.eps * (o.vals false * o.vals true) := rfl

theorem mk_row [DecidableEq J]
    (rowB : (st : St) → Empty → HPt ((mkLev St J k z F sl w c).par.vars st) → J → E)
    (o : (mkLev St J k z F sl w c).par.Out) :
    pushJ (id : J → J) ((mkLev St J k z F sl w c).par.slU rowB o) =
      fun j => rowF k (fun r t => w (nmV E k r t)) (w (nmC E k)) (ppGet (lk E k) o.pt) j + o.eps *
          sl o.st j := by
  refine (pushJ_id _).trans (funext fun (j : J) => ?_)
  unfold PscPar.slU
  show (∑ i, @ite E (w (pIx (lk E k) (dk E k (z o.st)) i) = j) (Classical.propDecidable _)
      (hSl (pVars (lk E k) (dk E k (z o.st))) (pH (lk E k) (dk E k (z o.st)) o.pt) i) 0) +
    o.eps * hPsi (pVars (lk E k) (dk E k (z o.st))) (pH (lk E k) (dk E k (z o.st)) o.pt) * sl o.st
        j +
    o.eps * ∑ b : Empty, _ = _
  rw [row_form, psi_one, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero, mul_one]

variable [DecidableEq E]

/-- the reader of the values' round -/
def rdB : RdS E [pRoundV E Bool] := (rdV e2, ())

/-- the readers of the level's sumcheck -/
noncomputable def rdMk : RdS E (shapeS (mkLev St J k z F sl w c).par) :=
  rdFull (mkLev St J k z F sl w c).par (fuK k) e2

/-- the formats of a sumcheck on k variables and Y with two shown values -/
def fmSum (k : ℕ) : List Fm :=
  ⟨1, 1, false⟩ :: (List.replicate k ⟨2, 1, false⟩ ++ [⟨2, 1, true⟩, ⟨2, 0, false⟩])

theorem fms_vars : ∀ k : ℕ, (rdVars (lk E k) (fuK k)).fms = List.replicate k ⟨2, 1, false⟩ ++ [⟨2,
    1, true⟩]
  | 0 => rfl
  | k + 1 => congrArg (List.cons (⟨2, 1, false⟩ : Fm)) (fms_vars k)

theorem fms_mk : (rdMk St J k z F sl w c).fms = fmSum k := by
  show (⟨1, 1, false⟩ : Fm) :: ((rdVars (lk E k) (fuK k)).app (rdB (E := E))).fms = _
  rw [RdS.fms_app, fms_vars]
  show _ = (⟨1, 1, false⟩ : Fm) :: (List.replicate k ⟨2, 1, false⟩ ++ [⟨2, 1, true⟩, ⟨2, 0, false⟩])
  rw [List.append_assoc]
  rfl

variable (x : E × St) (τ : Tr (shapeS (mkLev St J k z F sl w c).par))

/-- the short verifier's output at x, τ -/
noncomputable abbrev mkV : (mkLev St J k z F sl w c).par.Out :=
  TWhole.shortV (mkLev St J k z F sl w c).par (TWhole.F₀ (mkLev St J k z F sl w c).par) x τ

theorem mk_st : (mkV St J k z F sl w c x τ).st = x.2 := rfl

theorem mk_eps : (mkV St J k z F sl w c x τ).eps = chC ((rdMk St J k z F sl w c).view τ) 0 := by
  obtain ⟨m, ε, τ'⟩ := τ
  rfl

theorem mk_fin : (mkV St J k z F sl w c x τ).fin =
    finC k (z x.2) (snt ((rdMk St J k z F sl w c).view τ) 0 0 + chC ((rdMk St J k z F sl w c).view
        τ) 0 * x.1)
      ((rdMk St J k z F sl w c).view τ).tail := by
  obtain ⟨m, ε, τ'⟩ := τ
  exact fin_view (rdB (E := E)) k (z x.2) (m.2 + ε * x.1) τ'

theorem mk_pt (j : ℕ) (hj : j ≤ k) : ppGet (lk E k) (mkV St J k z F sl w c x τ).pt j =
    chC ((rdMk St J k z F sl w c).view τ) (j + 1) := by
  obtain ⟨m, ε, τ'⟩ := τ
  exact (ppGet_vFinT (lk E k) _ _ _ _ τ' j).trans
    (ch_view (rdB (E := E)) k τ' j hj)

theorem mk_vals (b : Bool) : (mkV St J k z F sl w c x τ).vals b =
    snt ((rdMk St J k z F sl w c).view τ) (k + 2) (e2 b).val := by
  obtain ⟨m, ε, τ'⟩ := τ
  have h := tail_view (rdB (E := E)) k (z x.2) (m.2 + ε * x.1) τ' 0
  show (TWhole.vFinT (lk E k) (dk E k (z x.2)) (TWhole.fix0 (pVars (lk E k) (dk E k (z x.2))))
      (m.2 + ε * x.1) [pRoundV E Bool] τ').2.1.2 b =
    ((((rdVars (lk E k) (fuK k)).app (rdB (E := E))).view τ').getD (k + 1) ([], [])).1.getD (e2
        b).val 0
  rw [Nat.add_zero] at h
  rw [h]
  generalize (TWhole.vFinT (lk E k) (dk E k (z x.2)) (TWhole.fix0 (pVars (lk E k) (dk E k (z x.2))))
    (m.2 + ε * x.1) [pRoundV E Bool] τ').2 = u
  obtain ⟨mv, cv, uu⟩ := u
  show mv.2 b = (List.ofFn fun i => mv.2 (e2.symm i)).getD (e2 b).val 0
  rw [getD_ofFn (fun i => mv.2 (e2.symm i)) (e2 b), Equiv.symm_apply_apply]

end
end Lev
end Lk6
