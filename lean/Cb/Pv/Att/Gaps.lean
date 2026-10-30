-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/Gaps.lean: the laws on the letters of an attention sub-proof's own rounds (`Tail.Laws`,
Cb/Pv/Att/Own.lean) from equations between the letters.

Definitions, statements and proofs. In Cb/Pv/Att/Own.lean what is claimed before each of the five
rounds that draw is a letter, and a bound on the bad draws is a premise. Here these claims are made
of gaps: elements of E that are 0 if and only if a claim holds. Before a draw of one element: each
of n gaps is 0. Behind it: the next sumcheck's gap (at the value products: the two sumchecks' gaps
together) is, where the stage's linear claims L hold, the batch of the n gaps by the powers of the
element drawn. That is an equation between letters. Before the draw of the point: two families of
vectors on cubes vanish. Behind it: their extensions vanish, the first family's at the point's first
coordinates, the second's at the others.

Main names:
  `S.tot`, `S.gap`, `SumL.gap_iff`: a sumcheck's sum with its incoming form; that less the target;
    the sum claim says that the gap is 0. `S.eGap`, `SumL.eGap_iff`: the same for the claim on an
    end value.
  `law_powS`: `law_pow` for a round that sends scalars. `law_pt2`: the bound (a + b) |E|^(a + b - 1)
    on the bad draws of a point of a + b coordinates, from `cnt_badPtFam` and `zero_of_pt_fam`
    (Cb/G6/Johnson/Layers/Rounds.lean).
  `TailG E M X`: the letters. The six sumchecks; `gV`: the two gaps before the draw for the value
    products; `d1`, `d2`: the two families, of np vectors each, on cubes of g1 and g2 variables;
    `h1`, `h2`: their extensions at the point drawn; `lF`, `fF`: what is claimed of the pairs'
    scalars, and the np gaps that the score's sumcheck batches; `iB`: the end values of the score's
    sumcheck that are not owed at the end: the next sumcheck's claim gives them. The equations:
    `eV`, `e1`, `e2`, `eF`, `eF1`, `eD`, `eH`.
  `T.toTail`: the letters of Cb/Pv/Att/Own.lean. `TailG.laws`: `T.toTail.Laws`, without a premise
    (the equations are fields of T).
  `attOwnG_knowAt`: `attOwn_knowAt` for score units and a `TailG`, without a premise (the equations
    are fields of T).

Limits: those of Cb/Pv/Att/Own.lean. The seven equations are fields of the record: whoever gives a
value proves them. That the gaps at a value say what the programs' claims say is not said here.
-/
import Cb.Pv.Att.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-! ### Gaps of a sumcheck's claims -/

namespace SumL
variable {X : Type} (S : SumL E M X)

/-- The statement before the sumcheck, inside a statement behind it. -/
abbrev pre (b : S.Nx) : X := b.1.1

/-- The sum over the cube, with the incoming form. -/
def tot (st : S.T.St) (m : M) : E :=
  ∑ b : Fin S.T.nv → Bool,
      S.T.S st (Alg.corner b) (fun a => S.T.map st (S.msg m) a (Alg.corner b)) +
    ∑ j, S.T.inc st j * S.msg m j

/-- That, less the target. -/
def gap (x : X) (r : Fin S.n → E) (m : M) : E := S.tot (S.cl x r).2 m - (S.cl x r).1

theorem gap_iff (x : X) (r : Fin S.n → E) (m : M) :
    S.T.our.par.SumHolds (S.cl x r) (S.msg m) ↔ S.gap x r m = 0 :=
  (plain_sum S.T (S.cl x r) (S.msg m)).trans sub_eq_zero.symm

/-- The masked map's value at the point, less the end value. -/
noncomputable def eGap (b : S.Nx) (m : M) (a : S.T.A) : E :=
  S.T.map b.2.st (S.msg m) a
      (ldPartFn S.T.nv S.T.deg S.T.dat (S.T.our.ini b.2.st (S.T.our.par.hp b.2.st b.2.pt))) +
    S.msg m (S.T.cAt a) * S.T.our.lst b.2.st (S.T.our.par.hp b.2.st b.2.pt) - b.2.vals a

theorem eGap_iff (b : S.Nx) (m : M) (a : S.T.A) :
    S.T.our.par.EHolds b.2 (S.msg m) a ↔ S.eGap b m a = 0 :=
  (plain_val S.T b.2 (S.msg m) a).trans sub_eq_zero.symm

end SumL

/-! ### Bounds on bad draws -/

/-- `law_pow` for a round that sends scalars before the draw. -/
theorem law_powS {X : Type} (k n : ℕ) (g : X → (Fin k → E) → M → Fin n → E) (Q P : X → M → Prop)
    (L : X → (Fin k → E) → M → Prop) (T : (X × (Fin k → E)) × E → M → Prop)
    (hP : ∀ x s m, L x s m → (∀ b, g x s m b = 0) → Q x m → P x m)
    (hT : ∀ x s β m, T ((x, s), β) m → ∑ b : Fin n, β ^ (b : ℕ) * g x s m b = 0 ∧ Q x m)
    (x : X) (m : M) (h : ¬ P x m) (s : Fin k → E) (hL : L x s m) :
    cnt (fun β : E => T ((x, s), β) m) ≤ n - 1 := by
  refine le_trans (cnt_mono fun β hβ => ?_) (cnt_badPow (g x s m))
  obtain ⟨h1, h2⟩ := hT x s β m hβ
  exact ⟨fun h0 => h (hP x s m hL (fun b => congrFun h0 b) h2), h1⟩

/-- A point of a + b coordinates as a pair of points. -/
def cutPt (a b : ℕ) (p : Fin (a + b) → E) : (Fin a → E) × (Fin b → E) :=
  (fun i => p (Fin.castAdd b i), fun i => p (Fin.natAdd a i))

omit [Field E] [Fintype E] in
theorem cutPt_inj (a b : ℕ) : Function.Injective (cutPt (E := E) a b) := fun _ _ h =>
  funext fun i => Fin.addCases (fun i => congrFun (congrArg Prod.fst h) i)
    (fun i => congrFun (congrArg Prod.snd h) i) i

theorem pt_arith (q a b : ℕ) : a * q ^ (a - 1) * q ^ b ≤ (a + b) * q ^ (a + b - 1) := by
  rcases a with _ | k
  · simp
  · have e : k + 1 + b - 1 = k + b := by omega
    rw [e, Nat.add_sub_cancel, Nat.mul_assoc, ← pow_add]
    exact Nat.mul_le_mul_right _ (by omega)

/-- Two families of vectors, tested at apart coordinates of one point. -/
theorem law_pt2 {X J₁ J₂ : Type} (a b : ℕ) (d₁ : X → M → J₁ → ℕ → E) (d₂ : X → M → J₂ → ℕ → E)
    (P : X → M → Prop) (T : X × (Fin (a + b) → E) → M → Prop)
    (hP : ∀ x m, (∀ k, ∀ Y < 2 ^ a, d₁ x m k Y = 0) → (∀ k, ∀ Y < 2 ^ b, d₂ x m k Y = 0) → P x m)
    (hT : ∀ x p m, T (x, p) m →
      (∀ k, Blocks.ext a (d₁ x m k) (Blocks.nat (cutPt a b p).1) = 0) ∧
        ∀ k, Blocks.ext b (d₂ x m k) (Blocks.nat (cutPt a b p).2) = 0)
    (x : X) (m : M) (h : ¬ P x m) :
    cnt (fun p : Fin (a + b) → E => T (x, p) m) ≤ (a + b) * Fintype.card E ^ (a + b - 1) := by
  have cA : Fintype.card (Fin a → E) = Fintype.card E ^ a := by simp
  have cB : Fintype.card (Fin b → E) = Fintype.card E ^ b := by simp
  by_cases h1 : ∀ k, ∀ Y < 2 ^ a, d₁ x m k Y = 0
  · have h2 : ¬ ∀ k, ∀ Y < 2 ^ b, d₂ x m k Y = 0 := fun h2 => h (hP x m h1 h2)
    refine le_trans (cnt_le_of_inj (Q := fun c : (Fin a → E) × (Fin b → E) =>
      c.2 ∈ badPtFam b (d₂ x m)) (cutPt a b) (cutPt_inj a b) fun p hp => ?_) ?_
    · by_contra hn
      exact h2 (zero_of_pt_fam hn (hT x p m hp).2)
    · rw [cnt_snd, cA]
      refine le_trans (Nat.mul_le_mul_left _ (cnt_badPtFam b (d₂ x m))) ?_
      have := pt_arith (Fintype.card E) b a
      rw [Nat.add_comm b a] at this
      rw [Nat.mul_comm]
      exact this
  · refine le_trans (cnt_le_of_inj (Q := fun c : (Fin a → E) × (Fin b → E) =>
      c.1 ∈ badPtFam a (d₁ x m)) (cutPt a b) (cutPt_inj a b) fun p hp => ?_) ?_
    · by_contra hn
      exact h1 (zero_of_pt_fam hn (hT x p m hp).1)
    · rw [cnt_fst, cB]
      exact le_trans (Nat.mul_le_mul_right _ (cnt_badPtFam a (d₁ x m)))
        (pt_arith (Fintype.card E) a b)

/-! ### The letters, with the claims before the draws made of gaps -/

/-- The letters of the eleven stages behind the score units. -/
structure TailG (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the denominator times the output -/
  sE : SumL E M X
  /-- the two gaps before the draw for the value products -/
  gV : sE.Nx → M → Fin 2 → E
  /-- the pairs; the variables of the two cubes; the two families -/
  np : ℕ
  g1 : ℕ
  g2 : ℕ
  d1 : sE.Nx → M → Fin np → ℕ → E
  d2 : sE.Nx → M → Fin np → ℕ → E
  /-- the value product below the diagonal, and on it -/
  sVM : SumL E M (sE.Nx × E)
  sVD : SumL E M sVM.Nx
  eV : ∀ x β r o r' m, sVM.L (x, β) r m → sVD.L (((x, β), r), o) r' m →
    sVM.gap (x, β) r m + sVD.gap (((x, β), r), o) r' m = gV x m 0 + β * gV x m 1
  /-- the families' extensions at the point drawn -/
  h1 : sVD.Nx × (Fin (g1 + g2) → E) → M → Fin np → E
  h2 : sVD.Nx × (Fin (g1 + g2) → E) → M → Fin np → E
  e1 : ∀ y p m i, h1 (y, p) m i =
    Blocks.ext g1 (d1 (sVM.pre (sVD.pre y)).1 m i) (Blocks.nat (cutPt g1 g2 p).1)
  e2 : ∀ y p m i, h2 (y, p) m i =
    Blocks.ext g2 (d2 (sVM.pre (sVD.pre y)).1 m i) (Blocks.nat (cutPt g1 g2 p).2)
  /-- what is claimed of the pairs' scalars; the gaps that the score's sumcheck batches -/
  lF : sVD.Nx × (Fin (g1 + g2) → E) → (Fin np → E) → M → Prop
  fF : sVD.Nx × (Fin (g1 + g2) → E) → (Fin np → E) → M → Fin np → E
  eF1 : ∀ z s m i, lF z s m → fF z s m i = h1 z m i
  /-- the score at the index -/
  sF : SumL E M (((sVD.Nx × (Fin (g1 + g2) → E)) × (Fin np → E)) × E)
  eF : ∀ z s β r m, sF.L ((z, s), β) r m →
    sF.gap ((z, s), β) r m = ∑ i : Fin np, β ^ (i : ℕ) * fF z s m i
  /-- its end values that the next sumcheck's claim gives -/
  iB : Fin np → sF.T.A
  /-- the key at the index -/
  sD : SumL E M (sF.Nx × E)
  eD : ∀ b β r m, sD.L (b, β) r m →
    sD.gap (b, β) r m = ∑ i : Fin np, β ^ (i : ℕ) * sF.eGap b m (iB i)
  /-- the bits -/
  sH : SumL E M (sD.Nx × E)
  eH : ∀ c β r m, sH.L (c, β) r m →
    sH.gap (c, β) r m = ∑ i : Fin np, β ^ (i : ℕ) * h2 (sF.pre (sD.pre c).1).1.1 m i

namespace TailG
variable {X : Type} (T : TailG E M X)

/-- Both families vanish on their cubes. -/
def Zs (x : T.sE.Nx) (m : M) : Prop :=
  (∀ i, ∀ Y < 2 ^ T.g1, T.d1 x m i Y = 0) ∧ ∀ i, ∀ Y < 2 ^ T.g2, T.d2 x m i Y = 0

/-- The letters of Cb/Pv/Att/Own.lean. -/
def toTail : Tail E M X where
  sE := T.sE
  pV := fun x m => (∀ i, T.gV x m i = 0) ∧ T.Zs x m
  sVM := T.sVM
  sVD := T.sVD
  nz := T.g1 + T.g2
  eZ := (T.g1 + T.g2) * Fintype.card E ^ (T.g1 + T.g2 - 1)
  pZ := fun y m => T.Zs (T.sVM.pre (T.sVD.pre y)).1 m
  np := T.np
  pF := fun z m => (∀ i, T.h1 z m i = 0) ∧ ∀ i, T.h2 z m i = 0
  lF := T.lF
  sF := T.sF
  owF := fun b m => T.sF.T.our.par.UHolds b.2 (T.sF.msg m) ∧
    ∀ a, (∀ i, a ≠ T.iB i) → T.sF.T.our.par.EHolds b.2 (T.sF.msg m) a
  pD := fun b m => (∀ i, T.sF.eGap b m (T.iB i) = 0) ∧ ∀ i, T.h2 (T.sF.pre b).1.1 m i = 0
  sD := T.sD
  pH := fun c m => ∀ i, T.h2 (T.sF.pre (T.sD.pre c).1).1.1 m i = 0
  sH := T.sH

theorem laws : T.toTail.Laws where
  cH := law_pow T.np (fun c m i => T.h2 (T.sF.pre (T.sD.pre c).1).1.1 m i) (fun _ _ => True) _ _
    (fun _ _ h _ => h) fun c β m h => by
      obtain ⟨r, hL, hS, _⟩ := h
      exact ⟨(T.eH c β r m hL).symm.trans ((T.sH.gap_iff (c, β) r m).1 hS), trivial⟩
  cD := law_pow T.np (fun b m i => T.sF.eGap b m (T.iB i))
    (fun b m => ∀ i, T.h2 (T.sF.pre b).1.1 m i = 0) _ _ (fun _ _ h hQ => ⟨h, hQ⟩)
    fun b β m h => by
      obtain ⟨r, hL, hS, _, hH⟩ := h
      exact ⟨(T.eD b β r m hL).symm.trans ((T.sD.gap_iff (b, β) r m).1 hS), hH⟩
  oF := fun b m h1 h2 => ⟨h1.1, fun a => by
    by_cases ha : ∃ i, a = T.iB i
    · obtain ⟨i, rfl⟩ := ha
      exact (T.sF.eGap_iff b m (T.iB i)).2 (h2.1 i)
    · exact h1.2 a fun i hi => ha ⟨i, hi⟩⟩
  cF := law_powS T.np T.np T.fF (fun z m => ∀ i, T.h2 z m i = 0) _ T.lF _
    (fun z s m hL h hQ => ⟨fun i => (T.eF1 z s m i hL).symm.trans (h i), hQ⟩)
    fun z s β m h => by
      obtain ⟨r, hL, hS, _, hD⟩ := h
      exact ⟨(T.eF z s β r m hL).symm.trans ((T.sF.gap_iff ((z, s), β) r m).1 hS), hD.2⟩
  cZ := law_pt2 T.g1 T.g2 (fun y m => T.d1 (T.sVM.pre (T.sVD.pre y)).1 m)
    (fun y m => T.d2 (T.sVM.pre (T.sVD.pre y)).1 m) _ _ (fun _ _ h1 h2 => ⟨h1, h2⟩)
    fun y p m h => ⟨fun i => (T.e1 y p m i).symm.trans (h.1 i),
      fun i => (T.e2 y p m i).symm.trans (h.2 i)⟩
  cV := law_pow 2 T.gV T.Zs _ _ (fun _ _ h hQ => ⟨h, hQ⟩) fun x β m h => by
    obtain ⟨r, hL, hS, o, r', hL', hS', _, hZ⟩ := h
    refine ⟨?_, hZ⟩
    have e := T.eV x β r o r' m hL hL'
    rw [(T.sVM.gap_iff (x, β) r m).1 hS, (T.sVD.gap_iff (((x, β), r), o) r' m).1 hS',
      add_zero] at e
    rw [Fin.sum_univ_two]
    simpa using e.symm

end TailG

/-- Knowledge soundness of an attention sub-proof's own rounds, without a premise. -/
theorem attOwnG_knowAt {X Kc X0 Wp : Type} (units : List (SumL E M (Seen E X)))
    (T : TailG E M (Seen E X)) (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt ((AttOwn.mk units T.toTail).ch.R Ex)
      (jt A0 pr fun x m => Dn x m ∧ (AttOwn.mk units T.toTail).ch.Todo x m)
      (jt A0 (fun e => pr ((AttOwn.mk units T.toTail).ch.back e))
        ((AttOwn.mk units T.toTail).ch.Last Dn))
      (fun _ _ _ wp => wp) ((AttOwn.mk units T.toTail).ch.eps Ex) :=
  attOwn_knowAt (AttOwn.mk units T.toTail) T.laws Ex A0 pr Dn

end Cb.Pv.Att
