-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupStage.lean: the lookup argument as a stage (Blocks/Stage.lean), with all properties.

The lookup argument shows that committed looked-up values (keys in Lean names) are entries of public
tables: there are NT batches of 2^D keys, each with a table of 2^r entries (`LkPar.InTable`,
Blocks/LookupRel.lean). Its steps are in Blocks/LookupBlock.lean (soundness) and
Blocks/LookupHon.lean (honest prover):

  1, 2  the verifier sends α; the prover sends, masked, the product of α - key over each batch and
        products over its table with committed multiplicity bits;
  3, 4  product trees (Blocks/ProductBlock.lean) over the keys and over the table reduce these
        products to claims at random points, with a check that the multiplicity bits are bits;
  5     the degree check: the multiplicities of a batch add up to the number of its keys that are
        not padding;
  6     the root test: the products of step 2 satisfy `LkPar.Ident`.

This file composes the steps into a stage (Blocks/Stage.lean: a sub-protocol with its honest prover,
errors and simulator; other words of this library: lean/GLOSSARY.md). The verifier's part of a
statement contains the list of deferred claims (`Ledger`, Blocks/Form.lean): LIN(f), the affine form
f has the value 0, and REL, f is a sum of products of opened forms.

`Lk.props_stLookup`: under `LkPar.WF` at the characteristic p of E, `Lk.PadsOK` (no pad is used
twice) and 2 ≠ 0 in E, `Lk.stLookup` has `Stage.Props` from `Lk.c0` to `Lk.c10`. For soundness: if a
key is not in its table or a deferred claim is false (`Lk.R0` fails), then, outside the bad
challenges that the errors bound, either the verifier rejects, or afterwards a deferred claim or one
of four claims passed to the containing protocol is false (`Lk.R10` fails). The same is proved for
three phases, between which the containing protocol may place other stages: `Lk.st14` (steps 1 to
4), `Lk.st5` and `Lk.st6`. Section 6 shows that no vector is sent. Section 7 counts the deferred
claims that the honest prover's copy of the list gains; the closing of a segment needs these
numbers.

Notation:
 * `Stage` P E a b: a `Core` (a block and its honest prover) with ε: `Err B.shape`: the errors,
   round by round, as counts; `S.U`, `S.D`: sets of pads (`Set P`); see the fields' doc comment;
   `Sim`; `pBad`, `pWin`: `ℝ≥0∞` (Blocks/Stage.lean).
 * `Stage.Props` S ca cb: all properties of a stage, between the relations before and after it: the
   fields clean (`Block.Clean`), acc (`Hon.AccOn`), masked (`Hon.Masked`), keeps, prBad, prWin
   (Blocks/Stage.lean).
 * `Cut` P E a: the relations between two stages: R: the relation for soundness; Hn: the relation of
   the honest run; V: validity of the honest state (Blocks/Stage.lean).
 * `PL.plErr` e: the errors of a product layer: 2 in each round of the sumcheck, e at ζ
   (Blocks/ProductBlock.lean); `ePt` E g: g |E|^(g-1): the error of a point of g coordinates; `nzT`
   ϱ: the public check of a point: no coordinate is 0 (Blocks/LookupBlock.lean); `eXi`: see
   Blocks/LookupRel.lean.
 * D, σ, r, lp, NT: natural numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with
   2^r entries, 2^lp bits for a multiplicity; σ: the number of bits of a tree's index
   (Blocks/LookupRel.lean; σ: the head of Blocks/LookupWhole.lean).
 * gT: `LkPar.gT` = r + σ + lp: the number of variables of the leaves of the table side; Pm:
   `LkPar.Pm` = 2^lp - 1: the number of the highest plane (Blocks/LookupRel.lean).
 * `T`: `Lk.Vecs E Y`: the true vectors of a lookup argument: the keys and the multiplicity bits, as
   functions of the implicit part (Blocks/LookupBlock.lean).
 * E, Y, Pd, N: types, the arguments of `Lk`: E the field; Y the implicit part; Pd the set of places
   of pads; N the set of entries (Blocks/LookupBlock.lean).

Limits: the verifier rejects, and the randomness is in the withheld set (`Hon.withheld`,
Blocks/BlockHon.lean), if a coordinate of one of the four points sampled in `stZY`, `stT0`, `stB0`,
`stUV` is 0 (probability at most `pPt E n` for n coordinates) or a challenge of a layer of the two
product trees is 0 (at most (g + 1) / |E| for g variables; in the last layer over the keys this
applies only to the challenges that `LkPar.zf` selects). These events are public; the withheld set
holds no other. What the heads of Blocks/LookupBlock.lean and Blocks/LookupHon.lean list as not said
is not said here either.
-/
import Blocks.LookupHon
import Blocks.ProductStage
import Blocks.StageSide
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-! ## 1. The probability that a point has a coordinate 0 -/

theorem cnt_nzT_le {E : Type} [Field E] [Fintype E] [DecidableEq E] (n : ℕ) :
    cnt (fun ϱ : Fin n → E => nzT ϱ = false) ≤ Lk.ePt E n := by
  have h := Alg.count_pi_exists_le (J := Fin n) (α := E) (fun j f => f j = 0) (fun _ => 1) fun j f => by
    simp only [Function.update_self]
    exact Alg.count_eq_le_one 0
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  refine le_trans (cnt_mono fun ϱ hϱ => ?_) h
  by_contra hn
  push Not at hn
  have : nzT ϱ = true := by simpa [nzT] using hn
  rw [this] at hϱ
  exact absurd hϱ (by simp)

/-- The bound for the probability that a point of n coordinates has a coordinate 0: n |E|^(n-1) /
|E|^n. -/
def pPt (E : Type) [Fintype E] (n : ℕ) : ℝ≥0∞ :=
  (Lk.ePt E n : ℝ≥0∞) / Fintype.card (Fin n → E)

namespace Lk

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-! ## 2. Statement types, and the relations between the steps -/

/-- The statement types before the argument (`sL`) and, below, inside and after it (`sX`). -/
@[reducible] def sL (_ : Lk E Y Pd N) : Sorts := ⟨Ledger N E, Y, LkA E⟩
@[reducible] def sX (_ : Lk E Y Pd N) : Sorts := ⟨LkX N E, Y, LkA E⟩

/-- All pads of the argument. -/
def allPads : Set Pd := {p | ∃ g, L.GOK g ∧ p ∈ L.grp g}

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem grp_subset {g : Grp} (hg : L.GOK g) : L.grp g ⊆ L.allPads := fun _ hp => ⟨g, hg, hp⟩

@[reducible] def c0 : Cut Pd E L.sL := ⟨(L.R0 T), (L.Lnk0 T) L.allPads, fun _ => True⟩
@[reducible] def c1 : Cut Pd E L.sX := ⟨(L.R1 T), (L.Lnk T) L.allPads, fun _ => True⟩
@[reducible] def cK (l : ℕ) : Cut Pd E L.sX := ⟨(L.RK T) l, (L.HK T) L.allPads l, fun _ => True⟩
@[reducible] def c3 : Cut Pd E L.sX := ⟨(L.R3 T), (L.H3 T) L.allPads, fun _ => True⟩
@[reducible] def cT (l : ℕ) : Cut Pd E L.sX := ⟨(L.RT T) l, (L.HT T) L.allPads l, fun _ => True⟩
@[reducible] def c5 : Cut Pd E L.sX := ⟨(L.R5 T), (L.H5 T) L.allPads, fun _ => True⟩
@[reducible] def c6 : Cut Pd E L.sX := ⟨(L.R6 T), (L.H6 T) L.allPads, fun _ => True⟩
/-- The relations after steps 1 to 4. -/
@[reducible] def c7 : Cut Pd E L.sX := ⟨(L.R7 T), (L.H7 T) L.allPads, fun _ => True⟩
/-- The relations after step 5. -/
@[reducible] def c8 : Cut Pd E L.sX := ⟨(L.R8 T), (L.H8 T) L.allPads, fun _ => True⟩
@[reducible] def c9a : Cut Pd E L.sX := ⟨(L.R9a T), (L.H9 T) L.allPads, fun _ => True⟩
@[reducible] def c9b : Cut Pd E L.sX := ⟨(L.R9b T), (L.H9 T) L.allPads, fun _ => True⟩
@[reducible] def c9c : Cut Pd E L.sX := ⟨(L.R9c T), (L.H9c T) L.allPads, fun _ => True⟩
/-- The relations after the argument. -/
@[reducible] def c10 : Cut Pd E L.sX := ⟨(L.R10 T), (L.H10 T) L.allPads, fun _ => True⟩

/-! ## 3. The steps as stages

In the names: Al, α (step 1); ZY, the products, then a point (step 2 and the start of 3); K, Key,
Ke, the product tree over the keys (step 3); T0, T, Tab, the product tree over the table, and L, B0,
B, its leaf layer and bit layer (step 4); UV, Xi, Rs, Rec, the root test (step 6). -/

def coAl : Core Pd E L.sL L.sX := ⟨L.bAl, L.hAl⟩

def stAl : Stage Pd E L.sL L.sX :=
  ⟨L.coAl, (2 ^ L.par.D - 1, ()), ∅, ∅, simNone E, 0, 0⟩

omit [NeZero (2 : E)] in
theorem props_stAl {p : ℕ} [CharP E p] (hW : L.par.WF p) : L.stAl.Props (L.c0 T) (L.c1 T) :=
  Stage.Props.of_empty (S := L.stAl) (L.clean_bAl T hW) (L.accOn_hAl T _) L.masked_hAl
    (fun _ _ _ => trivial) rfl fun _ => rfl

def coZY : Core Pd E L.sX L.sX := ⟨L.bZY, L.hZY⟩

def stZY : Stage Pd E L.sX L.sX :=
  ⟨L.coZY, (ePt E L.par.σ, ()), L.grp .zy, L.grp .zy,
    Hon.simOne (r := L.rZY) (K := L.KZY) E id, pPt E L.par.σ, 0⟩

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem padsZY_subset : L.padsZY ⊆ L.allPads := by
  rintro p (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, π, hπ, rfl⟩)
  · exact ⟨.zy, trivial, ⟨.inl ⟨θ, hθ⟩, rfl⟩⟩
  · exact ⟨.zy, trivial, ⟨.inr (⟨θ, hθ⟩, ⟨π, hπ⟩), rfl⟩⟩

omit [NeZero (2 : E)] in
theorem props_stZY (hok : L.PadsOK) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.stZY.Props (L.c1 T) (L.cK T 0) where
  clean := (L.clean_bZY T) hnt
  acc := (L.accOn_hZY T) L.padsZY_subset
  masked := L.masked_hZY hok.zy
  keeps := fun _ _ _ => trivial
  prBad := prRho_head_le L.rZY [] (fun ϱ => nzT ϱ = false) _ (cnt_nzT_le _)
  prWin := fun _ _ => prRho_empty _ fun _ h => h

def coK (l : ℕ) : Core Pd E L.sX L.sX := ⟨L.bK l, L.hK l⟩

def stK (l : ℕ) : Stage Pd E L.sX L.sX :=
  ⟨L.coK l, (L.plK l).plErr 1, L.grp (.k l), L.grp (.k l), PL.Prover.simPl (L.plK l),
    PL.Prover.pBad (L.plK l), 0⟩

theorem props_stK (ho : L.par.OrdOK) (hok : L.PadsOK) {l : ℕ} (hl : l < L.par.D) :
    (L.stK l).Props (L.cK T l) ((L.cK T) (l + 1)) where
  clean := (L.clean_bK T) ho hl
  acc := (L.accOn_hK T) ho hl (L.grp_subset (g := .k l) hl)
  masked := L.masked_hK ho (hok.k l hl)
  keeps := fun _ _ _ => trivial
  prBad := (L.prK l).prBad_pl (ho.kOrd l)
  prWin := fun a _ => by
    show prRho ((L.prK l).pl.Win a) ≤ 0
    rw [(L.prK l).win_pl a]
    exact prRho_empty _ fun _ h => h

/-- The layers l, .., l + n - 1 of the tree over the keys: the protocol, and the other fields one by
one, so that the stage's protocol is `coKey` by definition. -/
def coKey : (n l : ℕ) → Core Pd E L.sX L.sX
  | 0, _ => Core.id _
  | n + 1, l => (L.coK l).seq (coKey n (l + 1))

def errKey : (n l : ℕ) → Err (L.coKey n l).B.shape
  | 0, _ => ()
  | n + 1, l => Err.app (s := (L.coK l).B.shape) ((L.plK l).plErr 1) (errKey n (l + 1))

def uKey : (n l : ℕ) → Set Pd
  | 0, _ => ∅
  | n + 1, l => L.grp (.k l) ∪ uKey n (l + 1)

def simKey :
    (n l : ℕ) → Rho (L.coKey n l).B.shape → PMF (Plains (L.coKey n l).B.shape)
  | 0, _ => fun _ => PMF.pure ()
  | n + 1, l => Hon.simSeq (s := (L.coK l).B.shape) (PL.Prover.simPl (L.plK l)) (simKey n (l + 1))

def pBadKey : (n l : ℕ) → ℝ≥0∞
  | 0, _ => 0
  | n + 1, l => PL.Prover.pBad (L.plK l) + pBadKey n (l + 1)

def pWinN : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => 0 + pWinN n

def stKey (n l : ℕ) : Stage Pd E L.sX L.sX :=
  ⟨L.coKey n l, L.errKey n l, L.uKey n l, L.uKey n l, L.simKey n l, L.pBadKey n l, pWinN n⟩

omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem stKey_zero (l : ℕ) : L.stKey 0 l = Stage.id _ := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem stKey_succ (n l : ℕ) : L.stKey (n + 1) l = (L.stK l).seq (L.stKey n (l + 1)) := rfl

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem mem_stKey_U {p : Pd} :
    ∀ {n l : ℕ}, p ∈ (L.stKey n l).U ↔ ∃ l', l ≤ l' ∧ l' < l + n ∧ p ∈ L.grp (.k l')
  | 0, l => ⟨fun h => absurd h (Set.notMem_empty p), fun ⟨l', h1, h2, _⟩ => by omega⟩
  | n + 1, l => by
      show p ∈ L.grp (.k l) ∪ (L.stKey n (l + 1)).U ↔ _
      rw [Set.mem_union, mem_stKey_U]
      constructor
      · rintro (h | ⟨l', h1, h2, h3⟩)
        · exact ⟨l, le_rfl, by omega, h⟩
        · exact ⟨l', by omega, by omega, h3⟩
      · rintro ⟨l', h1, h2, h3⟩
        by_cases h : l' = l
        · subst h
          exact Or.inl h3
        · exact Or.inr ⟨l', by omega, by omega, h3⟩

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem stKey_D : ∀ n l : ℕ, (L.stKey n l).D = (L.stKey n l).U
  | 0, _ => rfl
  | n + 1, l => by
      show L.grp (.k l) ∪ (L.stKey n (l + 1)).D = L.grp (.k l) ∪ (L.stKey n (l + 1)).U
      rw [stKey_D]

theorem props_stKey (ho : L.par.OrdOK) (hok : L.PadsOK) :
    ∀ n l : ℕ, l + n ≤ L.par.D → (L.stKey n l).Props (L.cK T l) ((L.cK T) (l + n))
  | 0, l, _ => Stage.props_id _
  | n + 1, l, h => by
      have hd : Disjoint (L.grp (.k l))
          (L.stKey n (l + 1)).U := Set.disjoint_left.mpr fun p hp hp' => by
        obtain ⟨l', h1, h2, h3⟩ := L.mem_stKey_U.mp hp'
        exact Set.disjoint_left.mp
          (hok.disj (.k l) (.k l') (by show l < _; omega)
            (by show l' < _; omega) (fun he => by injection he; omega))
          hp h3
      have h2 := props_stKey ho hok n (l + 1) (by omega)
      rw [show l + 1 + n = l + (n + 1) by omega] at h2
      exact ((L.props_stK T) ho hok (by omega)).seq h2 hd hd

def coKe : Core Pd E L.sX L.sX := ⟨L.bKe, L.hKe⟩

def stKe : Stage Pd E L.sX L.sX := ⟨L.coKe, (), ∅, ∅, fun _ => PMF.pure (), 0, 0⟩

omit [NeZero (2 : E)] in
theorem props_stKe : L.stKe.Props (L.cK T L.par.D) (L.c3 T) :=
  Stage.Props.of_empty (S := L.stKe) (L.clean_bKe T) (L.accOn_hKe T _) (Hon.masked_pure _ _ _ _)
    (fun _ _ _ => trivial) rfl fun _ => rfl

def coT0 : Core Pd E L.sX L.sX := ⟨L.bT0, L.hT0⟩

def stT0 : Stage Pd E L.sX L.sX :=
  ⟨L.coT0, (ePt E (L.par.σ + L.par.lp), ()), ∅, ∅, simNone _, pPt E (L.par.σ + L.par.lp), 0⟩

omit [NeZero (2 : E)] in
theorem props_stT0 (hnt : L.par.NT ≤ 2 ^ L.par.σ) : L.stT0.Props (L.c3 T) (L.cT T 0) where
  clean := (L.clean_bT0 T) hnt
  acc := (L.accOn_hT0 T) _ hnt
  masked := L.masked_hT0
  keeps := fun _ _ _ => trivial
  prBad := prRho_head_le (Block.chalRound E (Fin (L.par.σ + L.par.lp) → E)) []
    (fun ϱ => nzT ϱ = false) _ (cnt_nzT_le _)
  prWin := fun _ _ => prRho_empty _ fun _ h => h

def coT (l : ℕ) : Core Pd E L.sX L.sX := ⟨L.bT l, L.hT l⟩

def stT (l : ℕ) : Stage Pd E L.sX L.sX :=
  ⟨L.coT l, (L.plT l).plErr 1, L.grp (.t l), L.grp (.t l), PL.Prover.simPl (L.plT l),
    PL.Prover.pBad (L.plT l), 0⟩

theorem props_stT (hok : L.PadsOK) {l : ℕ} (hl : l < L.par.r) :
    (L.stT l).Props (L.cT T l) ((L.cT T) (l + 1)) where
  clean := (L.clean_bT T) hl
  acc := (L.accOn_hT T) hl (L.grp_subset (g := .t l) hl)
  masked := L.masked_hT (hok.t l hl)
  keeps := fun _ _ _ => trivial
  prBad := (L.prT l).prBad_pl (List.Perm.refl _)
  prWin := fun a _ => by
    show prRho ((L.prT l).pl.Win a) ≤ 0
    rw [(L.prT l).win_pl a]
    exact prRho_empty _ fun _ h => h

/-- The layers l, .., l + n - 1 of the tree over the table. -/
def coTab : (n l : ℕ) → Core Pd E L.sX L.sX
  | 0, _ => Core.id _
  | n + 1, l => (L.coT l).seq (coTab n (l + 1))

def errTab : (n l : ℕ) → Err (L.coTab n l).B.shape
  | 0, _ => ()
  | n + 1, l => Err.app (s := (L.coT l).B.shape) ((L.plT l).plErr 1) (errTab n (l + 1))

def uTab : (n l : ℕ) → Set Pd
  | 0, _ => ∅
  | n + 1, l => L.grp (.t l) ∪ uTab n (l + 1)

def simTab :
    (n l : ℕ) → Rho (L.coTab n l).B.shape → PMF (Plains (L.coTab n l).B.shape)
  | 0, _ => fun _ => PMF.pure ()
  | n + 1, l => Hon.simSeq (s := (L.coT l).B.shape) (PL.Prover.simPl (L.plT l)) (simTab n (l + 1))

def pBadTab : (n l : ℕ) → ℝ≥0∞
  | 0, _ => 0
  | n + 1, l => PL.Prover.pBad (L.plT l) + pBadTab n (l + 1)

def stTab (n l : ℕ) : Stage Pd E L.sX L.sX :=
  ⟨L.coTab n l, L.errTab n l, L.uTab n l, L.uTab n l, L.simTab n l, L.pBadTab n l, pWinN n⟩

omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem stTab_zero (l : ℕ) : L.stTab 0 l = Stage.id _ := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem stTab_succ (n l : ℕ) : L.stTab (n + 1) l = (L.stT l).seq (L.stTab n (l + 1)) := rfl

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem mem_stTab_U {p : Pd} :
    ∀ {n l : ℕ}, p ∈ (L.stTab n l).U ↔ ∃ l', l ≤ l' ∧ l' < l + n ∧ p ∈ L.grp (.t l')
  | 0, l => ⟨fun h => absurd h (Set.notMem_empty p), fun ⟨l', h1, h2, _⟩ => by omega⟩
  | n + 1, l => by
      show p ∈ L.grp (.t l) ∪ (L.stTab n (l + 1)).U ↔ _
      rw [Set.mem_union, mem_stTab_U]
      constructor
      · rintro (h | ⟨l', h1, h2, h3⟩)
        · exact ⟨l, le_rfl, by omega, h⟩
        · exact ⟨l', by omega, by omega, h3⟩
      · rintro ⟨l', h1, h2, h3⟩
        by_cases h : l' = l
        · subst h
          exact Or.inl h3
        · exact Or.inr ⟨l', by omega, by omega, h3⟩

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem stTab_D : ∀ n l : ℕ, (L.stTab n l).D = (L.stTab n l).U
  | 0, _ => rfl
  | n + 1, l => by
      show L.grp (.t l) ∪ (L.stTab n (l + 1)).D = L.grp (.t l) ∪ (L.stTab n (l + 1)).U
      rw [stTab_D]

theorem props_stTab (hok : L.PadsOK) :
    ∀ n l : ℕ, l + n ≤ L.par.r → (L.stTab n l).Props (L.cT T l) ((L.cT T) (l + n))
  | 0, l, _ => Stage.props_id _
  | n + 1, l, h => by
      have hd : Disjoint (L.grp (.t l))
          (L.stTab n (l + 1)).U := Set.disjoint_left.mpr fun p hp hp' => by
        obtain ⟨l', h1, h2, h3⟩ := L.mem_stTab_U.mp hp'
        exact Set.disjoint_left.mp
          (hok.disj (.t l) (.t l') (by show l < _; omega)
            (by show l' < _; omega) (fun he => by injection he; omega))
          hp h3
      have h2 := props_stTab hok n (l + 1) (by omega)
      rw [show l + 1 + n = l + (n + 1) by omega] at h2
      exact ((L.props_stT T) hok (by omega)).seq h2 hd hd

def coL : Core Pd E L.sX L.sX := ⟨L.bL, L.hL⟩

def stL : Stage Pd E L.sX L.sX :=
  ⟨L.coL, L.plL.plErr 0, L.grp .lf, L.grp .lf, PL.Prover.simPl L.plL, 0, 0⟩

theorem props_stL (hok : L.PadsOK) : L.stL.Props (L.cT T L.par.r) (L.c5 T) where
  clean := (L.clean_bL T)
  acc := (L.accOn_hL T) (L.grp_subset (g := .lf) trivial)
  masked := L.masked_hL hok.lf
  keeps := fun _ _ _ => trivial
  prBad :=
    (L.prL.prBad_pl (List.Perm.refl _)).trans (le_of_eq (PL.Prover.pBad_of_none fun _ => rfl))
  prWin := fun a _ => by
    show prRho (L.prL.pl.Win a) ≤ 0
    rw [L.prL.win_pl a]
    exact prRho_empty _ fun _ h => h

def coB0 : Core Pd E L.sX L.sX := ⟨L.bB0, L.hB0⟩

def stB0 : Stage Pd E L.sX L.sX :=
  ⟨L.coB0, (ePt E L.par.gT, ()), ∅, ∅, simNone _, pPt E L.par.gT, 0⟩

omit [NeZero (2 : E)] in
theorem props_stB0 (hnt : L.par.NT ≤ 2 ^ L.par.σ) : L.stB0.Props (L.c5 T) (L.c6 T) where
  clean := (L.clean_bB0 T) hnt
  acc := (L.accOn_hB0 T) _ hnt
  masked := L.masked_hB0
  keeps := fun _ _ _ => trivial
  prBad := prRho_head_le (Block.chalRound E (Fin L.par.gT → E)) []
    (fun ϱ => nzT ϱ = false) _ (cnt_nzT_le _)
  prWin := fun _ _ => prRho_empty _ fun _ h => h

def coB : Core Pd E L.sX L.sX := ⟨L.bB, L.hB⟩

def stB : Stage Pd E L.sX L.sX :=
  ⟨L.coB, L.plB.plErr 0, L.grp .bt, L.grp .bt, PL.Prover.simPl L.plB, 0, 0⟩

theorem props_stB (hok : L.PadsOK) : L.stB.Props (L.c6 T) (L.c7 T) where
  clean := (L.clean_bB T)
  acc := (L.accOn_hB T) (L.grp_subset (g := .bt) trivial)
  masked := L.masked_hB hok.bt
  keeps := fun _ _ _ => trivial
  prBad :=
    (L.prB.prBad_pl (List.Perm.refl _)).trans (le_of_eq (PL.Prover.pBad_of_none fun _ => rfl))
  prWin := fun a _ => by
    show prRho (L.prB.pl.Win a) ≤ 0
    rw [L.prB.win_pl a]
    exact prRho_empty _ fun _ h => h

def co5 : Core Pd E L.sX L.sX := ⟨L.bDeg, L.hDeg⟩

/-- Step 5 as a stage. -/
def st5 : Stage Pd E L.sX L.sX := ⟨L.co5, (ePt E L.par.σ, ()), ∅, ∅, simNone _, 0, 0⟩

omit [NeZero (2 : E)] in
theorem props_st5 (hnt : L.par.NT ≤ 2 ^ L.par.σ) : L.st5.Props (L.c7 T) (L.c8 T) :=
  Stage.Props.of_empty (S := L.st5) (L.clean_bDeg T hnt) (L.accOn_hDeg T _ hnt) L.masked_hDeg
    (fun _ _ _ => trivial) rfl fun _ => rfl

def coUV : Core Pd E L.sX L.sX := ⟨L.bUV, L.hUV⟩

def stUV : Stage Pd E L.sX L.sX :=
  ⟨L.coUV, (ePt E L.par.σ, ()), L.grp .uv, L.grp .uv,
    Hon.simOne (r := L.rUV) (K := L.KUV) E id, pPt E L.par.σ, 0⟩

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem padsUV_subset : L.padsUV ⊆ L.allPads := by
  rintro p ⟨π, hπ, θ, hθ, rfl | rfl⟩
  · exact ⟨.uv, trivial, ⟨.inl (⟨π, hπ⟩, ⟨θ, hθ⟩), rfl⟩⟩
  · exact ⟨.uv, trivial, ⟨.inr (⟨π, hπ⟩, ⟨θ, hθ⟩), rfl⟩⟩

omit [NeZero (2 : E)] in
theorem props_stUV (hok : L.PadsOK) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.stUV.Props (L.c8 T) (L.c9a T) where
  clean := (L.clean_bUV T) hnt
  acc := (L.accOn_hUV T) L.padsUV_subset
  masked := L.masked_hUV hok.uv
  keeps := fun _ _ _ => trivial
  prBad := prRho_head_le L.rUV [] (fun ϱ => nzT ϱ = false) _ (cnt_nzT_le _)
  prWin := fun _ _ => prRho_empty _ fun _ h => h

def coXi : Core Pd E L.sX L.sX := ⟨L.bXi, L.hXi⟩

def stXi : Stage Pd E L.sX L.sX :=
  ⟨L.coXi, (L.par.eXi (Fintype.card E), ()), ∅, ∅, simNone _, 0, 0⟩

omit [NeZero (2 : E)] in
theorem props_stXi : L.stXi.Props (L.c9a T) (L.c9b T) :=
  Stage.Props.of_empty (S := L.stXi) (L.clean_bXi T) (L.accOn_hXi T _) L.masked_hXi
    (fun _ _ _ => trivial) rfl fun _ => rfl

def coRs : Core Pd E L.sX L.sX := ⟨L.bRs, L.hRs⟩

def stRs : Stage Pd E L.sX L.sX :=
  ⟨L.coRs, L.scR.scErr (lkVars L.par.σ), L.grp .rt, L.grp .rt, L.scR.simSc (lkVars L.par.σ), 0, 0⟩

theorem props_stRs (hok : L.PadsOK) : L.stRs.Props (L.c9b T) (L.c9c T) :=
  Stage.Props.of_empty (S := L.stRs) (L.clean_bRs T)
    ((L.accOn_hRs T) (L.grp_subset (g := .rt) trivial)) (L.masked_hRs hok.rt) (fun _ _ _ => trivial)
    (L.prR.bad_sc (fun _ => rfl) _ _) fun _ => L.prR.win_sc _ _ _

def coRec : Core Pd E L.sX L.sX := ⟨L.bRec, L.hRec⟩

def stRec : Stage Pd E L.sX L.sX := ⟨L.coRec, (), ∅, ∅, fun _ => PMF.pure (), 0, 0⟩

omit [NeZero (2 : E)] in
theorem props_stRec : L.stRec.Props (L.c9c T) (L.c10 T) :=
  Stage.Props.of_empty (S := L.stRec) (L.clean_bRec T) (L.accOn_hRec T _) (Hon.masked_pure _ _ _ _)
    (fun _ _ _ => trivial) rfl fun _ => rfl

/-! ## 4. Groups of pads, in the order of the messages -/

/-- The position of a group in the order of the messages. -/
def rank : Grp → ℕ
  | .zy => 0 | .k _ => 1 | .t _ => 2 | .lf => 3 | .bt => 4 | .uv => 5 | .rt => 6

/-- The pads of the groups whose rank has the property Q. -/
def UG (Q : ℕ → Prop) : Set Pd := {p | ∃ g, Q (rank g) ∧ L.GOK g ∧ p ∈ L.grp g}

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem disj_UG (hok : L.PadsOK) {Q Q' : ℕ → Prop} (h : ∀ m, Q m → ¬ Q' m) :
    Disjoint (L.UG Q) (L.UG Q') :=
  Set.disjoint_left.mpr fun _ ⟨g, hQ, hg, hp⟩ ⟨g', hQ', hg', hp'⟩ =>
    Set.disjoint_left.mp (hok.disj g g' hg hg' fun he => h _ hQ (he ▸ hQ')) hp hp'

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem grp_sub_UG {Q : ℕ → Prop} (g : Grp) (hg : L.GOK g) (hQ : Q (rank g)) : L.grp g ⊆ L.UG Q :=
  fun _ hp => ⟨g, hQ, hg, hp⟩

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem UG_mono {Q Q' : ℕ → Prop} (h : ∀ m, Q m → Q' m) : L.UG Q ⊆ L.UG Q' :=
  fun _ ⟨g, hQ, hg, hp⟩ => ⟨g, h _ hQ, hg, hp⟩

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem stKey_sub : (L.stKey L.par.D 0).U ⊆ L.UG (· = 1) := fun _ hp => by
  obtain ⟨l', _, h2, h3⟩ := L.mem_stKey_U.mp hp
  exact ⟨.k l', rfl, by show l' < _; omega, h3⟩

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem stTab_sub : (L.stTab L.par.r 0).U ⊆ L.UG (· = 2) := fun _ hp => by
  obtain ⟨l', _, h2, h3⟩ := L.mem_stTab_U.mp hp
  exact ⟨.t l', rfl, by show l' < _; omega, h3⟩

/-! ## 5. The three phases and the whole argument -/

/-- The protocols of the three phases and of the whole argument. -/
def co14 : Core Pd E L.sL L.sX :=
  L.coAl.seq (L.coZY.seq
    ((L.coKey L.par.D 0).seq
      (L.coKe.seq (L.coT0.seq ((L.coTab L.par.r 0).seq (L.coL.seq (L.coB0.seq L.coB)))))))

def co6 : Core Pd E L.sX L.sX := L.coUV.seq (L.coXi.seq (L.coRs.seq L.coRec))

def coLookup : Core Pd E L.sL L.sX := L.co14.seq (L.co5.seq L.co6)

/-- Steps 1 to 4 as a stage. -/
def st14 : Stage Pd E L.sL L.sX :=
  L.stAl.seq (L.stZY.seq
    ((L.stKey L.par.D 0).seq
      (L.stKe.seq (L.stT0.seq ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB)))))))

/-- Step 6 as a stage. -/
def st6 : Stage Pd E L.sX L.sX := L.stUV.seq (L.stXi.seq (L.stRs.seq L.stRec))

/-- The lookup argument as a stage. -/
def stLookup : Stage Pd E L.sL L.sX := L.st14.seq (L.st5.seq L.st6)

omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
/-- The protocol of each stage is the one defined above, by definition. -/
theorem toCore_st14 : L.st14.toCore = L.co14 := rfl
omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_st5 : L.st5.toCore = L.co5 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_st6 : L.st6.toCore = L.co6 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_stLookup : L.stLookup.toCore = L.coLookup := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_stKey (n l : ℕ) : (L.stKey n l).toCore = L.coKey n l := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_stTab (n l : ℕ) : (L.stTab n l).toCore = L.coTab n l := rfl

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem st14_U_sub : L.st14.U ⊆ L.UG (· ≤ 4) := by
  refine Set.union_subset (Set.empty_subset _)
    (Set.union_subset (L.grp_sub_UG .zy trivial (by show 0 ≤ 4; omega))
      (Set.union_subset (L.stKey_sub.trans (L.UG_mono fun m h => by omega))
        (Set.union_subset (Set.empty_subset _)
          (Set.union_subset (Set.empty_subset _)
            (Set.union_subset (L.stTab_sub.trans (L.UG_mono fun m h => by omega))
              (Set.union_subset (L.grp_sub_UG .lf trivial (by show 3 ≤ 4; omega))
                (Set.union_subset (Set.empty_subset _)
                  (L.grp_sub_UG .bt trivial (by show 4 ≤ 4; omega)))))))))

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem st6_U_sub : L.st6.U ⊆ L.UG (5 ≤ ·) :=
  Set.union_subset (L.grp_sub_UG .uv trivial (by show 5 ≤ 5; omega))
    (Set.union_subset (Set.empty_subset _)
      (Set.union_subset (L.grp_sub_UG .rt trivial (by show 5 ≤ 6; omega)) (Set.empty_subset _)))

/-- Under `LkPar.WF` at the characteristic p of E, `PadsOK` and 2 ≠ 0 in E: all properties of steps
1 to 4. -/
theorem props_st14 {p : ℕ} [CharP E p] (hW : L.par.WF p) (hok : L.PadsOK) :
    L.st14.Props (L.c0 T) (L.c7 T) := by
  have p8 : (L.stB0.seq L.stB).Props (L.c5 T) (L.c7 T) :=
    (L.props_stB0 T hW.nt).seq (L.props_stB T hok) (Set.empty_disjoint _) (Set.empty_disjoint _)
  have u8 : (L.stB0.seq L.stB).U ⊆ L.UG (4 ≤ ·) :=
    Set.union_subset (Set.empty_subset _) (L.grp_sub_UG .bt trivial (by show 4 ≤ 4; omega))
  have d7 : Disjoint (L.grp .lf) (L.stB0.seq L.stB).U :=
    (L.disj_UG hok (Q := (· = 3)) (Q' := (4 ≤ ·)) fun m h => by omega).mono
      (L.grp_sub_UG (Q := (· = 3)) .lf trivial rfl) u8
  have p7 := (L.props_stL T hok).seq p8 d7 d7
  have u7 : (L.stL.seq (L.stB0.seq L.stB)).U ⊆ L.UG (3 ≤ ·) :=
    Set.union_subset (L.grp_sub_UG .lf trivial (by show 3 ≤ 3; omega))
      (u8.trans (L.UG_mono fun m h => by omega))
  have d6 : Disjoint (L.stTab L.par.r 0).U (L.stL.seq (L.stB0.seq L.stB)).U :=
    (L.disj_UG hok (Q := (· = 2)) (Q' := (3 ≤ ·)) fun m h => by omega).mono L.stTab_sub u7
  have h6 := (L.props_stTab T) hok L.par.r 0 (by omega)
  rw [Nat.zero_add] at h6
  have p6 := h6.seq p7 d6 (by rw [L.stTab_D]; exact d6)
  have u6 : ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB))).U ⊆ L.UG (2 ≤ ·) :=
    Set.union_subset (L.stTab_sub.trans (L.UG_mono fun m h => by omega))
      (u7.trans (L.UG_mono fun m h => by omega))
  have p5 := (L.props_stT0 T hW.nt).seq p6 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have p4 := (L.props_stKe T).seq p5 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have u4 : (L.stKe.seq (L.stT0.seq ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB))))).U ⊆
      L.UG (2 ≤ ·) :=
    Set.union_subset (Set.empty_subset _) (Set.union_subset (Set.empty_subset _) u6)
  have d3 : Disjoint (L.stKey L.par.D 0).U
      (L.stKe.seq (L.stT0.seq ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB))))).U :=
    (L.disj_UG hok (Q := (· = 1)) (Q' := (2 ≤ ·)) fun m h => by omega).mono L.stKey_sub u4
  have h3 := (L.props_stKey T) hW.ord hok L.par.D 0 (by omega)
  rw [Nat.zero_add] at h3
  have p3 := h3.seq p4 d3 (by rw [L.stKey_D]; exact d3)
  have u3 : ((L.stKey L.par.D 0).seq
        (L.stKe.seq (L.stT0.seq ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB)))))).U ⊆
      L.UG (1 ≤ ·) :=
    Set.union_subset (L.stKey_sub.trans (L.UG_mono fun m h => by omega))
      (u4.trans (L.UG_mono fun m h => by omega))
  have d2 : Disjoint (L.grp .zy)
      ((L.stKey L.par.D 0).seq
        (L.stKe.seq (L.stT0.seq ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB)))))).U :=
    (L.disj_UG hok (Q := (· = 0)) (Q' := (1 ≤ ·)) fun m h => by omega).mono
      (L.grp_sub_UG (Q := (· = 0)) .zy trivial rfl) u3
  have p2 := (L.props_stZY T hok hW.nt).seq p3 d2 d2
  exact (L.props_stAl T hW).seq p2 (Set.empty_disjoint _) (Set.empty_disjoint _)

/-- Under `PadsOK`, NT ≤ 2^σ and 2 ≠ 0 in E: all properties of step 6. -/
theorem props_st6 (hok : L.PadsOK) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.st6.Props (L.c8 T) (L.c10 T) := by
  have p3 :=
    (L.props_stRs T hok).seq (L.props_stRec T) (Set.disjoint_empty _) (Set.disjoint_empty _)
  have p2 := (L.props_stXi T).seq p3 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have u2 : (L.stXi.seq (L.stRs.seq L.stRec)).U ⊆ L.UG (6 ≤ ·) :=
    Set.union_subset (Set.empty_subset _)
      (Set.union_subset (L.grp_sub_UG .rt trivial (by show 6 ≤ 6; omega)) (Set.empty_subset _))
  have d1 : Disjoint (L.grp .uv) (L.stXi.seq (L.stRs.seq L.stRec)).U :=
    (L.disj_UG hok (Q := (· = 5)) (Q' := (6 ≤ ·)) fun m h => by omega).mono
      (L.grp_sub_UG (Q := (· = 5)) .uv trivial rfl) u2
  exact (L.props_stUV T hok hnt).seq p2 d1 d1

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem st14_D : L.st14.D = L.st14.U := by
  show ∅ ∪ (L.grp .zy ∪
        ((L.stKey L.par.D 0).D ∪
          (∅ ∪ (∅ ∪ ((L.stTab L.par.r 0).D ∪ (L.grp .lf ∪ (∅ ∪ L.grp .bt))))))) =
    ∅ ∪ (L.grp .zy ∪
        ((L.stKey L.par.D 0).U ∪
          (∅ ∪ (∅ ∪ ((L.stTab L.par.r 0).U ∪ (L.grp .lf ∪ (∅ ∪ L.grp .bt)))))))
  rw [L.stKey_D, L.stTab_D]

/-- Under `LkPar.WF` at the characteristic p of E, `PadsOK` and 2 ≠ 0 in E: all properties of the
lookup argument. -/
theorem props_stLookup {p : ℕ} [CharP E p] (hW : L.par.WF p) (hok : L.PadsOK) :
    L.stLookup.Props (L.c0 T) (L.c10 T) := by
  have p2 := (L.props_st5 T hW.nt).seq
    (L.props_st6 T hok hW.nt) (Set.empty_disjoint _) (Set.empty_disjoint _)
  have u2 : (L.st5.seq L.st6).U ⊆ L.UG (5 ≤ ·) := Set.union_subset (Set.empty_subset _) L.st6_U_sub
  have d1 : Disjoint L.st14.U (L.st5.seq L.st6).U :=
    (L.disj_UG hok (Q := (· ≤ 4)) (Q' := (5 ≤ ·)) fun m h => by omega).mono L.st14_U_sub u2
  exact (L.props_st14 T hW hok).seq p2 d1 (by rw [L.st14_D]; exact d1)

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
/-- The argument masks with its own pads only. -/
theorem stLookup_U_sub : L.stLookup.U ⊆ L.allPads := by
  have h : ∀ Q, L.UG Q ⊆ L.allPads := fun Q _ ⟨g, _, hg, hp⟩ => ⟨g, hg, hp⟩
  exact Set.union_subset (L.st14_U_sub.trans (h _))
    (Set.union_subset (Set.empty_subset _) (L.st6_U_sub.trans (h _)))

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
/-- It reads no other pad. -/
theorem stLookup_D : L.stLookup.D = L.stLookup.U := by
  show L.st14.D ∪ (∅ ∪ L.st6.U) = L.st14.U ∪ (∅ ∪ L.st6.U)
  rw [L.st14_D]

/-! ## 6. No vector is sent -/

section Track

variable {F : Type} [Field F] [Algebra F E]

/-- A protocol that leaves the implicit part unchanged exposes the same entries as its input,
whatever encoding data its rounds are given. -/
def trackSame {X X' I I' : Type} (S : Core Pd E ⟨X, Y, I⟩ ⟨X', Y, I'⟩)
    (d : EncData F E S.B.shape) (ra : Reads F E ⟨X, Y, I⟩) :
    S.Track ra (Stage.readsX X' I' ra) :=
  ⟨d, fun n => .inl n⟩

omit [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem trackSame_ok {X X' I I' : Type} (S : Core Pd E ⟨X, Y, I⟩ ⟨X', Y, I'⟩)
    (d : EncData F E S.B.shape) (ra : Reads F E ⟨X, Y, I⟩) (himp : ∀ y τ, S.B.imp y τ = y) :
    (trackSame S d ra).OK :=
  ⟨fun y τ n => by
      show ra.rd (S.B.imp y τ) n = ra.rd y n
      rw [himp],
    fun y τ => by
      show ra.mat (S.B.imp y τ) = ra.mat y
      rw [himp]⟩

omit [Field E] [Fintype E] [DecidableEq E] [Fintype Pd] [DecidableEq Pd] in
theorem imp_seq {X₁ X₂ X₃ I₁ I₂ I₃ : Type} {S₁ : Core Pd E ⟨X₁, Y, I₁⟩ ⟨X₂, Y, I₂⟩}
    {S₂ : Core Pd E ⟨X₂, Y, I₂⟩ ⟨X₃, Y, I₃⟩} (h₁ : ∀ y τ, S₁.B.imp y τ = y)
    (h₂ : ∀ y τ, S₂.B.imp y τ = y) :
    ∀ y τ, (S₁.seq S₂).B.imp y τ = y := fun y τ => by
  show S₂.B.imp (S₁.B.imp y _) _ = y
  rw [h₁, h₂]

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem imp_stKey : ∀ (n l : ℕ) (y : Y) (τ : Tr (L.stKey n l).B.shape), (L.stKey n l).B.imp y τ = y
  | 0, _, _, _ => rfl
  | n + 1, l, y, τ =>
    imp_seq (S₁ := L.coK l) (S₂ := L.coKey n (l + 1)) (fun y τ => (L.plK l).imp_pl y τ)
      (imp_stKey n (l + 1)) y τ

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem imp_stTab : ∀ (n l : ℕ) (y : Y) (τ : Tr (L.stTab n l).B.shape), (L.stTab n l).B.imp y τ = y
  | 0, _, _, _ => rfl
  | n + 1, l, y, τ =>
    imp_seq (S₁ := L.coT l) (S₂ := L.coTab n (l + 1)) (fun y τ => (L.plT l).imp_pl y τ)
      (imp_stTab n (l + 1)) y τ

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem imp_st14 : ∀ y τ, L.st14.B.imp y τ = y :=
  imp_seq (S₁ := L.coAl) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coZY) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coKey L.par.D 0) (L.imp_stKey _ _) <|
  imp_seq (S₁ := L.coKe) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coT0) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coTab L.par.r 0) (L.imp_stTab _ _) <|
  imp_seq (S₁ := L.coL) (fun y τ => L.plL.imp_pl y τ) <|
  imp_seq (S₁ := L.coB0) (S₂ := L.coB) (fun _ _ => rfl) (fun y τ => L.plB.imp_pl y τ)

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem imp_st6 : ∀ y τ, L.st6.B.imp y τ = y :=
  imp_seq (S₁ := L.coUV) (fun _ _ => rfl) <| imp_seq (S₁ := L.coXi) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coRs) (S₂ := L.coRec) (fun y τ => L.scR.imp_sc _ y τ) (fun _ _ => rfl)

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
/-- The lookup argument leaves the implicit part unchanged. -/
theorem imp_stLookup : ∀ y τ, L.stLookup.B.imp y τ = y :=
  imp_seq (S₁ := L.co14) L.imp_st14 (imp_seq (S₁ := L.co5) (S₂ := L.co6) (fun _ _ => rfl) L.imp_st6)

variable (F)

/-- The encoding data of the rounds of a product layer: they have no vectors. -/
def encPl (Q : PL E Y Pd N (LkX N E)) : EncData F E Q.pl.shape :=
  EncData.app (s := Q.init.shape) PUnit.unit
    (EncData.app (s := (Q.sc.sc Q.ord).shape) (t := Q.fin.shape)
      (SC.encSc Q.sc F Q.ord) (REnc.none E F Bool E, PUnit.unit))

def encKey : (n l : ℕ) → EncData F E (L.coKey n l).B.shape
  | 0, _ => PUnit.unit
  | n + 1, l => EncData.app (s := (L.coK l).B.shape) (encPl F (L.plK l)) (encKey n (l + 1))

def encTab : (n l : ℕ) → EncData F E (L.coTab n l).B.shape
  | 0, _ => PUnit.unit
  | n + 1, l => EncData.app (s := (L.coT l).B.shape) (encPl F (L.plT l)) (encTab n (l + 1))

def enc14 : EncData F E L.co14.B.shape :=
  EncData.app (s := L.coAl.B.shape) (REnc.none E F Empty E, PUnit.unit) <|
  EncData.app (s := L.coZY.B.shape) (REnc.none E F L.KZY (Fin L.par.σ → E), PUnit.unit) <|
  EncData.app (s := (L.coKey L.par.D 0).B.shape) (L.encKey F _ _) <|
  EncData.app (s := L.coKe.B.shape) PUnit.unit <|
  EncData.app (s := L.coT0.B.shape)
      (REnc.none E F Empty (Fin (L.par.σ + L.par.lp) → E), PUnit.unit) <|
  EncData.app (s := (L.coTab L.par.r 0).B.shape) (L.encTab F _ _) <|
  EncData.app (s := L.coL.B.shape) (encPl F L.plL) <|
  EncData.app (s := L.coB0.B.shape)
    (t := L.coB.B.shape) (REnc.none E F Empty (Fin L.par.gT → E), PUnit.unit) (encPl F L.plB)

def enc5 : EncData F E L.co5.B.shape :=
  (REnc.none E F Empty (Fin L.par.σ → E), PUnit.unit)

def enc6 : EncData F E L.co6.B.shape :=
  EncData.app (s := L.coUV.B.shape) (REnc.none E F L.KUV (Fin L.par.σ → E), PUnit.unit) <|
  EncData.app (s := L.coXi.B.shape) (REnc.none E F Empty (Fin (2 * L.par.Pm) → E), PUnit.unit) <|
  EncData.app (s := L.coRs.B.shape)
    (t := L.coRec.B.shape) (SC.encSc L.scR F (lkVars L.par.σ)) PUnit.unit

/-- The three phases and the whole argument send no vector: they expose the same entries as their
input. `tk14`, .. are for the protocols, `track14`, .. for the stages. -/
def tk14 (ra : Reads F E L.sL) :
    L.co14.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  trackSame L.co14 (L.enc14 F) ra
def track14 (ra : Reads F E L.sL) :
    L.st14.Track ra (Stage.readsX (LkX N E) (LkA E) ra) := L.tk14 F ra
def tk5 (ra : Reads F E L.sX) : L.co5.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  trackSame L.co5 (L.enc5 F) ra
def track5 (ra : Reads F E L.sX) :
    L.st5.Track ra (Stage.readsX (LkX N E) (LkA E) ra) := L.tk5 F ra
def tk6 (ra : Reads F E L.sX) : L.co6.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  trackSame L.co6 (L.enc6 F) ra
def track6 (ra : Reads F E L.sX) :
    L.st6.Track ra (Stage.readsX (LkX N E) (LkA E) ra) := L.tk6 F ra
def tkLookup (ra : Reads F E L.sL) :
    L.coLookup.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  trackSame L.coLookup
    (EncData.app (s := L.co14.B.shape) (L.enc14 F)
      (EncData.app (s := L.co5.B.shape) (t := L.co6.B.shape) (L.enc5 F) (L.enc6 F))) ra
def trackLookup (ra : Reads F E L.sL) :
    L.stLookup.Track ra (Stage.readsX (LkX N E) (LkA E) ra) := L.tkLookup F ra

omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem track14_ok (ra : Reads F E L.sL) : (L.track14 F ra).OK := trackSame_ok _ _ _ L.imp_st14
omit [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem track5_ok (ra : Reads F E L.sX) : (L.track5 F ra).OK := trackSame_ok _ _ _ fun _ _ => rfl
omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem track6_ok (ra : Reads F E L.sX) : (L.track6 F ra).OK := trackSame_ok _ _ _ L.imp_st6
omit [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem trackLookup_ok (ra : Reads F E L.sL) : (L.trackLookup F ra).OK :=
  trackSame_ok _ _ _ L.imp_stLookup

variable {F} {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

omit [NeZero (2 : E)] in
theorem all_encPl (K : PL E Y Pd N (LkX N E)) : EncData.All Q K.pl.shape (encPl F K) :=
  EncData.All.app (s := K.init.shape) (d := PUnit.unit) trivial
    (EncData.All.app (s := (K.sc.sc K.ord).shape) (t := K.fin.shape)
      (SC.all_encSc K.sc _) ⟨fun e => e.elim, trivial⟩)

omit [NeZero (2 : E)] in
theorem all_encKey : ∀ n l : ℕ, EncData.All Q (L.coKey n l).B.shape (L.encKey F n l)
  | 0, _ => trivial
  | n + 1, l =>
    EncData.All.app (s := (L.coK l).B.shape) (all_encPl (L.plK l)) (all_encKey n (l + 1))

omit [NeZero (2 : E)] in
theorem all_encTab : ∀ n l : ℕ, EncData.All Q (L.coTab n l).B.shape (L.encTab F n l)
  | 0, _ => trivial
  | n + 1, l =>
    EncData.All.app (s := (L.coT l).B.shape) (all_encPl (L.plT l)) (all_encTab n (l + 1))

omit [NeZero (2 : E)] in
theorem all_enc14 : EncData.All Q L.co14.B.shape (L.enc14 F) :=
  EncData.All.app (s := L.coAl.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.coZY.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := (L.coKey L.par.D 0).B.shape) (L.all_encKey _ _) <|
  EncData.All.app (s := L.coKe.B.shape) (d := PUnit.unit) trivial <|
  EncData.All.app (s := L.coT0.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := (L.coTab L.par.r 0).B.shape) (L.all_encTab _ _) <|
  EncData.All.app (s := L.coL.B.shape) (all_encPl L.plL) <|
  EncData.All.app (s := L.coB0.B.shape)
    (t := L.coB.B.shape) ⟨fun e => e.elim, trivial⟩ (all_encPl L.plB)

omit [NeZero (2 : E)] in
theorem all_enc6 : EncData.All Q L.co6.B.shape (L.enc6 F) :=
  EncData.All.app (s := L.coUV.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.coXi.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.coRs.B.shape)
    (t := L.coRec.B.shape) (d' := PUnit.unit) (SC.all_encSc L.scR _) trivial

omit [NeZero (2 : E)] in
/-- No vector is sent: every condition on the vectors that are sent holds vacuously. -/
theorem all_track14 (ra : Reads F E L.sL) : (L.track14 F ra).All Q := L.all_enc14
omit [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
omit [NeZero (2 : E)] in
theorem all_track5 (ra : Reads F E L.sX) : (L.track5 F ra).All Q := ⟨fun e => e.elim, trivial⟩
omit [NeZero (2 : E)] in
theorem all_track6 (ra : Reads F E L.sX) : (L.track6 F ra).All Q := L.all_enc6
omit [NeZero (2 : E)] in
theorem all_trackLookup (ra : Reads F E L.sL) : (L.trackLookup F ra).All Q :=
  EncData.All.app (s := L.co14.B.shape) L.all_enc14
    (EncData.All.app (s := L.co5.B.shape) (t := L.co6.B.shape)
      ⟨fun e => e.elim, trivial⟩ L.all_enc6)

end Track

end Lk

/-! ## 7. How many deferred claims the honest prover's copy of the list gains -/

/-- The numbers of LIN, opened forms and REL in the honest prover's copy of the list of claims. -/
def HLed.len {E : Type} (h : HLed E) : ℕ × ℕ × ℕ := (h.nl, h.ov.length, h.tm.length)

/-- If the copy belongs to the verifier's list (`HLed.Of`), it has as many claims of each kind. -/
theorem HLed.Of.len {N E : Type} [Fintype N] [CommRing E] {h : HLed E} {led : Ledger N E}
    {y : N → E} (H : h.Of led y) :
    (led.lin.length, led.opn.length, led.rel.length) = h.len := by
  unfold HLed.len
  rw [← H.1, ← H.2.1, ← H.2.2, List.length_map, List.length_map]

namespace Lk

variable {E Y Pd N : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
  (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The stage adds d = (LIN, opened forms, REL) claims to the honest prover's copy of the list,
whatever the verifier sends. -/
def Adds {X X' : Type} (S : Stage Pd E ⟨X, Y, LkA E⟩ ⟨X', Y, LkA E⟩) (d : ℕ × ℕ × ℕ) : Prop :=
  ∀ a ρ, (S.H.next a ρ).hl.len = (a.hl.len.1 + d.1, a.hl.len.2.1 + d.2.1, a.hl.len.2.2 + d.2.2)

omit [Field E] [Fintype E] [DecidableEq E] in
theorem Adds.seq {X₁ X₂ X₃ : Type} {S₁ : Stage Pd E ⟨X₁, Y, LkA E⟩ ⟨X₂, Y, LkA E⟩}
    {S₂ : Stage Pd E ⟨X₂, Y, LkA E⟩ ⟨X₃, Y, LkA E⟩} {d₁ d₂ : ℕ × ℕ × ℕ}
    (h₁ : Adds S₁ d₁) (h₂ : Adds S₂ d₂) :
    Adds (S₁.seq S₂) (d₁.1 + d₂.1, d₁.2.1 + d₂.2.1, d₁.2.2 + d₂.2.2) := fun a ρ => by
  show (S₂.H.next (S₁.H.next a _) _).hl.len = _
  rw [h₂, h₁]
  simp only [Nat.add_assoc]

omit [Fintype E] [DecidableEq E] in
private theorem len_addProd (h : HLed E) (e0 e1 : E) :
    (h.addProd e0 e1).len = (h.len.1 + 0, h.len.2.1 + 2, h.len.2.2 + 1) := by
  simp [HLed.len, HLed.addProd]

/-- If the layer's prover stores with `setA`: after a product layer the state is `setA` of the state
before it, at some point and some two values. -/
private theorem next_pl {Q : PL E Y Pd N (LkX N E)} (H : Q.Prover (LkA E)) (hs : H.set = setA)
    (a : LkA E) (ρ : Rho Q.pl.shape) :
    ∃ p e0 e1, H.pl.next a ρ = setA a p e0 e1 := by
  have h : ∃ s p e0 e1,
      H.pl.next a ρ = H.set ((H.scP.sc Q.ord []).next (a, fun _ => 0) s).1 p e0 e1 :=
    ⟨_, _, _, _, rfl⟩
  obtain ⟨s, p, e0, e1, h⟩ := h
  rw [SC.Prover.next_fst, hs] at h
  exact ⟨p, e0, e1, h⟩

theorem adds_stK (l : ℕ) : Adds (L.stK l) (0, 2, 1) := fun a ρ => by
  obtain ⟨p, e0, e1, h⟩ := next_pl (L.prK l) rfl a ρ
  show ((L.prK l).pl.next a ρ).hl.len = _
  rw [h]
  exact len_addProd _ _ _

theorem adds_stT (l : ℕ) : Adds (L.stT l) (0, 2, 1) := fun a ρ => by
  obtain ⟨p, e0, e1, h⟩ := next_pl (L.prT l) rfl a ρ
  show ((L.prT l).pl.next a ρ).hl.len = _
  rw [h]
  exact len_addProd _ _ _

theorem adds_stKey : ∀ n l : ℕ, Adds (L.stKey n l) (0, 2 * n, n)
  | 0, _ => fun _ _ => rfl
  | n + 1, l => fun a ρ => by
      have h := ((L.adds_stK l).seq (adds_stKey n (l + 1))) a ρ
      refine h.trans ?_
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

theorem adds_stTab : ∀ n l : ℕ, Adds (L.stTab n l) (0, 2 * n, n)
  | 0, _ => fun _ _ => rfl
  | n + 1, l => fun a ρ => by
      have h := ((L.adds_stT l).seq (adds_stTab n (l + 1))) a ρ
      refine h.trans ?_
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

theorem adds_stL : Adds L.stL (1, 2, 1) := fun a ρ => by
  obtain ⟨p, e0, e1, h⟩ := next_pl L.prL rfl a ρ
  show ((L.prL.pl.next a ρ).hl.addLin).len = _
  rw [h]
  simp [HLed.len, HLed.addLin, HLed.addProd, setA]

theorem adds_stB : Adds L.stB (1, 2, 1) := fun a ρ => by
  obtain ⟨p, e0, e1, h⟩ := next_pl L.prB rfl a ρ
  show ((L.prB.pl.next a ρ).hl.addLin).len = _
  rw [h]
  simp [HLed.len, HLed.addLin, HLed.addProd, setA]

theorem adds_stRs : Adds L.stRs (0, 0, 0) := fun a ρ => by
  show ((L.prR.sc (lkVars L.par.σ) []).next (a, fun _ => 0) ρ).1.hl.len = _
  rw [SC.Prover.next_fst]
  rfl

omit [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem adds_stRec : Adds L.stRec (1, 3 * L.par.Pm, 1) := fun a _ => by
  show ((a.hl.addRel (L.ovA a) (L.tsA a)).addLin).len = _
  simp [HLed.len, HLed.addLin, HLed.addRel, ovA]

/-- Steps 1 to 4 add 2 LIN, 2 (D + r + 2) opened forms and D + r + 2 REL to the honest prover's copy
of the list. -/
theorem adds_st14 :
    Adds L.st14 (2, 2 * (L.par.D + L.par.r + 2), L.par.D + L.par.r + 2) := fun a ρ => by
  have h := (Adds.seq (S₁ := L.stAl) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (S₁ := L.stZY) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (L.adds_stKey L.par.D 0) <|
      Adds.seq (S₁ := L.stKe) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (S₁ := L.stT0) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (L.adds_stTab L.par.r 0) <|
      Adds.seq L.adds_stL <|
      Adds.seq (S₁ := L.stB0) (d₁ := (0, 0, 0)) (fun _ _ => rfl) L.adds_stB)
    a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

omit [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem adds_st5 : Adds L.st5 (0, 0, 0) := fun _ _ => rfl

/-- Step 6 adds 1 LIN, 3 Pm opened forms and 1 REL to the honest prover's copy of the list. -/
theorem adds_st6 : Adds L.st6 (1, 3 * L.par.Pm, 1) := fun a ρ => by
  have h := (Adds.seq (S₁ := L.stUV) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (S₁ := L.stXi) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq L.adds_stRs L.adds_stRec)
    a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> first | (dsimp only; done) | (dsimp only; omega)

/-- The lookup argument adds 3 LIN, 2 (D + r + 2) + 3 Pm opened forms and D + r + 3 REL to the
honest prover's copy of the list. -/
theorem adds_stLookup :
    Adds L.stLookup
      (3, 2 * (L.par.D + L.par.r + 2) + 3 * L.par.Pm, L.par.D + L.par.r + 3) := fun a ρ => by
  have h := (L.adds_st14.seq (L.adds_st5.seq L.adds_st6)) a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> first | (dsimp only; done) | (dsimp only; omega)

end Lk

end Blocks
