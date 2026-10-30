-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean.
The calls' lookup of an attention sub-proof: its share of the link's public record, as a value made
of the byte-level verifier's own plan.

Main names:
  `pubAsk_calls`: Forest.pubAsk reads of the record's calls their number alone.
  `shape_cf`: the shape that Attention.shape makes holds the configuration from which it is made.
  `shapeOf_shapeHid`: Attention.shapeHid lid cf = .ok (S, fs) gives
    ShapeOf (S.calls.map (·.call)) fs.pub lid fs, with no run of Forest.pad, and S.cf = cf.
  `IxA`: what the sub-proof's committed messages hold, by names: the cells of the smallness test's
    matrices (NameA), and the mask row's slots.
  `JA`, `cellJ`, `maskJ`, `cellOf`: the entries: cells in a box and slots below a bound; an index
    beyond a bound is laid at the bound.
  `lookPubA rdA a nR nC St`: the record, over any base reading M₀ that is read at the names IxA by
    rdA: h := a.fs; the keys are A.kvA at the cells; the mask entries are the slots from
    a.seam.Fp.next on; the bits of the counts lie in the matrix number a.S.cf.NAs + 2, of 2^lmb
    rows.
  `lookPubA_plan`: where Attention.plan returns a: Fo.Pub2.LookPubOK of it, at the calls, numbers of
    padding keys and cap with which Attention.hear calls Forest.pad (Fo.a_hear_exact,
    OnBytes/Tie/Pv/Lookup/Ends/FoTiedLook.lean). Its clauses on the mask entries and the cells hold
    by unfolding: the layout is written by maskJ and cellJ.
  `lookPubA_ok`: so at every member a of X.A, where Verify.publicOf returns X.
Limits: attention's lookup on the calls alone. nR and nC, the box's bounds, are free: no clause here
asks that different places are different entries, and beyond the bounds they are not. The two other
bounds are the plan's (a.S.cf.NAs + 4 matrices; a.ns slots): that every matrix and every slot that
the lookup names lies below them is not shown here. That the first slot of the lookup in a run is
a.seam.Fp.next is Fo.slots_next (OnBytes/Tie/Pv/Lookup/Ends/FoDoors.lean). The keys do not read the
caller's state. The layout is WRITTEN here: that the byte-level verifier reads the bits of the
counts in the matrix number a.S.cf.NAs + 2, and its keys as A.kvA, is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPub
import OnBytes.Tie.Pv.Lookup.Ends.A
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePublic
import OnBytes.Tie.Pv.Lookup.Peel.FoPayPlan

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends
open Fo.BatRows (bindE_ok)

/-! ### the shape, at the plan -/

theorem pubAsk_calls (h : Forest.Shape) (c₂ : Array Call) (pub : Array ℕ)
    (hs : c₂.size = h.calls.size) :
    Forest.pubAsk { h with calls := c₂ } pub = Forest.pubAsk h pub := by
  unfold Forest.pubAsk
  dsimp only
  rw [hs]

theorem shape_cf {cf : Attention.Cfg} {A : Attention.Shape} (e : Attention.shape cf = .ok A) :
    A.cf = cf := by
  unfold Attention.shape at e
  dsimp only at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  rfl

theorem shapeOf_shapeHid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (e : Attention.shapeHid lid cf = .ok (S, fs)) :
    ShapeOf (S.calls.map (·.call)) fs.pub lid fs ∧ S.cf = cf := by
  unfold Attention.shapeHid at e
  obtain ⟨A, hA, e⟩ := bindE_ok e
  obtain ⟨h, hs, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨kbA, _, e⟩ := bindE_ok e
  dsimp only at e
  obtain ⟨counted, _, e⟩ := bindE_ok e
  obtain ⟨_, hp, e⟩ := bindE_ok e
  cases e
  refine ⟨⟨_, shape_iota ?_ hs, ?_, rfl⟩, (shape_cf hA : A.cf = cf)⟩
  · apply Array.ext <;> simp [strip]
  · rw [pubAsk_calls _ _ _ (by rw [(shape_more hs).1]; simp)]
    exact hp

/-! ### the entries -/

/-- The names at attention: the cells of the smallness test's matrices, and the mask row's slots. -/
abbrev IxA : Type := NameA ⊕ ℕ

/-- Cells in a box, and slots below a bound. -/
abbrev JA (nM nR nC nS : ℕ) : Type :=
  (Fin (nM + 1) × Fin (nR + 1) × Fin (nC + 1)) ⊕ Fin (nS + 1)

/-- A number as an index up to n: beyond n it is laid at n. -/
def upTo (n i : ℕ) : Fin (n + 1) := ⟨min i n, Nat.lt_succ_of_le (Nat.min_le_right i n)⟩

variable {nM nR nC nS : ℕ}

/-- The entry of a cell. -/
def cellJ (M r c : ℕ) : JA nM nR nC nS := .inl (upTo nM M, upTo nR r, upTo nC c)

/-- The entry of a slot of the mask row. -/
def maskJ (j : ℕ) : JA nM nR nC nS := .inr (upTo nS j)

/-- The cells by their names, read in the entries. -/
def cellOf (μ : JA nM nR nC nS → Cb.Gl.E) (n : NameA) : Cb.Gl.E := μ (cellJ n.M n.r n.c)

/-! ### the value -/

/-- The calls' lookup's share of the public record of an attention sub-proof. -/
def lookPubA {M₀ : Type} (rdA : M₀ → IxA → Cb.Gl.E) (a : Attention.Plan) (nR nC : ℕ) (St : Type) :
    LookPub M₀ St where
  h := a.fs
  J₀ := JA (a.S.cf.NAs + 4) nR nC a.ns
  L :=
    { K := fun _ μ q i => A.kvA a.S a.fs (cellOf μ) q i
      bc := fun t c j => cellJ (a.S.cf.NAs + 2) (FoNums.cellRC a.fs a.S.cf.lmb (t, c, j)).1
        (FoNums.cellRC a.fs a.S.cf.lmb (t, c, j)).2
      mkS := fun s => maskJ (a.seam.Fp.next + s) }
  rd₀ := fun b => Sum.elim (fun n => rdA b (.inl ⟨n.1.val, n.2.1.val, n.2.2.val⟩))
    fun s => rdA b (.inr s.val)

theorem lookPubA_plan {M₀ : Type} (rdA : M₀ → IxA → Cb.Gl.E) (settings : Settings)
    (i : Attention.In) (cf : Attention.Cfg) (a : Attention.Plan)
    (e : Attention.plan settings i cf = .ok a) (nR nC : ℕ) (St : Type) :
    LookPubOK (lookPubA rdA a nR nC St) (a.S.calls.map (·.call)) a.fs.pub a.lid a.S.cf.lmb
      a.seam.Fp.next maskJ (cellJ (a.S.cf.NAs + 2)) := by
  obtain ⟨h1, h2⟩ := Fo.Pub.planA_shapeHid settings i cf a e
  obtain ⟨s1, s2⟩ := shapeOf_shapeHid h1
  have hb := Fo.Pay.shapeHid_lm h1
  refine ⟨?_, ?_, ?_, fun _ => rfl, fun _ _ _ _ => rfl⟩
  · unfold Attention.Plan.lid
    rw [h2]
    exact s1
  · rw [s2]
    exact hb.1
  · rw [s2]
    exact hb.2

/-- At every member of X.A. A member is what Attention.plan returns but for the record of its
smallness test, which the lookup's share does not read. -/
theorem lookPubA_ok {M₀ : Type} (rdA : M₀ → IxA → Cb.Gl.E) {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    (g : ℕ) (a : Attention.Plan) (hg : X.A[g]? = some a) (nR nC : ℕ) (St : Type) :
    LookPubOK (lookPubA rdA a nR nC St) (a.S.calls.map (·.call)) a.fs.pub a.lid a.S.cf.lmb
      a.seam.Fp.next maskJ (cellJ (a.S.cf.NAs + 2)) := by
  obtain ⟨sc, lines, cf, a0, -, -, -, m2, e3, -, -⟩ := Fo.Pub.public_A h g a hg
  have k := lookPubA_plan rdA _ _ cf a0 m2 nR nC St
  rw [e3]
  exact k

end Fo.Pub2
