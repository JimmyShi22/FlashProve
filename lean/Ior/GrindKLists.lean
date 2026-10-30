-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/GrindKLists.lean: how the bound `Err.BelowG` (in round i the error, as a probability, is ≤
c · 2^b_i) passes through the operations by which lists of errors are made.

Definitions, statements and proofs. No protocol occurs here.
`Err.BelowG g ε c` (Iop/Grind.lean) says e_i ≤ c (2^b_i |C_i|) in every round. Here the error e_i,
from the list ε, is a count of values of the verifier message (Iop/Rbr.lean), |C_i| is the number of
all its values, and b_i, from the list g, is the round's number of test bits (proof of work;
Iop/GBits.lean).
These errors are the entries of a list ε (`Err s`, Iop/Rbr.lean), a variable of each statement that
speaks of them (in `belowG_errZero` the list is `Err.zero s`): that a protocol is sound at such a
list is no statement of this file; that tie, from ε to `Err.grind g ε`, is `Spec.sndBK_grind`
(Ior/GrindK.lean), under its hypotheses, `[Inhabited W]` and `Q.SndBK` at ε (that condition itself
asks soundness of the parts one level down: the tie carries soundness, it does not found it).

Why: the theorems of this library on composing and transforming protocols give explicit lists of
errors, made by the operations below. This file says, for each, how a list g is carried, and that
the bound is kept, under the hypotheses of each statement. So the numbers of test bits can be given
part by part, by the names of the parts, before the transformations.

Main names:
  `belowG_app`: two parts in a row (`Err.app`, `GBits.app`).
  `belowG_max`, `belowG_le`, `belowG_errZero`: a case split (`Err.max`, the larger error in each
    round); a smaller list; a part that adds no error (`Err.zero`).
  `belowG_same_keep`, `belowG_same_dense`, `belowG_same_app`: the verifier draws from subsets
    (`Err.same`, Ior/Sub.lean; bits carried by `GBits.pull`): a part that is not restricted keeps
    its bound; with `σ.Dense κ` the bound c becomes c κ; two parts in a row.
  `belowG_split`: messages are cut (`Err.split`; bits carried by `GBits.split`: they stay with the
    piece that keeps the verifier message).
  `belowG_hoist`: marked messages go first (`Err.hoist`; bits carried by `GBits.hoist`): a marked
    round's bits are dropped.
  `Spec.belowG_recut` (`Err.recut`; bits carried by `GBits.recut`): see its docstring.
  `GBits.UnitFree`: see its docstring. `unitZero_of_belowG`: with it, at c < 1, the bound gives
    `Err.UnitZero`.
  `GBits.pull_zero`, `GBits.split_zero`, `GBits.rest_zero`, `GBits.hoist_zero`: the list of zeros is
    carried to the list of zeros. At `GBits.zero` the bound is `Err.Below` (`Err.belowG_zero`,
    Hiop/GrindK.lean): every rule of the library for `Err.Below` serves a part without proof of work
    as it is.

Limits: where bits are dropped (a marked round at a hoist; the first round of a join by message) the
round's error is 0 by hypothesis: `ε.UnitZero` with `P.OK` here; `Err.ZeroAt` in Ior/Hoist.lean;
`belowG_hoist` itself asks neither. The rules here do not ask that the dropped number be 0.
This file says nothing on joins of two verifier messages (there errors add while bits take the
maximum: the head of Iop/GrindRecut.lean). The rule "all but one of an odd number of values" of
Ior/SubBelow.lean (`below_thin`, `below_fit`) is not carried: it is for parts without work. This
file says nothing on the size of an error beyond `Err.BelowG g ε c`, `Err.le a b` and
`Err.UnitZero`: g, ε and c are variables.
Terms: lean/GLOSSARY.md.
-/
import Iop.GrindRecut
import Iop.SplitNonce
import Iop.BatchJoin
import Iop.JoinProofs
import Blocks.GrindSmallMsg
import Ior.SubBelow
import Ior.Hoist

set_option autoImplicit false

namespace Iop
open scoped ENNReal

/-- The numbers of test bits without the marked rounds. -/
def GBits.rest : {s : Shape} → (μ : Marks s) → GBits s → GBits μ.rest
  | [], _, _ => ()
  | _ :: _, (none, μ), (b, g) => (b, GBits.rest μ g)
  | _ :: _, (some _, μ), (_, g) => GBits.rest μ g

/-- The numbers of test bits when marked messages go first: the new first round has no test. -/
def GBits.hoist {s : Shape} (μ : Marks s) (g : GBits s) : GBits μ.shape := (0, GBits.rest μ g)

/-- A round whose verifier message has one value has no test. -/
def GBits.UnitFree : {s : Shape} → GBits s → Prop
  | [], _ => True
  | r :: _, (b, g) => (Fintype.card r.Chal = 1 → b = 0) ∧ GBits.UnitFree g

theorem GBits.pull_zero :
    ∀ {s : Shape} (σ : Samplers s), (GBits.zero s).pull σ = GBits.zero (s.pull σ)
  | [], _ => rfl
  | _ :: _, (_, σs) => congrArg (Prod.mk 0) (GBits.pull_zero σs)

theorem GBits.split_zero {s : Shape} (P : SPlan s) :
    (GBits.zero s).split P = GBits.zero P.shape := by
  induction P with
  | nil => rfl
  | keep r P ih => exact congrArg (Prod.mk 0) ih
  | cut c P ih => exact congrArg (Prod.mk 0) ih

theorem GBits.rest_zero :
    ∀ {s : Shape} (μ : Marks s), GBits.rest μ (GBits.zero s) = GBits.zero μ.rest
  | [], _ => rfl
  | _ :: _, (none, μ) => congrArg (Prod.mk 0) (GBits.rest_zero μ)
  | _ :: _, (some _, μ) => GBits.rest_zero μ

theorem GBits.hoist_zero {s : Shape} (μ : Marks s) : (GBits.zero s).hoist μ = GBits.zero μ.shape :=
  congrArg (Prod.mk 0) (GBits.rest_zero μ)

namespace Spec

def belowG_app : Prop :=
  ∀ (s t : Shape) (g : GBits s) (g' : GBits t) (ε : Err s) (ε' : Err t) (c : ℝ≥0∞),
    Err.BelowG (GBits.app g g') (Err.app ε ε') c ↔ Err.BelowG g ε c ∧ Err.BelowG g' ε' c

def belowG_max : Prop :=
  ∀ (s : Shape) (g : GBits s) (a b : Err s) (c : ℝ≥0∞),
    Err.BelowG g a c → Err.BelowG g b c → Err.BelowG g (Err.max a b) c

def belowG_le : Prop :=
  ∀ (s : Shape) (g : GBits s) (a b : Err s) (c : ℝ≥0∞),
    Err.le a b → Err.BelowG g b c → Err.BelowG g a c

def belowG_errZero : Prop := ∀ (s : Shape) (g : GBits s) (c : ℝ≥0∞), Err.BelowG g (Err.zero s) c

def belowG_same_keep : Prop :=
  ∀ (s : Shape) (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
    Err.BelowG g ε c → Err.BelowG (g.pull (Samplers.keep s)) (Err.same (Samplers.keep s) ε) c

def belowG_same_dense : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (g : GBits s) (ε : Err s) (c κ : ℝ≥0∞),
    σ.Dense κ → Err.BelowG g ε c → Err.BelowG (g.pull σ) (Err.same σ ε) (c * κ)

def belowG_same_app : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t) (g : GBits s) (g' : GBits t) (ε₁ : Err s)
      (ε₂ : Err t) (c : ℝ≥0∞),
    Err.BelowG (g.pull σ) (Err.same σ ε₁) c → Err.BelowG (g'.pull τ) (Err.same τ ε₂) c →
    Err.BelowG ((GBits.app g g').pull (σ.app τ)) (Err.same (σ.app τ) (Err.app ε₁ ε₂)) c

def belowG_split : Prop :=
  ∀ (s : Shape) (P : SPlan s) (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
    Err.BelowG g ε c → Err.BelowG (g.split P) (Err.split P ε) c

def belowG_hoist : Prop :=
  ∀ (s : Shape) (μ : Marks s) (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
    Err.BelowG g ε c → Err.BelowG (g.hoist μ) (ε.hoist μ) c

/-- States: the bound is kept when rounds are cut and joined along a plan P with `P.OK` that joins
no two verifier messages (`P.NoChal`), if a round whose verifier message has one value has the
error 0 (`ε.UnitZero`). -/
def belowG_recut : Prop :=
  ∀ (s : Shape) (P : XPlan s), P.OK → P.NoChal →
    ∀ (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
      ε.UnitZero → Err.BelowG g ε c → Err.BelowG (g.recut P) (Err.recut P ε) c

def unitZero_of_belowG : Prop :=
  ∀ (s : Shape) (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
    c < 1 → g.UnitFree → Err.BelowG g ε c → ε.UnitZero

def unitFree_zero : Prop := ∀ s : Shape, (GBits.zero s).UnitFree

end Spec

theorem belowG_app : Spec.belowG_app
  | [], _, _, _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: s, t, (_, g), g', (_, ε), ε', c =>
      ⟨fun h =>
          ⟨⟨h.1, ((belowG_app s t g g' ε ε' c).1 h.2).1⟩, ((belowG_app s t g g' ε ε' c).1 h.2).2⟩,
        fun h => ⟨h.1.1, (belowG_app s t g g' ε ε' c).2 ⟨h.1.2, h.2⟩⟩⟩

theorem belowG_max : Spec.belowG_max
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, g), (e, a), (e', b), c, h, h' => ⟨by
      rcases Nat.le_total e e' with hle | hle
      · rw [show Nat.max e e' = e' from Nat.max_eq_right hle]; exact h'.1
      · rw [show Nat.max e e' = e from Nat.max_eq_left hle]; exact h.1, belowG_max s g a b c h.2 h'.2⟩

theorem belowG_le : Spec.belowG_le
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, g), (_, a), (_, b), c, hl, h =>
    ⟨le_trans (Nat.cast_le.2 hl.1) h.1, belowG_le s g a b c hl.2 h.2⟩

theorem belowG_errZero : Spec.belowG_errZero
  | [], _, _ => trivial
  | _ :: s, (_, g), c => ⟨by rw [Nat.cast_zero]; exact zero_le _, belowG_errZero s g c⟩

theorem belowG_same_keep : Spec.belowG_same_keep
  | [], _, _, _, _ => trivial
  | _ :: s, (_, g), (_, ε), c, h => ⟨h.1, belowG_same_keep s g ε c h.2⟩

theorem belowG_same_dense : Spec.belowG_same_dense
  | [], _, _, _, _, _, _, _ => trivial
  | r :: s, (a, σ), (b, g), (e, ε), c, κ, hd, h => ⟨by
      calc (e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) := h.1
        _ ≤ c * ((2 : ℝ≥0∞) ^ b * (κ * (Fintype.card a.Src : ℝ≥0∞))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hd.1)
        _ = c * κ * ((2 : ℝ≥0∞) ^ b * (Fintype.card a.Src : ℝ≥0∞)) := by
          ring, belowG_same_dense s σ g ε c κ hd.2 h.2⟩

theorem belowG_same_app : Spec.belowG_same_app
  | [], _, _, _, _, _, _, _, _, _, h => h
  | _ :: s, t, (_, σ), τ, (_, g), g', (_, ε₁), ε₂, c, h, h' =>
    ⟨h.1, belowG_same_app s t σ τ g g' ε₁ ε₂ c h.2 h'⟩

theorem belowG_split : Spec.belowG_split := by
  intro s P
  induction P with
  | nil => intro _ _ _ _; trivial
  | keep r P ih =>
      rintro ⟨b, g⟩ ⟨e, ε⟩ c h
      exact ⟨h.1, ih g ε c h.2⟩
  | cut k P ih =>
      rintro ⟨b, g⟩ ⟨e, ε⟩ c h
      exact ⟨by rw [Nat.cast_zero]; exact zero_le _, ih (b, g) (e, ε) c h⟩

/-- The kept rounds keep their bound. -/
theorem belowG_rest :
    ∀ (s : Shape) (μ : Marks s) (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
      Err.BelowG g ε c → Err.BelowG (GBits.rest μ g) (Err.rest μ ε) c
  | [], _, _, _, _, _ => trivial
  | _ :: s, (none, μ), (_, g), (_, ε), c, h => ⟨h.1, belowG_rest s μ g ε c h.2⟩
  | _ :: s, (some _, μ), (_, g), (_, ε), c, h => belowG_rest s μ g ε c h.2

theorem belowG_hoist : Spec.belowG_hoist := fun s μ g ε c h =>
  ⟨by rw [Nat.cast_zero]; exact zero_le _, belowG_rest s μ g ε c h⟩

theorem belowG_recut : Spec.belowG_recut := by
  intro s P
  induction P with
  | nil => intro _ _ _ _ _ _ _; trivial
  | keep r P ih =>
      rintro hP hn ⟨b, g⟩ ⟨e, ε⟩ c hu hb
      exact ⟨hb.1, ih hP hn g ε c hu.2 hb.2⟩
  | cut k P ih =>
      rintro hP hn ⟨b, g⟩ ⟨e, ε⟩ c hu hb
      exact ⟨by rw [Nat.cast_zero]; exact zero_le _, ih hP.2 hn (b, g) (e, ε) c hu hb⟩
  | @msg r1 r2 s u P ih =>
      rintro hP hn ⟨b1, b2, g⟩ ⟨e1, e2, ε⟩ c hu hb
      have h1 : Fintype.card r1.Chal = 1 := card_eq_one_of_forall hP.1
      have he : e1 = 0 := hu.1 h1
      have e : e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2 = e2 := by
        rw [he, h1, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
      refine ih hP.2 hn (b2, g) (e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2, ε) c
        ⟨fun hcard => ?_, hu.2.2⟩ ⟨?_, hb.2.2⟩
      · rw [e]
        exact hu.2.1 hcard
      · rw [e]
        exact hb.2.1
  | chal r1 r2 np P ih => intro _ hn; exact hn.elim

theorem unitZero_of_belowG : Spec.unitZero_of_belowG
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (b, g), (e, ε), c, hc, hg, h => ⟨fun h1 => by
      have h0 : (e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) := h.1
      rw [hg.1 h1, h1, pow_zero, Nat.cast_one, mul_one, mul_one] at h0
      have h2 : (e : ℝ≥0∞) < 1 := lt_of_le_of_lt h0 hc
      exact Nat.lt_one_iff.1 (by exact_mod_cast h2), unitZero_of_belowG s g ε c hc hg.2 h.2⟩

theorem unitFree_zero : Spec.unitFree_zero
  | [] => trivial
  | _ :: s => ⟨fun _ => rfl, unitFree_zero s⟩

end Iop
