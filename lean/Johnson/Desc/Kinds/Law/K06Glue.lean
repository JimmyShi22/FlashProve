-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Glue.lean: THE GLUE, for reads that are true at every index (`k06GlueAll`; from it
Clamp.lean has `K06GlueStatement` of K06Statement.lean): each key and
each of the policy's four forms, at the hidden scalars and the sent reads, is the element of which
HeadLaw.lean's lemmas speak. `worldE`: the world of a ledger, mask entries and sent reads;
`rd_atWorld`: the statement's `atWorld` is the value of the form there. Both sides have the
closed form of General.lean (World.lean for the one, Lemma2a.lean for the other) and are canonical.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Statement
import Johnson.Desc.Kinds.Law.World
import Johnson.Desc.Kinds.Law.Lemma2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE okE addE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)

/-- The world of a ledger, mask entries and sent reads. -/
def worldE (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) : World K :=
  ⟨fun j => rd (hidden F mask j), fun t r i => rd (ent t r i)⟩

theorem rd_atWorld (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) (f : Form) :
    rd (atWorld F mask ent f) = vW (worldE F mask ent) f := by
  -- The induction on the list is run once, at letters f, r, v, in which nothing can be unfolded;
  -- the values lie in the field K. With it run twice, at the concrete steps, a
  -- second kernel did not return within its memory. Why it did not is not known.
  have fold : ∀ (α β : Type) (f : β → α → β) (r : β → K) (v : α → K),
      (∀ b a, r (f b a) = r b + v a) →
      ∀ (l : List α) (b : β), r (l.foldl f b) = (l.map v).sum + r b := by
    intro α β f r v hf l
    induction l with
    | nil =>
      intro b
      rw [List.foldl_nil, List.map_nil, List.sum_nil, zero_add]
    | cons x xs ih =>
      intro b
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, hf]
      ring
  have g1 : ∀ (l : List (Nat × E)) (s : E),
      rd (l.foldl (fun s x => s + x.2 * hidden F mask x.1) s)
        = (l.map (OnBytes.Model.slotValue Reading.gl (worldE F mask ent))).sum + rd s :=
    fold (Nat × E) E (fun s x => s + x.2 * hidden F mask x.1) rd
      (OnBytes.Model.slotValue Reading.gl (worldE F mask ent)) fun b a => by
        simp only [OnBytes.Model.slotValue, worldE]
        show rd (b + a.2 * hidden F mask a.1) = rd b + rd a.2 * rd (hidden F mask a.1)
        rw [rd_add, rd_mul]
  have g2 : ∀ (l : List OnBytes.Model.Ent) (s : E),
      rd (l.foldl (fun s x => s + x.coef * ent x.tree x.row x.idx) s)
        = (l.map (OnBytes.Model.Ent.value Reading.gl (worldE F mask ent))).sum + rd s :=
    fold OnBytes.Model.Ent E (fun s x => s + x.coef * ent x.tree x.row x.idx) rd
      (OnBytes.Model.Ent.value Reading.gl (worldE F mask ent)) fun b a => by
        simp only [OnBytes.Model.Ent.value, worldE]
        show rd (b + a.coef * ent a.tree a.row a.idx)
          = rd b + rd a.coef * rd (ent a.tree a.row a.idx)
        rw [rd_add, rd_mul]
  unfold atWorld atHidden vW Aff.value
  rw [← Array.foldl_toList, g2, ← Array.foldl_toList, g1]
  show _ + (_ + rd f.const) = _ + _ + rd f.const
  ring

/-! ## Canonical -/

theorem okE_foldl_add {α : Type} (g : α → E) : ∀ (l : List α) (s : E), okE s = true →
    okE (l.foldl (fun s x => s + g x) s) = true := by
  -- The step of the fold is taken at letters P and f, in which nothing can be unfolded. With the
  -- step taken by definition, at the field's own addition, a second kernel did not return
  -- within its memory. Why it did not is not known.
  have keeps : ∀ (β : Type) (P : β → Prop) (f : β → α → β), (∀ b a, P (f b a)) →
      ∀ (l : List α) (b : β), P b → P (l.foldl f b) := by
    intro β P f hf l
    induction l with
    | nil =>
      intro b h
      rw [List.foldl_nil]
      exact h
    | cons x xs ih =>
      intro b _
      rw [List.foldl_cons]
      exact ih (f b x) (hf b x)
  have sum : ∀ a b : E, okE (a + b) = true := fun a b => okE_addE a b
  exact fun l s h =>
    keeps E (fun e => okE e = true) (fun s x => s + g x) (fun b a => sum b (g a)) l s h

theorem okE_atWorld (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) (f : Form)
    (h : okE f.const = true) : okE (atWorld F mask ent f) = true := by
  unfold atWorld atHidden
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact okE_foldl_add _ _ _ (okE_foldl_add _ _ _ h)

/-- For a canonical element "is read as 0" and "is the record 0" are one. -/
theorem zero_of_rd {x : E} (hx : okE x = true) (h : rd x = 0) : x = 0 :=
  eq_of_rd hx okE_zero (h.trans rd_zero.symm)

variable [Sizes] [Policy] [Request] [Token]

section Letters
variable [FinalNorm.In] [In]

theorem filledIn_of (h : WeightsOk) : FilledIn := ⟨h.ew, h.wsum, h.wx, h.below⟩

variable [Heard] [Reads]

/-- The reads are true AT EVERY INDEX: a device of the proofs: no real run's letters meet it; the
clamped letters of Clamp.lean do. -/
def TrueReadsAll (c : Cells) (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) : Prop :=
  ∀ r i, atWorld F mask ent (entry r i) = readAt c r.of i

theorem filledW_of {c : Cells} {F : Fork} {mask : Nat → E} {ent : Nat → Nat → Nat → E}
    (hw : WeightsOk) (hr : TrueReadsAll c F mask ent)
    (hc : (2 ^ lPd : E) * atWorld F mask ent logits.claimed.var = trueSum c) :
    FilledW (worldE F mask ent) c where
  hentry := fun r i => by rw [← rd_atWorld, hr r i]
  hclaimed := by
    have hr2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
    have h1 := congrArg rd hc
    rw [rd_mul, rd_pow, rd_atWorld, hr2] at h1
    rw [rd_mul, rd_inv, rd_pow, hr2, ← h1, inv_mul_cancel_left₀ (two_pow_ne_zero _)]
  hin := filledIn_of hw

theorem okE_key_const (k : Key) : okE (key k).const = true := by
  cases k <;> exact okE_addMul _ _ _

/-- The glue, for reads that are true at every index. -/
theorem k06GlueAll (c : Cells) (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E)
    (hreq : Request.ok = true) (hy : y < V) (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt)
    (hr : TrueReadsAll c F mask ent)
    (hc : (2 ^ lPd : E) * atWorld F mask ent logits.claimed.var = trueSum c) :
    (∀ k, atWorld F mask ent (key k) = keyAt c ptOf k) ∧
      atWorld F mask ent clip = clipAt c ptOf ∧ atWorld F mask ent table = tableAt c ptOf ∧
      atWorld F mask ent mean = meanAt c ∧ atWorld F mask ent count = countAt c := by
  have hF := filledW_of hw hr hc
  refine ⟨fun k => ?_, ?_, ?_, ?_, ?_⟩
  · apply eq_of_rd (okE_atWorld _ _ _ _ (okE_key_const k)) (okE_keyAt c ptOf k)
    rw [rd_atWorld, vW_keyG hF hzt hreq hy k, rd_keyAt c ptOf hzt hreq hy k]
    refine Finset.sum_congr rfl fun x hx => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    have hU : Ut k x = rd (ptOf.ew k x) := by
      unfold Ut
      rw [hw.ew k x (Finset.mem_range.mp hx)]
      rfl
    rw [hU]
    rfl
  · have hk : okE (clip).const = true := okE_addMul _ _ _
    apply eq_of_rd (okE_atWorld F mask ent clip hk) (okE_clipAt c ptOf)
    rw [rd_atWorld, vW_clip hF, rd_clipAt]
    rfl
  · have hk : okE (table).const = true := okE_addMul _ _ _
    apply eq_of_rd (okE_atWorld F mask ent table hk) (okE_tableAt c ptOf)
    rw [rd_atWorld, vW_tableG hF, rd_tableAt]
    rfl
  · have hk : okE (mean).const = true := okE_addMul _ _ _
    have hm : okE (meanAt c) = true := okE_addMul _ _ _
    apply eq_of_rd (okE_atWorld F mask ent mean hk) hm
    rw [rd_atWorld, vW_mean hF, rd_mean]
  · have hk : okE (count).const = true := okE_addMul _ _ _
    have hm : okE (countAt c) = true := okE_addMul _ _ _
    apply eq_of_rd (okE_atWorld F mask ent count hk) hm
    rw [rd_atWorld, vW_count hF, rd_count]

end Letters

end VerifiableInference.Desc.Kinds.Head.Law

