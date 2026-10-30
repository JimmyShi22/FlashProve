-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeysHave.lean: WHAT THE FORMS' ARITHMETIC KEEPS IS KEPT BY THE OUTPUT HEAD's
NINE KEYS, BY THE SIX CALLS' KEY VECTORS AND BY THE FORM OF THE RUN "join": and so every slot that
the form of "join" names is one that the head's own hearing has taken, or one that the lookup's last
claim names. Statements and proofs. Beside Law/FormsAll.lean (the 35 forms) and
Law/SlotsFilled.lean.

  MoreHas P        P of the three things that the keys name and the 35 forms do not: the entries of
                   the read "wide" of the normalization; the claimed sums of the sumchecks "normed"
                   and "logits".
  keyN_has, key_has, keyVector_has   the normalization's four keys; the head's five; a call's key
                   vector.
  joinForm_has     the form of "join" at forms that have P, where the lookup's last claim has P.
  more_slotsIn     where the head's hearing returns, from a well laid ledger: MoreHas of "names
                   slots of the hearing's own stretch alone", at reads whose entries name no slot.
  keys_slotsIn     so of every call's key vector.

WHAT IT IS NOT. Nothing on the entries that the forms name. Nothing on values. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SlotsFilled
import Johnson.Desc.Kinds.Law.JoinValue
import Johnson.Desc.Kinds.HeadFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Later Sized)
open Norm (lt ls d lPd T S2)

section Have

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard] [FinalNorm.Reads] [Reads]

/-- P of what the keys name beside what the 35 forms name. -/
structure MoreHas (P : Form → Prop) : Prop where
  wide : ∀ i, P (FinalNorm.wide i)
  nmClaimed : P FinalNorm.normed.claimed.var
  lgClaimed : P logits.claimed.var

variable {P : Form → Prop} (C : Kept P) (R : ReadsHave P) (H : HeardHas P) (M : MoreHas P)
include C R H M

theorem wideAtN_has (k : FinalNorm.Key) (f0 : Nat) : P (FinalNorm.wideAt k f0) := by
  unfold FinalNorm.wideAt
  exact C.sums _ _ fun i => C.sums _ _ fun l => C.smulE _ (M.wide _)

theorem wideAt_has (k : Key) (f0 nl stride : Nat) : P (wideAt k f0 nl stride) := by
  unfold wideAt
  exact C.sums _ _ fun i => C.sums _ _ fun l => C.smulE _ (R.head .wideAtKeys _)

theorem mid_has (k : Key) (v0 : Nat) : P (mid k v0) := by
  unfold mid
  exact C.Eadd _ (wideAt_has C R H M _ _ _ _)

theorem low_has (k : Key) : P (low k) := by
  unfold low
  exact C.Eadd _ (wideAt_has C R H M _ _ _ _)

theorem tableValue_has (k : Key) (v0 : Nat) : P (tableValue k v0) := by
  unfold tableValue
  exact C.Eadd _ (wideAt_has C R H M _ _ _ _)

/-- **The normalization's four keys.** -/
theorem keyN_has (more : Nat) (k : FinalNorm.Key) : P (FinalNorm.key more k) := by
  cases k
  · unfold FinalNorm.key
    exact C.sub (C.sub (C.addE M.nmClaimed _) (C.smulN _ (wideAtN_has C R H M _ _)))
      (C.smulN _ (wideAtN_has C R H M _ _))
  · unfold FinalNorm.key
    exact C.smulN _ (C.Eadd _ (wideAtN_has C R H M _ _))
  · unfold FinalNorm.key
    refine C.addE (C.add (wideAtN_has C R H M _ _) (C.smulN _ (C.sums _ _ fun k => C.smulE _ ?_))) _
    unfold FinalNorm.actAt
    exact C.add (R.norm .actAtKeys _) (C.smulN _ (R.norm .actAtKeys _))
  · unfold FinalNorm.key
    exact C.sums _ _ fun j => C.smulE _ (C.addN (R.norm .rowAtKeys _) _)

/-- **The head's five keys.** -/
theorem key_has (k : Key) : P (key k) := by
  cases k
  · unfold key top
    exact C.smulE _ (C.sub (C.sub (C.subE (C.add (C.smulN _ M.lgClaimed)
      (C.smulE _ (C.add (atCosts_has C R H _) (C.smulN _ (atCosts_has C R H _))))) _)
      (C.smulN _ (mid_has C R H M _ _))) (low_has C R H M _))
  · exact mid_has C R H M _ _
  · exact low_has C R H M _
  · unfold key
    exact C.add (mid_has C R H M _ _) (C.smulN _ (tableValue_has C R H M _ _))
  · unfold key
    exact C.add (mid_has C R H M _ _) (C.smulN _ (tableValue_has C R H M _ _))

/-- **A call's key vector.** -/
theorem keyVector_has (padding : E) (keys : List PlaceKey) : P (keyVector key padding keys) := by
  unfold keyVector
  have step : ∀ (l : List Form) (a : Form), P a → (∀ f ∈ l, P f) → P (l.foldl (· + ·) a) := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hl
      exact ih _ (C.add ha (hl x List.mem_cons_self))
        fun f hf => hl f (List.mem_cons_of_mem _ hf)
  refine step _ _ (C.const _) fun f hf => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hf
  cases k with
  | inl k => exact keyN_has C R H M _ _
  | inr k => exact key_has C R H M _

end Have

/-- **The form of "join".** -/
theorem joinForm_has {P : Form → Prop} (C : Kept P) (g : OnBytes.Model.Forest.Heard)
    (KF : Array Aff) (hK : ∀ c, c < KF.size → P (KF.getD c (Aff.ofConst zeroE))) (hc : P g.cEnd) :
    P (Came.joinForm g KF) := by
  unfold Came.joinForm
  refine C.sub (C.add ?_ (C.const _)) hc
  have step : ∀ (l : List Nat) (a : Form), P a → (∀ c ∈ l, c < KF.size) →
      P (l.foldl (Came.joinStep g KF) a) := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hl
      refine ih _ ?_ fun c hc' => hl c (List.mem_cons_of_mem _ hc')
      unfold Came.joinStep
      exact C.addMul _ ha (C.sub (C.const _) (hK x (hl x List.mem_cons_self)))
  exact step _ _ (C.const _) fun c hc' => List.mem_range.mp hc'

section Slots

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **Where the head's hearing returns.** -/
theorem more_slotsIn [FinalNorm.Reads] [Reads] {F G : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left))
    (hw : ∀ i, (FinalNorm.wide i).slots = #[]) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    MoreHas (SlotsIn F.next G.next) := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  have sz : ∀ {X : Fork}, WellLaid X → Sized X := fun w => ⟨w.2.1, w.2.2, w.1⟩
  obtain ⟨G1, G2, l1, hNorm, wG1, wG2, hsN, hsL, _⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, _, _, h1, _, h3, h4, h5, wa, wb, wc⟩ :=
    norm_parts hW hNorm
  have n1 := (takes_send (sz hW) h1).next
  have n3 := (takes_level (sz wa) h3).next
  have n4 := (takes_send (sz wb) h4).next
  have n5 := (takes_sumcheck (sz wc) h5).next
  have n6 := (takes_sumcheck (sz wG1) hsN).next
  have n7 := (takes_sumcheck (sz wG2) hsL).next
  obtain ⟨nC, _, _⟩ := sumcheck_slots (sz wG1) hsN
  obtain ⟨lC, _, _⟩ := sumcheck_slots (sz wG2) hsL
  exact
    { wide := fun i x hx => by
        rw [hw i] at hx
        simp at hx
      nmClaimed := nC.mono (by omega) (by omega)
      lgClaimed := lC.mono (by omega) (by omega) }

/-- **Every slot that a call's key vector names lies in the stretch that the hearing took.** -/
theorem keys_slotsIn [FinalNorm.Reads] [Reads] {F G : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (entry r i).slots = #[])
    (hw : ∀ i, (FinalNorm.wide i).slots = #[]) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    ∀ (padding : E) (keys : List PlaceKey), SlotsIn F.next G.next (keyVector key padding keys) := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  intro padding keys
  refine keyVector_has (kept_slotsIn F.next G.next) ⟨fun r i x hx => ?_, fun r i x hx => ?_⟩
    (heard_slotsIn hW h) (more_slotsIn hW h hw) padding keys
  · rw [hN r i] at hx
    simp at hx
  · rw [hR r i] at hx
    simp at hx

end Slots

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.keyVector_has
#print axioms VerifiableInference.Desc.Kinds.Head.Law.joinForm_has
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keys_slotsIn
