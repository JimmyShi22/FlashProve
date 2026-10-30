-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsK.lean: the parts' chain as blocks without an honest side, with the sumcheck as
a letter; knowledge soundness of the stretch between the joints Tied and Roots.

Definitions, statements and proofs. No definition of this file names an honest prover, and no
statement does but the two bridges toK_after and toK_partsX, which say that the blocks of
Cb/Pv/KeyLookup/Parts.lean and Cb/Pv/KeyLookup/PartsX.lean, their honest sides taken off, are the
blocks of this file. No premise reads the witness. It uses KnowAt, BkK, know_seq, know_postM,
know_of_good, knowAt_congr, toK (Cb/Pv/Lookup/Know/KnowAt.lean) and PscLtK, FullK, our_know, lib,
lib_ourK (Cb/Pv/Lookup/Know/LtK.lean).

Main names:
  SK : PscLtK E Ex: the sumcheck as a letter: for every PscPar a verifier and its errors.
  D.stepK SK l := (SK.full (D.lv l).T.par).postM (D.nxt l). D.afterK SK b k: the block b, then the
    steps 0, .., k - 1, by recursion from b.
  D.LtK SK Wp Kc msg k: what is asked of the letter: SK.FullK at the steps below k (knowledge
    soundness from the sum claim to the output rows, beside every riding joint).
  mapK Ex φ: a step without rounds as a block of its own.
  A.partsXK wP cP SK: the stretch: partsIn, the m - 1 steps, partsBack.
  partsK_step: FullK at step l and l ≤ n give Know from D.jtAt l to D.jtAt (l + 1).
  partsK_after: b Know from A to D.jtAt 0, LtK below k and k ≤ n + 1 give D.afterK SK b k Know from
    A
    to D.jtAt k.
  mapK_know: a map on the explicit part has Know, from the two conditions on the field on and on the
    relaxed relation alone.
  partsXK_know: 1 ≤ A.m and LtK below m - 1 give Know from A.jt R0 msg Mu A.Tied to
    A.jt R0 msg Mu A.Roots.
  partsK_lib, partsXK_lib: at the sumcheck of Cb/Ld/LdPsc.lean (PscLtK.lib) what is asked of the
    letter is proved, from parts_ok; so partsXK_lib stands under 1 ≤ A.m alone.

Limits: at PscLtK.lib the sumcheck's knowledge soundness is the field know of psc_goodAt
(Cb/Ld/LdPscSig.lean), and mapK_know comes out of mapA_good at exact relations that are False; the
rules that join blocks (know_seq, know_postM) read no honest side. Knowledge soundness alone does
not say that the verifier accepts anything: Cb/Pv/KeyLookup/PartsTotal.lean. The short format as a
value of the letter: Cb/Pv/KeyLookup/Short0.lean, Cb/Pv/KeyLookup/PartsShort.lean.

-/
import Cb.Pv.Lookup.Know.LtK
import Cb.Pv.KeyLookup.PartsX

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn

noncomputable section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

namespace PartsP
variable (D : PartsP E) (SK : PscLtK E Ex)

/-- Step l, with the step without rounds after it. -/
def stepK (l : ℕ) : BkK (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex :=
  (SK.full (D.lv l).T.par).postM (D.nxt l)

/-- The block b, then the steps 0, .., k - 1. -/
def afterK {X : Type} (b : BkK X (E × (D.lv 0).T.St) Ex) : (k : ℕ) → BkK X (E × (D.lv k).T.St) Ex
  | 0 => b
  | k + 1 => (afterK b k).seq (D.stepK SK k)

/-- What is asked of the letter, at the steps below k. -/
def LtK {M : Type} (Wp Kc : Type) (msg : M → D.J → E) (k : ℕ) : Prop :=
  ∀ l < k, SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l)

end PartsP

/-- A step without rounds as a block of its own. -/
def mapK {X X' : Type} (Ex : ExtSpec) (φ : X → X') : BkK X X' Ex :=
  ⟨IOR.pure (fun x => some (φ x)) (ExtMap.id Ex), ()⟩

/-- Stretch 3, the verifier's side alone. -/
def Dat.partsXK (A : Dat E) (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J)
    (cP : ℕ → Bool → A.J) (SK : PscLtK E Ex) : BkK A.XS A.XS Ex :=
  ((A.partsD wP cP).afterK SK (mapK Ex (A.partsIn wP cP)) (A.partsD wP cP).n).postM
    (A.partsBack wP cP)

end

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

theorem mapK_know {K M X X' Wp : Type} (φ : X → X') (A : Rels K X Ex (M × Wp))
    (B : Rels K X' Ex (M × Wp)) (h2 : ∀ x y, A.on (x, y) → B.on (φ x, y))
    (h4 : ∀ x y w, A.on (x, y) → B.relR (φ x, y) w → A.relR (x, y) w) : (mapK Ex φ).Know A B :=
  knowAt_congr
    (know_of_good (mapA_good Unit M X X' Ex Wp φ ⟨fun _ _ _ => False, A.relR, A.on, fun _ => ()⟩
      ⟨fun _ _ _ => False, B.relR, B.on, fun _ => ()⟩ (fun _ _ _ h => h.elim) h2 (fun _ => rfl) h4))
    rfl rfl rfl rfl

variable (D : PartsP E) (SK : PscLtK E Ex) (M Wp Kc : Type) (msg : M → D.J → E)
  (A0 : Rels Kc D.St0 Ex (M × Wp))

theorem partsK_step (l : ℕ) (hL : SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l))
    (hl : l ≤ D.n) :
    (D.stepK SK l).Know (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1)) := by
  have g1 := SK.our_know M Wp Kc (D.lv l).T (D.msgAt M msg l) hL (D.ride msg A0 l)
  rw [parts_jt D Ex M Wp Kc msg A0 l hl] at g1
  refine know_postM (B' := D.jtAt msg A0 (l + 1)) (D.nxt l) g1 (fun _ _ h => h) ?_
  intro o y w _ h
  refine ⟨h.1.1, h.1.2.1, fun a => ?_⟩
  rcases D.cover l a with rfl | rfl
  · exact (parts_next D l o (msg w.1)).2 h.2
  · exact h.1.2.2

theorem partsK_after {X : Type} (b : BkK X (E × (D.lv 0).T.St) Ex) (A : Rels Kc X Ex (M × Wp))
    (hb : b.Know A (D.jtAt msg A0 0)) :
    ∀ k, D.LtK SK Wp Kc msg k → k ≤ D.n + 1 → (D.afterK SK b k).Know A (D.jtAt msg A0 k)
  | 0, _, _ => hb
  | k + 1, hL, hk =>
    know_seq
      (partsK_after b A hb k (fun l hl => hL l (Nat.lt_succ_of_lt hl)) (Nat.le_of_succ_le hk))
      (partsK_step D SK M Wp Kc msg A0 k (hL k (Nat.lt_succ_self k)) (Nat.le_of_succ_le_succ hk))

/-- At the library's own sumcheck what is asked of the letter is proved. -/
theorem partsK_lib (k : ℕ) : D.LtK (PscLtK.lib E Ex) Wp Kc msg k := fun l _ =>
  PscLtK.lib_ourK M Wp Kc (D.lv l).T (D.msgAt M msg l) (parts_ok D l).1 (parts_ok D l).2.2.1
    (parts_ok D l).2.2.2 (parts_ok D l).2.1

/-- The chain of Parts.lean without its honest side is this chain at the library's letter. -/
theorem toK_after {X : Type} (b : BkA Kc M X (E × (D.lv 0).T.St) Ex Wp) :
    ∀ k, toK (D.afterA msg b k) = D.afterK (PscLtK.lib E Ex) (toK b) k
  | 0 => rfl
  | k + 1 => by
    show (toK (D.afterA msg b k)).seq (toK (D.stepA Ex Wp Kc msg k)) = _
    rw [toK_after b k]
    rfl

end

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)
variable (SK : PscLtK E Ex) (M Wp Kc : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
  (Mu : A.St → (A.J → E) → Prop)

/-- Stretch 3 by road (k): from «Tied» to «Roots». -/
theorem partsXK_know (hm : 1 ≤ A.m) (hL : (A.partsD wP cP).LtK SK Wp Kc msg (A.m - 1)) :
    (A.partsXK wP cP SK).Know (A.jt R0 msg Mu A.Tied) (A.jt R0 msg Mu A.Roots) := by
  have g0 : (mapK Ex (A.partsIn wP cP)).Know (A.jt R0 msg Mu A.Tied)
      ((A.partsD wP cP).jtAt msg
        (cj R0 msg (fun x : A.XS => x.st)
          (fun x μ => (A.Side x μ ∧ A.AllPlanes x μ) ∧ Mu x.st μ)
          (fun x μ => A.Side x μ ∧ A.AllPlanes x μ)) 0) := by
    refine mapK_know (A.partsIn wP cP) _ _ (fun _ _ h => h) ?_
    intro x y w _ h
    exact ⟨h.1.1, h.1.2.1, (partsX_claim0 A wP cP hm x (msg w.1)).1 h.2, h.1.2.2⟩
  have g1 := partsK_after (A.partsD wP cP) SK M Wp Kc msg _ _ _ g0 (A.partsD wP cP).n hL
    (Nat.le_succ _)
  have e := partsR_end (A.partsD wP cP) Ex Kc A.St M Wp R0 msg (fun x : A.XS => x.st)
    (fun x μ => (A.Side x μ ∧ A.AllPlanes x μ) ∧ Mu x.st μ)
    (fun x μ => A.Side x μ ∧ A.AllPlanes x μ)
  have g2 := Eq.mp (congrArg (BkK.Know _ (A.jt R0 msg Mu A.Tied)) e) g1
  refine know_postM (B' := A.jt R0 msg Mu A.Roots) (A.partsBack wP cP) g2 (fun _ _ h => h) ?_
  intro y z w _ h
  have := (partsX_roots A wP cP hm y (msg w.1)).1 h.2
  exact ⟨h.1, this.1, this.2⟩

/-- At the library's own sumcheck: under 1 ≤ m alone. -/
theorem partsXK_lib (hm : 1 ≤ A.m) :
    (A.partsXK wP cP (PscLtK.lib E Ex)).Know (A.jt R0 msg Mu A.Tied) (A.jt R0 msg Mu A.Roots) :=
  partsXK_know A wP cP _ M Wp Kc R0 msg Mu hm (partsK_lib (A.partsD wP cP) M Wp Kc msg _)

/-- The block of PartsX.lean without its honest side. -/
theorem toK_partsX : toK (A.partsX wP cP Ex Wp Kc msg) = A.partsXK wP cP (PscLtK.lib E Ex) := by
  show (toK ((A.partsD wP cP).afterA msg (mapA Kc M Ex Wp (A.partsIn wP cP))
    (A.partsD wP cP).n)).postM (A.partsBack wP cP) = _
  rw [toK_after]
  rfl

end
end Lk6
