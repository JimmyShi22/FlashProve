-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsX.lean: the parts' steps as a stretch of the lookup with parts, between the
joints Tied and Roots of Cb/Pv/KeyLookup/Letters.lean, over that file's one flat state record.

Definitions, statements and proofs. It lays the chain of Cb/Pv/KeyLookup/Parts.lean over the state
A.XS and ends it with a map back into A.XS. Only files of Cb/ and of this folder are imported.

Main names:
  A.partsD wP cP: the data of the chain: n := m - 1; root i := A.root x.st μ x.al i; the incoming
    form := x.all.mf. wP and cP say where the steps' own masks stand (three names and two a step, as
    TieP.wAt and TieP.cAt do for the tie): letters of this stretch.
  A.partsIn: the step without rounds into the chain: x ↦ (x.all.tg, x).
  A.partsBack      the step without rounds back into X: the first state with
                   roots i := ⟨form i, target i⟩ and the m - 1 rows
                   on the hiding coefficients behind the rows so far, in the order of the steps. No
                     other field turns (x.all stays
                   as it was: Roots does not read it).
  A.partsX: the block: partsIn, the m - 1 steps, partsBack : BkA Kc M A.XS A.XS Ex Wp.
  partsX_good: Good (GoodAt; the identity extracts) from A.jt R0 msg Mu A.Tied to
    A.jt R0 msg Mu A.Roots, for every riding joint R0 and every Mu.
  partsX_know: the field know of partsX_good, written out. Blocks without an honest side:
    Cb/Pv/KeyLookup/PartsK.lean.
  partsX_ll, partsX_rounds: its lists are partsErrs (m - 1) and partsVals q (m - 1); it has
    3 (m - 1) rounds. No premise.

Limits: partsX_good and partsX_know stand under 1 ≤ A.m alone (a public number; a clause of
Pub.Adm).
At m = 1 there is no round, and roots 0 is the claim that came in. The round in the further variable
sends all three coefficients of its polynomial; see Cb/Pv/KeyLookup/PartsShort.lean.

-/
import Cb.Pv.KeyLookup.Letters
import Cb.Pv.KeyLookup.PartsRows
import Cb.Pv.KeyLookup.PartsErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp

noncomputable section
namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)

/-- The parts' chain over the common state. -/
def partsD : PartsP E where
  St0 := A.XS
  J := A.J
  n := A.m - 1
  root := fun x μ i => A.root x.st μ x.al i
  inc := fun x => x.all.mf
  wAt := wP
  cAt := cP

/-- Into the chain. -/
def partsIn (x : A.XS) : E × ((A.partsD wP cP).lv 0).T.St := (x.all.tg, x)

/-- The first state, read off the state after the steps. -/
def partsOld (y : E × ((A.partsD wP cP).lv (A.partsD wP cP).n).T.St) : A.XS :=
  ((A.partsD wP cP).lv (A.partsD wP cP).n).base y.2

/-- The rows on the steps' hiding coefficients, in the order of the steps. -/
def partsRows (y : E × ((A.partsD wP cP).lv (A.partsD wP cP).n).T.St) : List (Row E A.J) :=
  ((A.partsD wP cP).rowsAt (A.partsD wP cP).n y.2).reverse

/-- Back into the common state. -/
def partsBack (y : E × ((A.partsD wP cP).lv (A.partsD wP cP).n).T.St) : A.XS :=
  { A.partsOld wP cP y with
    roots := fun i =>
      ⟨(A.partsD wP cP).formAt (A.partsD wP cP).n y i,
        (A.partsD wP cP).tgtAt (A.partsD wP cP).n y i⟩
    rows := (A.partsOld wP cP y).rows ++ A.partsRows wP cP y }

/-- Stretch 3. -/
def partsX (Ex : ExtSpec) {M : Type} (Wp Kc : Type) (msg : M → A.J → E) :
    BkA Kc M A.XS A.XS Ex Wp :=
  ((A.partsD wP cP).afterA msg (mapA Kc M Ex Wp (A.partsIn wP cP)) (A.partsD wP cP).n).postM
    (A.partsBack wP cP)

end Dat
end

section
variable {E : Type} [Field E] [Fintype E] (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)

/-- The chain's first claim is the common joint's claim on the product of all roots. -/
theorem partsX_claim0 (hm : 1 ≤ A.m) (x : A.XS) (μ : A.J → E) :
    (A.partsD wP cP).claim 0 (A.partsIn wP cP x) μ ↔ x.all.Holds (A.rest x.st μ x.al 0) μ := by
  show (∏ i ∈ Finset.Ico 0 (A.m - 1 + 1), A.root x.st μ x.al i) + ∑ j, x.all.mf j * μ j = x.all.tg ↔
    (∏ i ∈ Finset.Ico 0 A.m, A.root x.st μ x.al i) + ∑ j, x.all.mf j * μ j = x.all.tg
  rw [Nat.sub_add_cancel hm]

/-- «Roots» at the state handed back. -/
theorem partsX_roots (hm : 1 ≤ A.m) (y : E × ((A.partsD wP cP).lv (A.partsD wP cP).n).T.St)
    (μ : A.J → E) :
    A.Roots (A.partsBack wP cP y) μ ↔
      (A.Side (A.partsOld wP cP y) μ ∧ A.AllPlanes (A.partsOld wP cP y) μ) ∧
        RowsHold ((A.partsD wP cP).rowsAt (A.partsD wP cP).n y.2) μ ∧
          (A.partsD wP cP).Claims y μ := by
  have hn : ∀ i, i < A.m ↔ i ≤ (A.partsD wP cP).n := fun i => by
    show i < A.m ↔ i ≤ A.m - 1
    omega
  constructor
  · rintro ⟨⟨hb, hr⟩, hp, hc⟩
    exact ⟨⟨⟨hb, fun r h => hr r (List.mem_append_left _ h)⟩, hp⟩,
      fun r h => hr r (List.mem_append_right _ (List.mem_reverse.2 h)),
      fun i hi => hc i ((hn i).2 hi)⟩
  · rintro ⟨⟨⟨hb, hr⟩, hp⟩, hr', hc⟩
    refine ⟨⟨hb, fun r h => ?_⟩, hp, fun i hi => hc i ((hn i).1 hi)⟩
    rcases List.mem_append.1 h with h | h
    · exact hr r h
    · exact hr' r (List.mem_reverse.1 h)

variable (Ex : ExtSpec) (M Wp Kc : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
  (Mu : A.St → (A.J → E) → Prop)

/-- Stretch 3: from «Tied» to «Roots». -/
theorem partsX_good (hm : 1 ≤ A.m) :
    (A.partsX wP cP Ex Wp Kc msg).Good (A.jt R0 msg Mu A.Tied) (A.jt R0 msg Mu A.Roots) := by
  have g0 : (mapA Kc M Ex Wp (A.partsIn wP cP)).Good (A.jt R0 msg Mu A.Tied)
      ((A.partsD wP cP).jtAt msg
        (cj R0 msg (fun x : A.XS => x.st)
          (fun x μ => (A.Side x μ ∧ A.AllPlanes x μ) ∧ Mu x.st μ)
          (fun x μ => A.Side x μ ∧ A.AllPlanes x μ)) 0) := by
    refine mapA_good Kc M _ _ Ex Wp (A.partsIn wP cP) _ _ ?_ (fun _ _ h => h) (fun _ => rfl) ?_
    · intro x y w h
      exact ⟨⟨h.1, ⟨h.2.1.1, h.2.1.2.2⟩, h.2.2⟩, (partsX_claim0 A wP cP hm x (msg w.1)).2 h.2.1.2.1⟩
    · intro x y w _ h
      exact ⟨h.1.1, h.1.2.1, (partsX_claim0 A wP cP hm x (msg w.1)).1 h.2, h.1.2.2⟩
  have g1 := parts_after (A.partsD wP cP) Ex M Wp Kc msg _ _ _ g0 (A.partsD wP cP).n (Nat.le_succ _)
  have e := partsR_end (A.partsD wP cP) Ex Kc A.St M Wp R0 msg (fun x : A.XS => x.st)
    (fun x μ => (A.Side x μ ∧ A.AllPlanes x μ) ∧ Mu x.st μ)
    (fun x μ => A.Side x μ ∧ A.AllPlanes x μ)
  have g2 := Eq.mp (congrArg (BkA.Good _ (A.jt R0 msg Mu A.Tied)) e) g1
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ (A.jt R0 msg Mu A.Roots) _ _
    (A.partsBack wP cP) g2 ?_ (fun _ _ h => h) (fun _ => rfl) ?_
  · intro y z w h
    exact ⟨h.1, (partsX_roots A wP cP hm y (msg w.1)).2 ⟨h.2.1.1, h.2.2⟩, h.2.1.2⟩
  · intro y z w _ h
    have := (partsX_roots A wP cP hm y (msg w.1)).1 h.2
    exact ⟨h.1, this.1, this.2⟩

/-- The field know of partsX_good. Road (k) proper: PartsK.lean. -/
theorem partsX_know (hm : 1 ≤ A.m) (m : M) :
    (A.partsX wP cP Ex Wp Kc msg).R.red.Know (A.jt R0 msg Mu A.Tied).on
      (fun a wp => (A.jt R0 msg Mu A.Tied).relR a (m, wp))
      (fun b wp => (A.jt R0 msg Mu A.Roots).relR b (m, wp))
      (fun _ _ wp => wp) (A.partsX wP cP Ex Wp Kc msg).P.err :=
  (partsX_good A wP cP Ex M Wp Kc R0 msg Mu hm).know m

/-- Its lists. -/
theorem partsX_ll :
    LL (A.partsX wP cP Ex Wp Kc msg) (partsErrs (A.m - 1)) (partsVals (Fintype.card E) (A.m - 1)) :=
  ll_postM (ll_after (A.partsD wP cP) Ex M Wp Kc msg _ [] [] (ll_mapA Ex M Wp Kc _) (A.m - 1)) _

theorem partsX_rounds : (A.partsX wP cP Ex Wp Kc msg).R.shape.length = 3 * (A.m - 1) := by
  have h := parts_rounds (A.partsD wP cP) Ex M Wp Kc msg (mapA Kc M Ex Wp (A.partsIn wP cP))
    (A.m - 1)
  have e : (mapA Kc M Ex Wp (A.partsIn wP cP)).R.shape.length = 0 := rfl
  rw [e, Nat.zero_add] at h
  exact h

end
end Lk6
