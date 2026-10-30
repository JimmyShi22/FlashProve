-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCall.lean: under `Std m` and `Test0 W` (the checks depend on block 0 alone) a
failed proof-of-work attempt that is not the last costs exactly one hash query under the rule
`ruleT`: the proof of `Spec.failCostsOne`, the statement of Compile/Batch/SpecOneCall.lean that is
about the rule alone. That header says what it says and what it does not. (Words of this library:
lean/GLOSSARY.md.)

  `ruleT_some`, `ruleT_none`, `ruleT_other`
      the rule at a query to `fb t` with proof-of-work bits (`Rom.ndTest`), at a query to `fb t`
      without them, at every other oracle (`needOf nb m`)
  `block0_fb`   block 0 of a Fiat-Shamir answer, for an encoding that splits answers as
                Compile/Batch/ImplOf.lean does (`Std m`), if 0 < K
  `test_block0`   under `Std m`, `Test0 W`: the check of an answer is the check of its block 0
  `shownT_rel`   under `Std m`, `Test0 W`: an answer and the answer as the rule shows it either
                 agree on what `needOf nb m` marks, or are both failed attempts that are not the
                 last
-/
import Compile.Batch.SpecOneCall
import Compile.EraseDead

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (needOf Std agree agree_of_Agree)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)
  (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam W.K L) lam)

theorem ruleT_some {t : Tag} {q : FbIn lam L t}
    {x : (Blk lam W.K → Bool) × Bool} (h : tryInfoT W t q.plain = some x) :
    ruleT W nb m (.fb t) q =
      ndTest (fun b0 => x.1 fun _ => b0) x.2 fun j' =>
        NeedA.ofNeed (needOf nb m) (.fb t) q j' (acc0 lam) := by
  funext j acc
  show (match tryInfoT W t q.plain with
    | some x =>
      ndTest (fun b0 => x.1 fun _ => b0) x.2
        (fun j' => NeedA.ofNeed (needOf nb m) (.fb t) q j' acc) j acc
    | none => NeedA.ofNeed (needOf nb m) (.fb t) q j acc) = _
  rw [h]
  rfl

theorem ruleT_none {t : Tag} {q : FbIn lam L t} (h : tryInfoT W t q.plain = none) :
    ruleT W nb m (.fb t) q = NeedA.ofNeed (needOf nb m) (.fb t) q := by
  funext j acc
  show (match tryInfoT W t q.plain with
    | some x =>
      ndTest (fun b0 => x.1 fun _ => b0) x.2
        (fun j' => NeedA.ofNeed (needOf nb m) (.fb t) q j' acc) j acc
    | none => NeedA.ofNeed (needOf nb m) (.fb t) q j acc) = _
  rw [h]

theorem ruleT_other {o : OracleName} (ho : ∀ t, o ≠ .fb t) (q : domOf lam L o) :
    ruleT W nb m o q = NeedA.ofNeed (needOf nb m) o q := by
  cases o with
  | fb t => exact absurd rfl (ho t)
  | _ => rfl

variable {W nb m}

theorem blocks_fb (hm : Std m) (t : Tag) : m.blocks (.fb t) = W.K + 1 := hm.blocks _

/-- block 0 of a Fiat-Shamir answer -/
theorem block0_fb (hm : Std m) {t : Tag} (r : rngOf lam W.K (.fb t)) (hK : 0 < W.K) :
    block0 m (.fb t) r = r.1 ⟨0, hK⟩ := by
  have hb : 0 < m.blocks (.fb t) := by rw [blocks_fb hm]; omega
  unfold block0 extBl
  rw [dif_pos hb, hm.rng]
  show Fin.snoc (α := fun _ : Fin (W.K + 1) => Dig lam) r.1 r.2 (Fin.castSucc ⟨0, hK⟩) = _
  rw [Fin.snoc_castSucc]

/-- Under `Std m`, `Test0 W`: the check of an answer is the check of its block 0. -/
theorem test_block0 (hm : Std m) (h0 : Test0 W) {t : Tag} {z : PlainPart (shapeOf L t) (annOf L t)}
    {x : (Blk lam W.K → Bool) × Bool} (h : tryInfoT W t z = some x) (r : rngOf lam W.K (.fb t)) :
    x.1 r.1 = x.1 fun _ => block0 m (.fb t) r :=
  (h0 t z x h).2 _ _ fun hK => (block0_fb hm r hK).symm

theorem failCostsOne : Spec.failCostsOne := by
  intro I X lam L W nb m hm h0 t q r hf
  have hb : 0 < m.blocks (.fb t) := by rw [blocks_fb hm]; omega
  unfold failsAt at hf
  cases hx : tryInfoT W t q.plain with
  | none => rw [hx] at hf; exact nomatch hf
  | some x =>
    rw [hx] at hf
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hq := ruleT_some W nb m hx
    rw [hf.2] at hq
    exact numA_fail m hb hq r (by rw [← test_block0 hm h0 hx r]; exact hf.1)

theorem shownA_congr {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) {need need' : NeedA S lam} {o : S.ι}
    {q : S.Dom o} (h : need o q = need' o q) (r : S.Rng o) :
    shownA m need o q r = shownA m need' o q r := by
  unfold shownA
  rw [h]

/-- An answer and the answer as the rule shows it. -/
theorem shownT_rel (hm : Std m) (h0 : Test0 W) (o : OracleName) (q : domOf lam L o) (r : rngOf lam W.K o) :
    agree nb o q r (shownA m (ruleT W nb m) o q r) ∨
    agF W o q r (shownA m (ruleT W nb m) o q r) := by
  have tab : ruleT W nb m o q = NeedA.ofNeed (needOf nb m) o q →
      agree nb o q r (shownA m (ruleT W nb m) o q r) := fun e => by
    rw [shownA_congr m e r]
    exact agree_of_Agree nb hm o q _ _ ((ofNeedA _ lam m (needOf nb m)).2.1 o q r)
  by_cases ho : ∃ t, o = .fb t
  · obtain ⟨t, rfl⟩ := ho
    have hb : 0 < m.blocks (.fb t) := by rw [blocks_fb hm]; omega
    cases hx : tryInfoT W t (q : FbIn lam L t).plain with
    | none => exact .inl (tab (ruleT_none W nb m hx))
    | some x =>
      have hq := ruleT_some W nb m hx
      by_cases hp : (x.1 (fun _ => block0 m (.fb t) r) || x.2) = true
      · refine .inl (agree_of_Agree nb hm _ q _ _ fun j hj => ?_)
        unfold shownA
        rw [Equiv.apply_symm_apply, hq, maskFrom_ndTest' _ _ _ _ hb]
        have ej : extBl (m.rng (.fb t) r) j = m.rng (.fb t) r j := by
          unfold extBl
          rw [dif_pos j.isLt]
        by_cases hj0 : (j : ℕ) = 0
        · rw [if_pos hj0, ← ej, hj0]
        · have hst : NeedA.ofNeed (needOf nb m) (.fb t) q j (acc0 lam) = true := by
            unfold NeedA.ofNeed
            rw [dif_pos j.isLt]
            exact hj
          have hp' : (x.1 (fun _ => extBl (m.rng (.fb t) r) 0) || x.2) = true := hp
          rw [if_neg hj0, if_pos ⟨j.isLt, by rw [hp', hst]; rfl⟩, ej]
      · refine .inr ?_
        have hp2 : x.1 (fun _ => block0 m (.fb t) r) = false ∧ x.2 = false := by
          cases h1 : x.1 (fun _ => block0 m (.fb t) r) <;> cases h2 : x.2 <;> simp [h1, h2] at hp ⊢
        have f : ∀ r' : rngOf lam W.K (.fb t),
            block0 m (.fb t) r' = block0 m (.fb t) r → failsAt W t q r'.1 = true := fun r' e => by
          unfold failsAt
          rw [hx]
          show (!x.1 r'.1 && !x.2) = true
          rw [test_block0 hm h0 hx r', e, hp2.1, hp2.2]
          rfl
        exact ⟨f r rfl, f _ (block0_shownA m hb hq r)⟩
  · exact .inl (tab (ruleT_other W nb m (fun t e => ho ⟨t, e⟩) q))


end Compile.Batch
