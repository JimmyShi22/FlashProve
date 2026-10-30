-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinOut3.lean: the four joining theorems with a conclusion that may speak of all three
checkers' values.

Why. The joining theorems (`join_verify`, OnBytes/Slice/PartO.lean; `join_id`, JoinId.lean;
`join_id_at`, JoinAtSet.lean) pass from the three
parts' languages to a property `Good` of the THIRD checker's value and the first raw string, by a
hypothesis `hpath` that holds for any three values. That is enough where the three languages speak
of the raw strings alone. Where each language also speaks of something that is read off its own
checker's value (a stored table's record), the path through them needs that these agree, and that is
known only of the three values of ONE run, in `hYes`. So `Good` must see all three.

The text. The first three theorems are their sources with `Good` taking the three values; every
other sign of the statements, and the proofs, are the sources'; the fourth is the third in the
shape of JoinRun.lean (`Pr_run_eq`), for any type of symbols.
The sources are the case in which `Good` does not look at the first two.

Main theorems: `join_verify3`, `join_id3`, `join_id_at3`, `join_id_run3`.

What is not claimed. All limits in the heads of PartO.lean, JoinId.lean, JoinAtSet.lean and
JoinRun.lean hold here too. IMPLICATIONS: the parts, the verifier and `Good` are variables;
nothing is joined.
-/
import OnBytes.Slice.JoinRun

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

section
variable {lam : ℕ} {Sg β δ : Type}

/-- `join_verify` (OnBytes/Slice/PartO.lean) with a `Good` that sees the values of ALL THREE
checkers, not of the third alone. Every other sign, and the proof, are that theorem's. -/
theorem join_verify3 (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ) (tC tP : ℕ)
    (hC : C.QueryBound tC) (hP : ∀ b, (P b).QueryBound tP)
    (rt : β × Trace (rom lam) → Option (Dig lam))
    (K E F : PartO lam ((β × Trace (rom lam)) × δ) Sg) (hK : K.OK) (hE : E.OK) (hF : F.OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : K.Stable bS)
    (hKE : SameRaw K E) (hEF : SameRaw E F) (Good : K.Out → E.Out → F.Out → Raw Sg → Prop)
    (hpath : ∀ (oK : K.Out) (oE : E.Out) (oF : F.Out) (Y₀ Y₁ : Raw Sg),
      K.Lang oK [Y₀] → E.Lang oE [Y₀, Y₁] → F.Lang oF [Y₁] → Good oK oE oF Y₀)
    (X : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam))) (bX : ℝ≥0∞)
    (hX : Rom.Pr (twoExp C P).withTrace X ≤ bX) (hXc : ∀ g w, w ∉ X g → NoClash w.2)
    (Yes : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam)))
    (Fine : ((β × Trace (rom lam)) × δ) × Trace (rom lam) → Prop)
    (hYes : ∀ g w, w ∈ Yes g → w ∉ X g → (∃ τ, w.2 = w.1.1.2 ++ τ) → ∃ oK oE oF cm cm',
      (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
      (F.chk w.1).det g = some oF ∧ rt w.1.1 = some cm ∧ K.roots oK = [cm] ∧
      E.roots oE = [cm, cm'] ∧ F.roots oF = [cm'] ∧
      (Good oK oE oF (K.raw w.1.1.2 cm) → Fine w)) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | w ∈ Yes g ∧ ¬ Fine w}) ≤
      K.bound (tC + tP) + (E.bound (tC + tP) + (F.bound (tC + tP) + (bS tC tP + bX))) := by
  have hM := queryBound_twoExp C P tC tP hC hP
  set c := (twoExp C P).withTrace with hc
  let E4 : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam)) := fun _ =>
    {w | ∃ cm, rt w.1.1 = some cm ∧ K.raw w.1.1.2 cm ≠ K.raw w.2 cm}
  have b4 : Rom.Pr c E4 ≤ bS tC tP := hS β δ C rt P tC tP hC hP
  rw [hc, Pr_twoExp_shape, ← hc]
  refine le_trans (Rom.Pr_mono c (F := fun g =>
    K.lose g ∪ (E.lose g ∪ (F.lose g ∪ (E4 g ∪ X g)))) fun g w hw => ?_) ?_
  · obtain ⟨⟨hy, hbad⟩, hsh⟩ := hw
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨nK, nE, nF, n4, n5⟩ := hno
    obtain ⟨oK, oE, oF, cm, cm', cK, cE, cF, hrt, rK, rE, rF, hfine⟩ := hYes g w hy n5 hsh
    have lK : K.Lang oK [K.raw w.2 cm] := by
      by_contra h
      exact nK ⟨oK, cK, by rw [rK]; exact h⟩
    have lE : E.Lang oE [E.raw w.2 cm, E.raw w.2 cm'] := by
      by_contra h
      exact nE ⟨oE, cE, by rw [rE]; exact h⟩
    have lF : F.Lang oF [F.raw w.2 cm'] := by
      by_contra h
      exact nF ⟨oF, cF, by rw [rF]; exact h⟩
    have hcl : NoClash w.2 := hXc g w n5
    have hst : K.raw w.1.1.2 cm = K.raw w.2 cm := by
      by_contra h
      exact n4 ⟨cm, hrt, h⟩
    rw [← hKE w.2 hcl cm, hEF w.2 hcl cm'] at lE
    refine hbad (hfine ?_)
    rw [hst]
    exact hpath oK oE oF _ _ lK lE lF
  · refine le_trans (Pr_union_le c _ _ (hK.meas _)) (add_le_add (hK.rare _ _ hM) ?_)
    refine le_trans (Pr_union_le c _ _ (hE.meas _)) (add_le_add (hE.rare _ _ hM) ?_)
    refine le_trans (Pr_union_le c _ _ (hF.meas _)) (add_le_add (hF.rare _ _ hM) ?_)
    exact le_trans (Pr_union_le c _ _ (measurable_PrCoins _ _)) (add_le_add b4 hX)

end

variable {Sg β δ : Type}

/-- `join_id` (OnBytes/Slice/JoinId.lean) with a `Good` that sees the values of all three
checkers. -/
theorem join_id3 (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256)
    (P : β → OComp (rom 256) δ) (key : δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : PartO 256 ((β × Trace (rom 256)) × δ) Sg) (hK : K.OK) (hE : E.OK) (hF : F.OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : K.Stable bS)
    (hKE : SameRaw K E) (hEF : SameRaw E F) (Good : K.Out → E.Out → F.Out → Raw Sg → Prop)
    (hpath : ∀ (oK : K.Out) (oE : E.Out) (oF : F.Out) (Y₀ Y₁ : Raw Sg),
      K.Lang oK [Y₀] → E.Lang oE [Y₀, Y₁] → F.Lang oF [Y₁] → Good oK oE oF Y₀)
    (X' : Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256))) (bX' : ℝ≥0∞)
    (hX' : Rom.Pr (twoExp C P).withTrace X' ≤ bX')
    (Yes : Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (Fine : ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hYes : ∀ g w, w ∈ Yes g → w ∉ X' g →
      (∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1) ∧ ∃ oK oE oF cm',
        (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
        (F.chk w.1).det g = some oF ∧
        K.roots oK = [Run.bytesToDig (key w.1.2).2.2.root] ∧
        E.roots oE = [Run.bytesToDig (key w.1.2).2.2.root, cm'] ∧ F.roots oF = [cm'] ∧
        (firstId (dig w.1.1.1) w.1.1.2 = some (key w.1.2) → NoClash w.2 →
          (∃ τ, w.2 = w.1.1.2 ++ τ) →
          Good oK oE oF (K.raw w.1.1.2 (Run.bytesToDig (key w.1.2).2.2.root)) → Fine w)) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | w ∈ Yes g ∧ ¬ Fine w}) ≤
      K.bound (tC + tP) + (E.bound (tC + tP) + (F.bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) := by
  refine join_verify3 C P tC tP hC hP (rootOfId dig) K E F hK hE hF bS hS hKE hEF Good hpath
    (fun g => {w | ¬ NoClash w.2 ∨ ∃ s, idCode (key w.1.2) = some s ∧ g () s = dig w.1.1.1 ∧
      firstId (dig w.1.1.1) w.1.1.2 ≠ some (key w.1.2)} ∪ X' g) _
    ((Pr_union_le _ _ _ (measurable_id_maker C dig P key)).trans
      (add_le_add (id_maker C dig P key tC tP hC hP) hX'))
    (fun g w hw => ?_) Yes Fine fun g w hy hw hsh => ?_
  · by_contra h
    exact hw (Or.inl (Or.inl h))
  · obtain ⟨⟨s, hs, hg⟩, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, hfine⟩ :=
      hYes g w hy fun h => hw (Or.inr h)
    have hfirst : firstId (dig w.1.1.1) w.1.1.2 = some (key w.1.2) := by
      by_contra h
      exact hw (Or.inl (Or.inr ⟨s, hs, hg, h⟩))
    refine ⟨oK, oE, oF, _, cm', cK, cE, cF, ?_, rK, rE, rF,
      hfine hfirst (by by_contra h; exact hw (Or.inl (Or.inl h))) hsh⟩
    show (firstId (dig w.1.1.1) w.1.1.2).map _ = _
    rw [hfirst]
    rfl

/-- `join_id_at` (OnBytes/Slice/JoinAtSet.lean) with a `Good` that sees the values of all three
checkers. -/
theorem join_id_at3 (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (key : Tab → Tab → δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) Sg)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (Good : ∀ T₀ T₁, (K T₀ T₁).Out → (E T₀ T₁).Out → (F T₀ T₁).Out → Raw Sg → Prop)
    (hpath : ∀ T₀ T₁ (oK : (K T₀ T₁).Out) (oE : (E T₀ T₁).Out) (oF : (F T₀ T₁).Out)
      (Y₀ Y₁ : Raw Sg), (K T₀ T₁).Lang oK [Y₀] → (E T₀ T₁).Lang oE [Y₀, Y₁] →
      (F T₀ T₁).Lang oF [Y₁] → Good T₀ T₁ oK oE oF Y₀)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (Yes : Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (Fine : Fam (rom 256) → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (FineT : Tab → Tab → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hFine : ∀ T₀ T₁ g w, FineT T₀ T₁ w → Fine (over S₀ T₀ (over (S₁ T₀) T₁ g)) w)
    (hm : ∀ w, MeasurableSet {g | w ∈ Yes g ∧ ¬ Fine g w})
    (hoff₀ : ∀ g w, w ∈ Yes g → ¬ Fine g w → offBoth S₀ w ∈ Yes g ∧ ¬ Fine g (offBoth S₀ w))
    (hoff₁ : ∀ T₀ g w, w ∈ Yes g → ¬ Fine g w →
      offBoth (S₁ T₀) w ∈ Yes g ∧ ¬ Fine g (offBoth (S₁ T₀) w))
    (hYes : ∀ T₀ T₁ g w, w ∈ Yes (over S₀ T₀ (over (S₁ T₀) T₁ g)) → w ∉ X' T₀ T₁ g →
      (∃ s, idCode (key T₀ T₁ w.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig w.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk w.1).det g = some oK ∧ ((E T₀ T₁).chk w.1).det g = some oE ∧
        ((F T₀ T₁).chk w.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root] ∧
        (E T₀ T₁).roots oE = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        (firstId (dig w.1.1.1) w.1.1.2 = some (key T₀ T₁ w.1.2) → NoClash w.2 →
          (∃ τ, w.2 = w.1.1.2 ++ τ) →
          Good T₀ T₁ oK oE oF
            ((K T₀ T₁).raw w.1.1.2 (Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root)) →
          FineT T₀ T₁ w))
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + tP) + ((E T₀ T₁).bound (tC + tP) +
      ((F T₀ T₁).bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | w ∈ Yes g ∧ ¬ Fine g w}) ≤ B := by
  refine Pr_twoExp_le_of_pinned₂ S₀ S₁ C P _ B hm (fun g w hw => hoff₀ g w hw.1 hw.2)
    (fun T₀ g w hw => hoff₁ T₀ g w hw.1 hw.2) fun T₀ T₁ => ?_
  have h := join_id3 (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C)) dig
    (fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))) (key T₀ T₁) tC tP
    (queryBound_pinOn _ _ _ tC (queryBound_pinOn _ _ C tC hC))
    (fun b => queryBound_pinOn _ _ _ tP (queryBound_pinOn _ _ (P b) tP (hP b)))
    (K T₀ T₁) (E T₀ T₁) (F T₀ T₁) (hK T₀ T₁) (hE T₀ T₁) (hF T₀ T₁) bS (hS T₀ T₁) (hKE T₀ T₁)
    (hEF T₀ T₁) (Good T₀ T₁) (hpath T₀ T₁) (X' T₀ T₁) bX' (hX' T₀ T₁)
    (fun g => Yes (over S₀ T₀ (over (S₁ T₀) T₁ g))) (FineT T₀ T₁) fun g w hy hx => by
      obtain ⟨⟨s, hs, hg⟩, rest⟩ := hYes T₀ T₁ g w hy hx
      refine ⟨⟨s, hs, ?_⟩, rest⟩
      rw [over_not_mem _ _ (hid _ s hs).1, over_not_mem _ _ ((hid _ s hs).2 T₀)] at hg
      exact hg
  refine le_trans (Rom.Pr_mono _ fun g w hw => ?_) (h.trans (hB T₀ T₁))
  exact ⟨hw.1, fun hf => hw.2 (hFine T₀ T₁ g w hf)⟩

/-- **The join for an experiment in which a verifier is run**, with a `Good` that sees the values of
all three checkers. -/
theorem join_id_run3 (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool))
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (key : Tab → Tab → δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) Sg)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (Good : ∀ T₀ T₁, (K T₀ T₁).Out → (E T₀ T₁).Out → (F T₀ T₁).Out → Raw Sg → Prop)
    (hpath : ∀ T₀ T₁ (oK : (K T₀ T₁).Out) (oE : (E T₀ T₁).Out) (oF : (F T₀ T₁).Out)
      (Y₀ Y₁ : Raw Sg), (K T₀ T₁).Lang oK [Y₀] → (E T₀ T₁).Lang oE [Y₀, Y₁] →
      (F T₀ T₁).Lang oF [Y₁] → Good T₀ T₁ oK oE oF Y₀)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (V : β × δ → OComp (rom 256) Bool) (hV : ∀ x, (V x).NoCoin)
    (Fine : ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (FineT : Tab → Tab → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hFine : ∀ T₀ T₁ w, FineT T₀ T₁ w → Fine w)
    (hoff₀ : ∀ w, ¬ Fine w → ¬ Fine (offBoth S₀ w))
    (hoff₁ : ∀ T₀ w, ¬ Fine w → ¬ Fine (offBoth (S₁ T₀) w))
    (hYes : ∀ T₀ T₁ g w,
      (V (w.1.1.1, w.1.2)).det (over S₀ T₀ (over (S₁ T₀) T₁ g)) = true → w ∉ X' T₀ T₁ g →
      (∃ s, idCode (key T₀ T₁ w.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig w.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk w.1).det g = some oK ∧ ((E T₀ T₁).chk w.1).det g = some oE ∧
        ((F T₀ T₁).chk w.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root] ∧
        (E T₀ T₁).roots oE = [Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        (firstId (dig w.1.1.1) w.1.1.2 = some (key T₀ T₁ w.1.2) → NoClash w.2 →
          (∃ τ, w.2 = w.1.1.2 ++ τ) →
          Good T₀ T₁ oK oE oF
            ((K T₀ T₁).raw w.1.1.2 (Run.bytesToDig (key T₀ T₁ w.1.2).2.2.root)) →
          FineT T₀ T₁ w))
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + tP) + ((E T₀ T₁).bound (tC + tP) +
      ((F T₀ T₁).bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
      (fun _ => {z | z.2 = true ∧ ¬ Fine z.1}) ≤ B := by
  rw [Pr_run_eq C P V hV Fine]
  exact join_id_at3 S₀ S₁ C dig P key tC tP hC hP K E F hK hE hF bS hS hKE hEF Good hpath
    X' bX' hX' hid (fun g => {w | (V (w.1.1.1, w.1.2)).det g = true}) (fun _ => Fine) FineT
    (fun T₀ T₁ _ w h => hFine T₀ T₁ w h)
    (fun w => (measurableSet_det (V (w.1.1.1, w.1.2)) {true}).inter (MeasurableSet.const _))
    (fun _ w hy hf => ⟨hy, hoff₀ w hf⟩) (fun T₀ _ w hy hf => ⟨hy, hoff₁ T₀ w hf⟩) hYes B hB

end OnBytes.Slice
