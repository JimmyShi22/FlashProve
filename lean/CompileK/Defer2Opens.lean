-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Opens.lean: the openings of the hash trees over prover messages, for the lemma on
deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). The openings in
the token trees of an execution (Compile/Batch/Prover.lean: `opensComp`, `opensOpt`, `opensB`) obey
the discipline with joint charges (CompileK/Defer2Safe.lean: `SafeO2`), from a state that is orderly
both ways (`TidyBoth`) in which the trees stand both ways (CompileK/Defer2Kit.lean: `TTOK2`, `AlJ2`,
`Al02`); each under the hypotheses of its statement (for `opensComp`: of leaves below 2 ^ depth).

The analogues for `SafeO2` of the theorems of Compile/Batch/DisciplineOpens.lean
(`safe2_opensTrees`: for a component with a list of trees: `opensTrees`; `safe2_opensB` does not use
it). Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Why: many paths, in many trees, one after the other: each opening's set is closed both ways in
itself, and a reveal makes no evaluation, so the trees go on standing both ways.

Words used in this file. The discipline with joint charges, orderly both ways, both ways: the
paragraph "Words used in this file." of CompileK/Defer2Chain.lean's head holds here too.
-/
import CompileK.Defer2Kit
import Compile.Batch.DisciplineOpens

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ}

/-- The openings in one tree. -/
theorem safe2_opensComp (n₀ depth : ℕ) {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → Option r.Pos) (o : r.Orc) (tr : TTree) (isRead : r.Pos → Bool)
    (f : (q : r.Pos) → Option (Opening lam (r.Sym q))) :
    ∀ (js : List ℕ), (∀ j ∈ js, j < 2 ^ depth) →
      ∀ (d : DSt (spec lam K L)), TidyBoth p mG d → TTOK2 d n₀ depth tr →
        SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
          (opensComp (K := K) (L := L) dec posAt o tr isRead f js) d fun _ d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d'
  | [], _, d, hd, _ => ⟨hd, Run.refl d⟩
  | j :: js, hjs, d, hd, ht => by
      rw [opensComp]
      refine SafeO2.bind _ _ d
        (SafeO2.mono ?_ _ d
          (safe2_opensComp n₀ depth dec posAt o tr isRead f js
            (fun i hi => hjs i (List.mem_cons_of_mem _ hi)) d hd ht))
      rintro f' d₁ ⟨hd₁, hr₁⟩
      have ht₁ : TTOK2 d₁ n₀ depth tr :=
        ht.keeps hr₁.charges (fun _ h => h.elim) (GJ.of_grows hr₁.grows) (fun _ h => h.elim)
      have hj := hjs j List.mem_cons_self
      split
      · split
        · refine SafeO2.bind _ _ d₁
            (SafeO2.mono ?_ _ d₁
              (safe2_openT tr j _ d₁ hd₁ (ht₁.1.open_ j hj) (UpClosed.of_rdeps (ht₁.2 j hj))))
          rintro op d₂ ⟨hd₂, hr₂⟩
          exact ⟨hd₂,
            hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h)
              (fun u hu => Or.inl (ht₁.1.new j hj u hu)) (fun _ => le_rfl) (fun _ => le_rfl)⟩
        · exact ⟨hd₁, hr₁⟩
      · exact ⟨hd₁, hr₁⟩

/-- The same for a component that may not have been sent. -/
theorem safe2_opensOpt (n₀ : ℕ) {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos)
    (depth : ℕ) (o : r.Orc) (tr : Option TTree)
    (isRead : r.Pos → Bool) (f : (q : r.Pos) → Option (Opening lam (r.Sym q)))
    (d : DSt (spec lam K L)) (hd : TidyBoth p mG d)
    (ht : ∀ t, tr = some t → TTOK2 d n₀ depth t) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) d fun _ d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d' := by
  cases tr with
  | none => exact ⟨hd, Run.refl d⟩
  | some t =>
    exact safe2_opensComp n₀ depth dec posAt o t isRead f _
      (fun j hj => List.mem_range.mp hj) d hd (ht t rfl)

/-- The openings in the trees of one component, each tree at the depth that it meets. -/
theorem safe2_opensTrees (n₀ : ℕ) {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (q : r.Pos) → Option (Opening lam (r.Sym q))) (d : DSt (spec lam K L)),
      TidyBoth p mG d → (∀ x ∈ ds.zip trs, TTOK2 d n₀ x.1 x.2) →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) d
        fun _ d' => TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d'
  | _, [], _, _, d, hd, _ => ⟨hd, Run.refl d⟩
  | _, _ :: _, [], _, d, hd, _ => ⟨hd, Run.refl d⟩
  | k, dp :: ds, tr :: trs, f, d, hd, ht => by
      rw [List.zip_cons_cons] at ht
      obtain ⟨ht0, hts⟩ := List.forall_mem_cons.1 ht
      rw [opensTrees]
      refine SafeO2.bind _ _ d
        (SafeO2.mono ?_ _ d (safe2_opensTrees n₀ dec posAt o isRead (k + 1) ds trs f d hd hts))
      rintro f' d₁ ⟨hd₁, hr₁⟩
      have ht₁ : TTOK2 d₁ n₀ dp tr :=
        ht0.keeps hr₁.charges (fun _ h => h.elim) (GJ.of_grows hr₁.grows) (fun _ h => h.elim)
      refine SafeO2.mono ?_ _ d₁
        (safe2_opensComp n₀ dp dec (posAt k) o tr isRead f' _ (fun j hj => List.mem_range.mp hj)
          d₁ hd₁ ht₁)
      rintro _ d₂ ⟨hd₂, hr₂⟩
      exact ⟨hd₂,
        hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- The same where every depth has its tree, in order. -/
theorem safe2_opensTrees_of_forall₂ (n₀ : ℕ) {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) (k : ℕ) (ds : List ℕ)
    (trs : List TTree) (f : (q : r.Pos) → Option (Opening lam (r.Sym q)))
    (d : DSt (spec lam K L)) (hd : TidyBoth p mG d) (ht : List.Forall₂ (TTOK2 d n₀) ds trs) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
      (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) d
      fun _ d' => TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d' :=
  safe2_opensTrees n₀ dec posAt o isRead k ds trs f d hd fun _ hx => List.forall₂_zip ht hx

/-- The openings in the token trees of all rounds. -/
theorem safe2_opensB (n₀ : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
    (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool)
    (d : DSt (spec lam K L)), TidyBoth p mG d → AlJ2 d n₀ s A W tjs → Al02 d n₀ s A W t0s →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (opensB s A W τ tjs t0s isRead) d fun _ d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d'
  | [], _, _, _, _, _, _, d, hd, _, _ => ⟨hd, Run.refl d⟩
  | _ :: s, (_, A), (w, W), (m, _, τ), tjs, t0s, isRead, d, hd, hJ, h0 => by
      rw [opensB]
      refine SafeO2.bind _ _ d
        (SafeO2.mono ?_ _ d
          (safe2_opensOpt n₀ w.pt.decPos w.posAt0 w.depth0 m.1 (t0s.headD none)
            (fun q => isRead (.inl q)) (fun _ => none) d hd h0.1))
      rintro f0 d₁ ⟨hd₁, hr₁⟩
      have hJ₁ := AlJ2.keeps hr₁.charges (n₀ := n₀) (fun _ h => h.elim) (GJ.of_grows hr₁.grows)
        (fun _ h => h.elim) _ _ _ _ hJ
      have h0₁ := Al02.keeps hr₁.charges (n₀ := n₀) (fun _ h => h.elim) (GJ.of_grows hr₁.grows)
        (fun _ h => h.elim) _ _ _ _ h0
      refine SafeO2.bind _ _ d₁
        (SafeO2.mono ?_ _ d₁
          (safe2_opensOpt n₀ w.pt.decPos w.posAtJ w.depthJ m.1 (tjs.headD none)
            (fun q => isRead (.inl q)) f0 d₁ hd₁ hJ₁.1))
      rintro f d₂ ⟨hd₂, hr₂⟩
      have hJ₂ := AlJ2.keeps hr₂.charges (n₀ := n₀) (fun _ h => h.elim) (GJ.of_grows hr₂.grows)
        (fun _ h => h.elim) _ _ _ _ hJ₁
      have h0₂ := Al02.keeps hr₂.charges (n₀ := n₀) (fun _ h => h.elim) (GJ.of_grows hr₂.grows)
        (fun _ h => h.elim) _ _ _ _ h0₁
      refine SafeO2.bind _ _ d₂
        (SafeO2.mono ?_ _ d₂
          (safe2_opensB n₀ s A W τ tjs.tail t0s.tail (fun q => isRead (.inr q)) d₂ hd₂ hJ₂.2 h0₂.2))
      rintro g d₃ ⟨hd₃, hr₃⟩
      exact ⟨hd₃,
        (hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
            (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₃ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl)⟩


end Compile.Batch.Disc
