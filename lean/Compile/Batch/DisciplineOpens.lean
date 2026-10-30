-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineOpens.lean: the openings in the token trees of an execution obey the rules
of deferred programming, from a state with `TidyO` and `TTOK` of the trees (words of this library:
lean/GLOSSARY.md).

For `Spec.safeProveB`: `opensComp`, `opensOpt`, `opensB` of Compile/Batch/Prover.lean. An opening
makes no query. It reveals the salt of a leaf with the digests beside and on its path together,
which is allowed while the tree is in order (`TTOK`, Compile/Batch/DisciplineTree.lean); a reveal
charges nothing, so the trees stay in order. Only tokens from n₀ on are shown. `safe_opensTrees`:
the same for a component with a list of trees (`opensTrees`, Compile/Batch/Prover.lean);
`safe_opensB` does not use it.

Notation:
  `SafeO Rl c d Q` (Compile/Batch/SpecDiscipline.lean): the program c obeys the rules from the
    state d, and ends in Q, whatever the coins, the answers and the tables are; Q takes c's value
    and the last state d';
  `Run Cc Ch R e M d d'` (Compile/Batch/DisciplineRun.lean): what a run does: Cc bounds the old
    tokens that it charges, Ch those that its queries hold; e and M count (R: see its doc comment);
  `zr`, `NoTok` (Compile/Batch/DisciplineE.lean): no query; no token;
  `AlJ`, `Al0` (Compile/Batch/DisciplineTree.lean): the trees over the slots' components are in
    order, round by round, with the depths of the wire record; the same for the trees over the
    shared components;
  J, 0 (in `tjs`/`t0s`, `depthJ`/`depth0`, `posAtJ`/`posAt0`): of a slot's component m_j; of the
    shared component m_0 (`WireRB`, Iop/BatchWire.lean);
  `posAt`, `f` (`bodyAt`, `opensComp`, Compile/Batch/Prover.lean): posAt says which position is at
    a leaf; f holds the openings made so far.
-/
import Compile.Batch.DisciplineTree

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params}

/-- Under the hypotheses below: the openings in one tree (`opensComp`) obey the rules and keep
`TidyO`; they make no query and charge no token (`Run NoTok NoTok (fun u => n₀ ≤ u) zr zr`). -/
theorem safe_opensComp (n₀ depth : ℕ) {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → Option r.Pos) (o : r.Orc) (tr : TTree) (isRead : r.Pos → Bool)
    (f : (q : r.Pos) → Option (Opening lam (r.Sym q))) :
    ∀ (js : List ℕ), (∀ j ∈ js, j < 2 ^ depth) →
      ∀ (d : DSt (spec lam K L)), TidyO (rulesB K L lam p) d → TTOK d n₀ depth tr →
        SafeO (rulesB K L lam p)
          (opensComp (K := K) (L := L) dec posAt o tr isRead f js) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d'
  | [], _, d, hd, _ => ⟨hd, Run.refl d⟩
  | j :: js, hjs, d, hd, ht => by
      rw [opensComp]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_opensComp n₀ depth dec posAt o tr isRead f js
        (fun i hi => hjs i (List.mem_cons_of_mem _ hi)) d hd ht))
      rintro f' d₁ ⟨hd₁, hr₁⟩
      have ht₁ : TTOK d₁ n₀ depth tr := ht.keeps hr₁.charges fun _ h => h.elim
      have hj := hjs j List.mem_cons_self
      split
      · split
        · refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_openT tr j _ d₁ hd₁ (ht₁.open_ j hj)))
          rintro op d₂ ⟨hd₂, hr₂⟩
          exact ⟨hd₂,
            hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h)
              (fun u hu => Or.inl (ht₁.new j hj u hu)) (fun _ => le_rfl) (fun _ => le_rfl)⟩
        · exact ⟨hd₁, hr₁⟩
      · exact ⟨hd₁, hr₁⟩

/-- The same as `safe_opensComp` for a component that may not have been sent. -/
theorem safe_opensOpt (n₀ : ℕ) {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos)
    (depth : ℕ) (o : r.Orc) (tr : Option TTree)
    (isRead : r.Pos → Bool) (f : (q : r.Pos) → Option (Opening lam (r.Sym q)))
    (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d)
    (ht : ∀ t, tr = some t → TTOK d n₀ depth t) :
    SafeO (rulesB K L lam p) (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d' := by
  cases tr with
  | none => exact ⟨hd, Run.refl d⟩
  | some t =>
    exact safe_opensComp n₀ depth dec posAt o t isRead f _
      (fun j hj => List.mem_range.mp hj) d hd (ht t rfl)

/-- Under `TidyO`, and `TTOK` of each tree at the depth that it meets: the openings in the trees of
one component (`opensTrees`): the conclusion of `safe_opensComp`. -/
theorem safe_opensTrees (n₀ : ℕ) {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (q : r.Pos) → Option (Opening lam (r.Sym q))) (d : DSt (spec lam K L)),
      TidyO (rulesB K L lam p) d → (∀ x ∈ ds.zip trs, TTOK d n₀ x.1 x.2) →
      SafeO (rulesB K L lam p) (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) d
        fun _ d' => TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d'
  | _, [], _, _, d, hd, _ => ⟨hd, Run.refl d⟩
  | _, _ :: _, [], _, d, hd, _ => ⟨hd, Run.refl d⟩
  | k, dp :: ds, tr :: trs, f, d, hd, ht => by
      rw [List.zip_cons_cons] at ht
      obtain ⟨ht0, hts⟩ := List.forall_mem_cons.1 ht
      rw [opensTrees]
      refine SafeO.bind _ _ d
        (SafeO.mono ?_ _ d (safe_opensTrees n₀ dec posAt o isRead (k + 1) ds trs f d hd hts))
      rintro f' d₁ ⟨hd₁, hr₁⟩
      have ht₁ : TTOK d₁ n₀ dp tr := ht0.keeps hr₁.charges fun _ h => h.elim
      refine SafeO.mono ?_ _ d₁
        (safe_opensComp n₀ dp dec (posAt k) o tr isRead f' _ (fun j hj => List.mem_range.mp hj)
          d₁ hd₁ ht₁)
      rintro _ d₂ ⟨hd₂, hr₂⟩
      exact ⟨hd₂,
        hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- The same as `safe_opensTrees` where every depth has its tree, in order. -/
theorem safe_opensTrees_of_forall₂ (n₀ : ℕ) {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) (k : ℕ) (ds : List ℕ)
    (trs : List TTree) (f : (q : r.Pos) → Option (Opening lam (r.Sym q)))
    (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d)
    (ht : List.Forall₂ (TTOK d n₀) ds trs) :
    SafeO (rulesB K L lam p) (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) d
      fun _ d' => TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d' :=
  safe_opensTrees n₀ dec posAt o isRead k ds trs f d hd fun _ hx => List.forall₂_zip ht hx

/-- Under `TidyO`, `AlJ`, `Al0`: the openings in the token trees of all rounds (`opensB`): the
conclusion of `safe_opensComp`. -/
theorem safe_opensB (n₀ : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
    (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool)
    (d : DSt (spec lam K L)), TidyO (rulesB K L lam p) d → AlJ d n₀ s A W tjs → Al0 d n₀ s A W t0s →
    SafeO (rulesB K L lam p) (opensB s A W τ tjs t0s isRead) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u) zr zr d d'
  | [], _, _, _, _, _, _, d, hd, _, _ => ⟨hd, Run.refl d⟩
  | _ :: s, (_, A), (w, W), (m, _, τ), tjs, t0s, isRead, d, hd, hJ, h0 => by
      rw [opensB]
      refine SafeO.bind _ _ d
        (SafeO.mono ?_ _ d
          (safe_opensOpt n₀ w.pt.decPos w.posAt0 w.depth0 m.1 (t0s.headD none)
            (fun q => isRead (.inl q)) (fun _ => none) d hd h0.1))
      rintro f0 d₁ ⟨hd₁, hr₁⟩
      have hJ₁ := AlJ.keeps hr₁.charges (n₀ := n₀) (fun _ h => h.elim) _ _ _ _ hJ
      have h0₁ := Al0.keeps hr₁.charges (n₀ := n₀) (fun _ h => h.elim) _ _ _ _ h0
      refine SafeO.bind _ _ d₁
        (SafeO.mono ?_ _ d₁
          (safe_opensOpt n₀ w.pt.decPos w.posAtJ w.depthJ m.1 (tjs.headD none)
            (fun q => isRead (.inl q)) f0 d₁ hd₁ hJ₁.1))
      rintro f d₂ ⟨hd₂, hr₂⟩
      have hJ₂ := AlJ.keeps hr₂.charges (n₀ := n₀) (fun _ h => h.elim) _ _ _ _ hJ₁
      have h0₂ := Al0.keeps hr₂.charges (n₀ := n₀) (fun _ h => h.elim) _ _ _ _ h0₁
      refine SafeO.bind _ _ d₂
        (SafeO.mono ?_ _ d₂
          (safe_opensB n₀ s A W τ tjs.tail t0s.tail (fun q => isRead (.inr q)) d₂ hd₂ hJ₂.2 h0₂.2))
      rintro g d₃ ⟨hd₃, hr₃⟩
      exact ⟨hd₃,
        (hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
            (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₃ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl)⟩

end Compile.Batch.Disc
