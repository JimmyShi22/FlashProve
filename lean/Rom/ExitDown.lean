-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/ExitDown.lean: the step to one hash function (Rom/Family.lean), part 1: an algorithm over the
hash function is an algorithm over the family.

The field `code` of a query encoding m (`OracleCoding`) is a bijection between the points (o, q, j) of the
family (oracle, query, index of the hash block) and all strings. So a function on strings and a
family are the same thing (`glue`, `readBlocks`), and a query to f at the string code o q j can be
answered by querying the oracle o at q and keeping hash block j (`down`). One query becomes one
query, so query bounds are kept.

  `runEager_down`  (down m c) with the family F fixed = c with the hash function glue m F fixed
  `withTrace_down` the same with traces
-/
import Rom.Prefix
noncomputable section -- Lean tags what it cannot compile

open MeasureTheory
open scoped ENNReal

namespace Rom

variable {S : OSpec} {lam : ℕ} {α β : Type}

/-- A point of the family: oracle, query, index of the hash block. -/
abbrev OracleCoding.Pt (m : OracleCoding S lam) : Type := Σ o, S.Dom o × Fin (m.blocks o)

/-- The encoding as an equivalence between points and strings. -/
def OracleCoding.equiv (m : OracleCoding S lam) : m.Pt ≃ List Bool :=
  ⟨fun x => m.code x.1 x.2.1 x.2.2, m.inv, m.inv_code, m.code_inv⟩

/-- The point that a string encodes. -/
def OracleCoding.dec (m : OracleCoding S lam) (s : List Bool) : m.Pt := m.equiv.symm s

lemma OracleCoding.dec_code (m : OracleCoding S lam) (o : S.ι) (q : S.Dom o) (j : Fin (m.blocks o)) :
    m.dec (m.code o q j) = ⟨o, q, j⟩ :=
  m.equiv.symm_apply_apply ⟨o, q, j⟩

lemma OracleCoding.code_dec (m : OracleCoding S lam) (s : List Bool) :
    m.code (m.dec s).1 (m.dec s).2.1 (m.dec s).2.2 = s :=
  m.equiv.apply_symm_apply s

/-- Hash block j of an answer of the oracle o. -/
def OracleCoding.blk (m : OracleCoding S lam) {o : S.ι} (r : S.Rng o) (j : Fin (m.blocks o)) : Fin lam → Bool :=
  m.rng o r j

/-- The hash function that contains all of the family F. -/
def glue (m : OracleCoding S lam) (F : Fam S) : Fam (rom lam) :=
  fun _ s => m.blk (F (m.dec s).1 (m.dec s).2.1) (m.dec s).2.2

lemma readBlocks_glue (m : OracleCoding S lam) (F : Fam S) : readBlocks m (glue m F) = F := by
  funext o q
  have : (fun j => rngOf () (glue m F () (m.code o q j))) = m.rng o (F o q) := by
    funext j
    show m.blk (F (m.dec (m.code o q j)).1 (m.dec (m.code o q j)).2.1) (m.dec (m.code o q j)).2.2 =
      _
    rw [m.dec_code]
    rfl
  show (m.rng o).symm _ = _
  rw [this, Equiv.symm_apply_apply]

lemma glue_readBlocks (m : OracleCoding S lam) (g : Fam (rom lam)) : glue m (readBlocks m g) = g := by
  funext u s
  cases u
  show m.rng _ ((m.rng _).symm fun j => rngOf () (g () (m.code (m.dec s).1 (m.dec s).2.1 j)))
      (m.dec s).2.2 = _
  rw [Equiv.apply_symm_apply, m.code_dec]
  rfl

/-- Under hφ: integrals over the hash function are integrals over the family. -/
theorem lintegral_glue (m : OracleCoding S lam) (φ : Fam (rom lam) → ℝ≥0∞)
    (hφ : Measurable fun F : Fam S => φ (glue m F)) :
    ∫⁻ g, φ g ∂(U (rom lam)) = ∫⁻ F, φ (glue m F) ∂(U S) := by
  rw [← U_map_readBlocks m, lintegral_map hφ (measurable_readBlocks m)]
  simp only [glue_readBlocks]

/-- The same algorithm over the family: a query at a string becomes one query at its point, of which
the hash block is kept. -/
def down (m : OracleCoding S lam) : OComp (rom lam) α → OComp S α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => down m (k r)
  | .query _ s k => .query (m.dec s).1 (m.dec s).2.1 fun r => down m (k (m.blk r (m.dec s).2.2))

theorem runEager_down (m : OracleCoding S lam) (F : Fam S) (c : OComp (rom lam) α) :
    (down m c).runEager F = c.runEager (glue m F) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [down, OComp.runEager, ih]
  | query u s k ih => cases u; simp only [down, OComp.runEager, ih]; rfl

theorem down_bind (m : OracleCoding S lam) (c : OComp (rom lam) α) (g : α → OComp (rom lam) β) :
    down m (c.bind g) = (down m c).bind fun a => down m (g a) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [down, OComp.bind, ih]
  | query u s k ih => simp only [down, OComp.bind, ih]

theorem queryBound_down (m : OracleCoding S lam) (c : OComp (rom lam) α) :
    ∀ t, c.QueryBound t → (down m c).QueryBound t := by
  induction c with
  | pure a => intro t _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query u s k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih _ t (h _)

/-- The probability of an event about the output is the same over the hash function and over the
family. -/
theorem Pr_down (m : OracleCoding S lam) (c : OComp (rom lam) α) (E : Set α) :
    Pr c (fun _ => E) = Pr (down m c) (fun _ => E) := by
  unfold Pr
  rw [lintegral_glue m (fun g => PrCoins g c E)]
  · simp only [PrCoins, runEager_down]
  · simp only [PrCoins, ← runEager_down]
    exact measurable_PrCoins (down m c) E

/-! ### Traces -/

/-- The trace over the family F that corresponds to a trace over the hash function: each entry
becomes the whole answer of F at its point. -/
def upTr (m : OracleCoding S lam) (F : Fam S) (tr : Trace (rom lam)) : Trace S :=
  tr.map fun e => ⟨(m.dec e.2.1).1, (m.dec e.2.1).2.1, F (m.dec e.2.1).1 (m.dec e.2.1).2.1⟩

theorem withTrace_down (m : OracleCoding S lam) (F : Fam S) (c : OComp (rom lam) α) :
    (down m c).withTrace.runEager F =
      (c.withTrace.runEager (glue m F)).map fun out => (out.1, upTr m F out.2) := by
  induction c with
  | pure a => simp only [down, OComp.withTrace, OComp.runEager, PMF.pure_map, upTr, List.map_nil]
  | sample n k ih => simp only [down, OComp.withTrace, OComp.runEager, ih, PMF.map_bind]
  | query u s k ih =>
    cases u
    simp only [down, OComp.withTrace, OComp.runEager, OComp.runEager_bind, ih, PMF.map_bind,
      PMF.bind_map, PMF.pure_map]
    rfl

/-- The answers of a trace, replaced by the true answers of g. -/
def retr (g : Fam S) (tr : Trace S) : Trace S := tr.map fun e => ⟨e.1, e.2.1, g e.1 e.2.1⟩

/-- A trace holds the true answers. -/
theorem withTrace_retr (g : Fam S) (c : OComp S α) :
    c.withTrace.runEager g = (c.withTrace.runEager g).map fun out => (out.1, retr g out.2) := by
  induction c with
  | pure a => simp only [OComp.withTrace, OComp.runEager, PMF.pure_map, retr, List.map_nil]
  | sample n k ih =>
    simp only [OComp.withTrace, OComp.runEager, PMF.map_bind]
    congr 1; funext r; exact ih r
  | query o q k ih =>
    simp only [OComp.withTrace, OComp.runEager, OComp.runEager_bind, PMF.map_bind, PMF.pure_map]
    conv_lhs => rw [ih]
    rw [PMF.bind_map]
    rfl

/-- What the extractor `extractorOverOneHashFunction` (Rom/ExitBind.lean) reads of a trace over the hash function: the
entries at oracles whose answer is one hash block, as entries over the family. -/
def singleTr (m : OracleCoding S lam) (tr : Trace (rom lam)) : Trace S :=
  tr.filterMap fun e =>
    if m.blocks (m.dec e.2.1).1 = 1 then
      some ⟨(m.dec e.2.1).1, (m.dec e.2.1).2.1, (m.rng (m.dec e.2.1).1).symm fun _ => e.2.2⟩
    else none

/-- On a trace with the true answers, the one-block entries over the family are those read off the
trace over the hash function. -/
theorem single_upTr (m : OracleCoding S lam) (F : Fam S) (tr : Trace (rom lam)) :
    single m (upTr m F tr) = singleTr m (retr (glue m F) tr) := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    obtain ⟨u, s, r⟩ := e
    cases u
    simp only [single, upTr, singleTr, retr, List.map_cons,
      List.filter_cons, List.filterMap_cons] at ih ⊢
    by_cases hb : m.blocks (m.dec s).1 = 1
    · simp only [hb, decide_true, if_true, ih]
      congr 3
      have hsub : Subsingleton (Fin (m.blocks (m.dec s).1)) := by rw [hb]; infer_instance
      have : (fun _ : Fin (m.blocks (m.dec s).1) => glue m F () s) =
          m.rng _ (F (m.dec s).1 (m.dec s).2.1) := by
        funext j
        show m.rng _ _ (m.dec s).2.2 = _
        rw [Subsingleton.elim j (m.dec s).2.2]
      rw [this, Equiv.symm_apply_apply]
    · simp only [hb, decide_false, if_false, ih]
      rfl

lemma upTr_retr (m : OracleCoding S lam) (F : Fam S) (g : Fam (rom lam)) (tr : Trace (rom lam)) :
    upTr m F (retr g tr) = upTr m F tr := by
  simp [upTr, retr]

end Rom
