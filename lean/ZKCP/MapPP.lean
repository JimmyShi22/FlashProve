-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/MapPP.lean: the public parameters of an indexed relation written in another form.

For every indexed relation R of ZKCP/Defs.lean with public parameters in PP and every function g :
PP → PP':
  `IndexedRelation.mapPP R g`  the same triples; the public parameters of i are g (pp(i))
  `Simulator.comapPP S g'`     for g' : PP' → PP: S, initialised with g' p in the place of p
  `IsZKCPArgWith.mapPP`, `IsZKCPArg.mapPP`: if g' (g (pp(i))) = pp(i) for every index i (the new
      form tells the old one), the three properties are carried over, for the same scheme, with
      the same bounds; in `IsZKCPArgWith.mapPP` with the same extractor and `S.comapPP g'`.
      Completeness and index binding do not read pp at all: they are carried over for every g.
Why. A construction can leave public parameters in a form with a part that carries no information (a
pair with the one element of Unit). This step writes them without it.

Limits: Nothing where the new form tells less than the old one: then the simulator would be handed
less, and privacy would be a stronger statement, which does not follow. (The other way: the new form
is a function of pp(i) alone, so it never tells more than the old one; g' is one function, fixed
outside the experiments, and is applied to g (pp(i)) only.)

After `IsZKCPArg` and its three properties in ZKCP/Defs.lean; the step itself is not in
ZKCP/Defs.lean.
Definitions are cited by their names in ZKCP/Defs.lean.
-/
import ZKCP.Defs

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP PP' IVK ISK Pf : Type}

/-- The relation: the same triples, the public parameters in another form. -/
def IndexedRelation.mapPP (R : IndexedRelation I X W PP) (g : PP → PP') :
    IndexedRelation I X W PP' :=
  ⟨R.rel, fun i => g (R.pp i)⟩

/-- The simulator: it applies g' to the new form. -/
def Simulator.comapPP (S : Simulator lam PP IVK X Pf) (g' : PP' → PP) :
    Simulator lam PP' IVK X Pf where
  St := S.St
  init p n := S.init (g' p) n
  answer := S.answer
  prove := S.prove

variable {R : IndexedRelation I X W PP}
  {A : Arg lam I X W IVK ISK Pf} (g : PP → PP') (g' : PP' → PP)

theorem HasCompletenessError.mapPP {α : ℝ≥0∞} (h : HasCompletenessError R A α) :
    HasCompletenessError (R.mapPP g) A α := h

theorem bindingBad_mapPP : bindingBad (R.mapPP g) = bindingBad R := by
  ext o
  obtain ⟨b, _ | i, x, w⟩ := o <;> rfl

theorem HasIndexBindingWith.mapPP
    {E : Extractor lam I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (h : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith (R.mapPP g) A E ε := by
  intro tC tP St Ct Pt hC hP
  rw [bindingBad_mapPP]
  exact h tC tP St Ct Pt hC hP

theorem HasIndexBinding.mapPP {ε : ℕ → ℕ → ℝ≥0∞} (h : HasIndexBinding R A ε) :
    HasIndexBinding (R.mapPP g) A ε :=
  h.elim fun E hE => ⟨E, hE.mapPP g⟩

theorem comapPP_idealLoop (S : Simulator lam PP IVK X Pf) (Z : ViewEnv lam IVK X W Pf) :
    ∀ (a : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop (S.comapPP g') Z a n v s = idealLoop S Z a n v s
  | .halt, _, _, _ => rfl
  | .query q k, n, v, s => by
      simp only [idealLoop]
      exact congrArg _ (funext fun out => comapPP_idealLoop S Z (k out.1) n _ out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop]
      exact congrArg _ (funext fun r => comapPP_idealLoop S Z (k r) n _ s)
  | .request _, 0, _, _ => rfl
  | .request k, n + 1, v, s => by
      simp only [idealLoop]
      cases Z v with
      | none => rfl
      | some xw =>
          show (S.prove s xw.1).bind (fun out =>
              idealLoop (S.comapPP g') Z (k xw.1 out.1) n
                { v with sessions := v.sessions ++ [(xw.1, out.1)] } out.2) =
            (S.prove s xw.1).bind fun out =>
              idealLoop S Z (k xw.1 out.1) n
                { v with sessions := v.sessions ++ [(xw.1, out.1)] } out.2
          exact congrArg _ (funext fun out => comapPP_idealLoop S Z (k xw.1 out.1) n _ out.2)

variable {g g'}

theorem mapPP_idealExp (hg : ∀ i, g' (g (R.pp i)) = R.pp i) (S : Simulator lam PP IVK X Pf)
    (Vt : IVK → AdvVerifier lam X Pf) (Z : ViewEnv lam IVK X W Pf) (i : I) (N : ℕ) :
    idealExp (R.mapPP g) (S.comapPP g') Vt Z i N = idealExp R S Vt Z i N := by
  show (S.init (g' (g (R.pp i))) N).bind
      (fun out => idealLoop (S.comapPP g') Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    (S.init (R.pp i) N).bind fun out => idealLoop S Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2
  rw [hg i]
  exact congrArg _ (funext fun out => comapPP_idealLoop g' S Z (Vt out.1) N _ out.2)

theorem PrivacyFor.mapPP (hg : ∀ i, g' (g (R.pp i)) = R.pp i) {S : Simulator lam PP IVK X Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} {i : I} {Z : ViewEnv lam IVK X W Pf} (h : PrivacyFor R A S ζ i Z) :
    PrivacyFor (R.mapPP g) A (S.comapPP g') ζ i Z := by
  intro tV Vt N hV
  simp only [mapPP_idealExp hg]
  exact h tV Vt N hV

theorem HasStrongIndexPrivacyWith.mapPP (hg : ∀ i, g' (g (R.pp i)) = R.pp i)
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasStrongIndexPrivacyWith R A S ζ) :
    HasStrongIndexPrivacyWith (R.mapPP g) A (S.comapPP g') ζ :=
  fun i Z hZ => (h i Z hZ).mapPP hg

theorem HasIndexPrivacyWith.mapPP (hg : ∀ i, g' (g (R.pp i)) = R.pp i)
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasIndexPrivacyWith R A S ζ) :
    HasIndexPrivacyWith (R.mapPP g) A (S.comapPP g') ζ :=
  fun i Z hZ => (h i Z hZ).mapPP hg

theorem HasIndexPrivacy.mapPP
    (hg : ∀ i, g' (g (R.pp i)) = R.pp i) {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasIndexPrivacy R A ζ) :
    HasIndexPrivacy (R.mapPP g) A ζ :=
  h.elim fun S hS => ⟨S.comapPP g', hS.mapPP hg⟩

/-- If g' (g (pp(i))) = pp(i) for every i, `IsZKCPArgWith` is carried over, with the same bounds. -/
theorem IsZKCPArgWith.mapPP (hg : ∀ i, g' (g (R.pp i)) = R.pp i)
    {E : Extractor lam I X W IVK Pf} {S : Simulator lam PP IVK X Pf} {α : ℝ≥0∞}
    {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArgWith R A E S α ε ζ) :
    IsZKCPArgWith (R.mapPP g) A E (S.comapPP g') α ε ζ :=
  ⟨h.completeness.mapPP g, h.indexBinding.mapPP g, h.indexPrivacy.mapPP hg⟩

/-- Under hg. IsZKCPArg (ZKCP/Defs.lean) is carried over, with the same bounds. -/
theorem IsZKCPArg.mapPP (hg : ∀ i, g' (g (R.pp i)) = R.pp i) {α : ℝ≥0∞}
    {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArg R A α ε ζ) : IsZKCPArg (R.mapPP g) A α ε ζ :=
  ⟨h.completeness.mapPP g, h.indexBinding.mapPP g, h.indexPrivacy.mapPP hg⟩

end ZKCP
