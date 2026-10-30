-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Special.lean: ZKCP/Gen.lean at one oracle and batches of one, compared with ZKCP/Defs.lean.

With R_yes = R_no, for the schemes `toGen A`: two equivalences and one implication. For a relation R
and a scheme A of Defs.lean, `toPair R` and `toGen A` (ZKCP/SpecialDefs.lean) are the same objects
in the form of Gen.lean. Proved:
  completeness_iff        Gen's completeness at B = 1          ↔  `HasCompletenessError`
  bindingWith_iff         Gen's binding, extractor extTo E ↔ `HasIndexBinding`,
                          extractor E
  binding_iff             the same with the extractor under ∃
  strongPrivacy_of_gen    Gen's privacy at B = 1, simulator S → the strong form of ZKCP/Defs.lean,
                          `HasIndexPrivacy`, same simulator (`simOf S`) and ζ
  isZKCPArgWith_of_gen    all three together, extractor and simulator named
  isZKCPArg_of_gen        all three together: Gen.IsZKCPArg at B = 1 → IsZKCPArg of ZKCP/Defs.lean
For privacy only the implication is claimed. At B = 1 Gen still asks more than Defs.lean: the
environment may name an empty batch, or one slot that is not the adversary's. The equivalence for
`HasRefinedCompletenessError` is not written. All of this is for schemes of the form
toGen A only.

Notation: ZKCP: see `IsZKCPArg`, ZKCP/Defs.lean; from there too:
`HasCompletenessError`, `HasRefinedCompletenessError`, `HasIndexBinding`,
`HasIndexPrivacy`; `extTo E`: a `Gen.Extractor`: E, an extractor of ZKCP/Defs.lean, translated into
the form of Gen.lean; `simOf S`: a `Simulator` of ZKCP/Defs.lean: S, a `Gen.Simulator`, translated
back (both: ZKCP/SpecialDefs.lean, its head).
-/
import ZKCP.SpecialDefs
import ZKCP.Basic
import Rom.EagerLazy

open scoped ENNReal

namespace ZKCP.Special

open Rom (rom toRom ofRom trTo trOf famOf)

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-! ### Monad laws for Rom.OComp -/

section Laws
variable {S : Rom.OSpec} {α β γ : Type}

@[simp] theorem rbind_eq (c : Rom.OComp S α) (g : α → Rom.OComp S β) : c >>= g = c.bind g := rfl
@[simp] theorem rpure_eq (a : α) : (Pure.pure a : Rom.OComp S α) = Rom.OComp.pure a := rfl

theorem bind_assoc (c : Rom.OComp S α) (g : α → Rom.OComp S β) (h : β → Rom.OComp S γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [Rom.OComp.bind, ih]
  | sample n k ih => simp only [Rom.OComp.bind, ih]

theorem bind_pure (c : Rom.OComp S α) : c.bind Rom.OComp.pure = c := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [Rom.OComp.bind, ih]
  | sample n k ih => simp only [Rom.OComp.bind, ih]

end Laws

variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-! ### Completeness -/

/-- P on a batch of one, followed by anything that reads the list of proofs. -/
theorem proveAll_single {β : Type} (isk : ISK) (x : X)
    (w : W) (K : List Pf → Rom.OComp (rom lam) β) :
    (proveAll A isk [(x, w)]).bind (fun πs => K πs.val) =
      (toRom (A.P isk x w)).bind fun π => K [π] := by
  simp only [proveAll, bind_assoc, Rom.OComp.bind]

theorem sessionExp_single (ivk : IVK) (isk : ISK) (x : X) (w : W) :
    Gen.sessionExp (toGen A) ivk isk [(x, w)] = toRom (ZKCP.sessionExp A ivk isk x w) := by
  have h :=
    proveAll_single A isk x w fun πs => Gen.verifyAll (toGen A) ivk (([(x, w)].map Prod.fst).zip πs)
  have e : Gen.sessionExp (toGen A) ivk isk [(x, w)] = (proveAll A isk [(x, w)]).bind fun πs =>
      Gen.verifyAll (toGen A) ivk (([(x, w)].map Prod.fst).zip πs.val) := rfl
  rw [e, h]
  have e2 : ZKCP.sessionExp A ivk isk x w = (A.P isk x w).bind fun π => A.V ivk x π := rfl
  rw [e2, Rom.toRom_bind]
  congr 1
  funext π
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, Gen.verifyAll,
    rbind_eq, rpure_eq, Rom.OComp.bind, Bool.and_true, toGen]
  exact bind_pure _

theorem completenessExp_single (i : I) (x : X) (w : W) :
    Gen.completenessExp (toGen A) i [(x, w)] = toRom (ZKCP.completenessExp A i x w) := by
  have e : Gen.completenessExp (toGen A) i [(x, w)] = (toRom (A.C i)).bind fun key =>
      Gen.sessionExp (toGen A) key.1 key.2 [(x, w)] := rfl
  have e2 : ZKCP.completenessExp A i x w =
      (A.C i).bind fun key => ZKCP.sessionExp A key.1 key.2 x w := rfl
  rw [e, e2, Rom.toRom_bind]
  simp only [sessionExp_single]

theorem completeness_iff (α : ℝ≥0∞) :
    Gen.HasCompletenessError (toPair R) (toGen A) 1 α ↔ ZKCP.HasCompletenessError R A α := by
  constructor
  · intro h i x w hR
    have := h i [(x, w)] ⟨by simp, by simpa [toPair] using hR⟩
    rwa [completenessExp_single, Rom.Pr_toRom] at this
  · rintro h i b ⟨hl, hv⟩
    match b, hl, hv with
    | [], _, _ =>
      have e : Gen.completenessExp (toGen A) i [] = (toRom (A.C i)).bind fun _ => .pure true := rfl
      rw [e, Rom.Pr_bind_pure]
      simp [Rom.Pr, Rom.PrCoins, Prob.pr]
    | [(x, w)], _, hv =>
      rw [completenessExp_single, Rom.Pr_toRom]
      exact h i x w (hv (x, w) (by simp))
    | _ :: _ :: _, hl, _ => simp at hl

/-! ### Index binding -/

theorem bindingBad_eq : Gen.bindingBad (toPair R) = ZKCP.bindingBad R := by
  ext o
  rcases o with ⟨c, iStar, x, w⟩
  cases iStar <;> rfl

theorem bindingExp_toRom {St : Type} (E : Extractor lam I X W IVK Pf)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    Gen.bindingExp (toGen A) (extTo E) (toRom Ct) (fun st => toRom (Pt st)) =
      toRom (ZKCP.bindingExp A E Ct Pt) := by
  have e : ZKCP.bindingExp A E Ct Pt = Ct.withTrace.bind fun o1 => (Pt o1.1.2).withTrace.bind fun o2 =>
      (A.V o1.1.1 o2.1.1 o2.1.2).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 o1.2, o2.1.1, E.Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ := rfl
  have e' : Gen.bindingExp (toGen A) (extTo E) (toRom Ct) (fun st => toRom (Pt st))
      = (toRom Ct).withTrace.bind fun o1 => (toRom (Pt o1.1.2)).withTrace.bind fun o2 =>
        (toRom (A.V o1.1.1 o2.1.1 o2.1.2)).bind fun c =>
          .pure ⟨c, E.Ei o1.1.1 (trOf o1.2), o2.1.1,
              E.Ew o1.1.1 (trOf o1.2) o2.1.1 o2.1.2 (trOf o2.2)⟩ := rfl
  rw [e, e']
  simp only [Rom.toRom_bind, Rom.toRom_withTrace, Rom.toRom_pure, bind_assoc, Rom.OComp.bind]

theorem bindingWith_iff (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    Gen.HasIndexBindingWith (toPair R) (toGen A) (extTo E) ε ↔
    ZKCP.HasIndexBindingWith R A E ε := by
  constructor
  · intro h tC tP St Ct Pt hC hP
    have := h tC tP St (toRom Ct) (fun st => toRom (Pt st)) ((Rom.queryBound_toRom _ _).2 hC)
      fun st => (Rom.queryBound_toRom _ _).2 (hP st)
    rwa [bindingExp_toRom, Rom.Pr_toRom, bindingBad_eq] at this
  · intro h tC tP St Ct Pt hC hP
    have := h tC tP St (ofRom Ct) (fun st => ofRom (Pt st))
      ((Rom.queryBound_toRom _ _).1 (by rwa [Rom.toRom_ofRom]))
      fun st => (Rom.queryBound_toRom _ _).1 (by rw [Rom.toRom_ofRom]; exact hP st)
    rw [← bindingBad_eq, ← Rom.Pr_toRom (E := fun _ => Gen.bindingBad (toPair R)),
      ← bindingExp_toRom] at this
    simpa only [Rom.toRom_ofRom] using this

theorem extTo_extOf (E : Gen.Extractor (rom lam) I X W IVK Pf) : extTo (extOf E) = E := by
  cases E
  simp [extTo, extOf, Rom.trTo_trOf]

theorem binding_iff (ε : ℕ → ℕ → ℝ≥0∞) :
    Gen.HasIndexBinding (toPair R) (toGen A) ε ↔ ZKCP.HasIndexBinding R A ε := by
  constructor
  · rintro ⟨E, h⟩
    exact ⟨extOf E, (bindingWith_iff R A (extOf E) ε).1 (by rwa [extTo_extOf])⟩
  · rintro ⟨E, h⟩
    exact ⟨extTo E, (bindingWith_iff R A E ε).2 h⟩

/-! ### Index privacy -/

theorem queryBound_advTo (V : AdvVerifier lam X Pf) :
    ∀ t, V.QueryBound t → (advTo V).QueryBound t := by
  induction V with
  | halt => intro t _; trivial
  | query q k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih r t (h r)
  | sample n k ih => exact fun t h r => ih r t (h r)
  | request k ih =>
    intro t h
    simp only [advTo, Gen.AdvVerifier.QueryBound]
    intro l
    rcases l with _ | ⟨⟨x, π⟩, _ | ⟨_, _⟩⟩
    · trivial
    · exact ih x π t (h x π)
    · trivial

theorem val_eq {x : X} (l : Gen.Slots Pf [x]) : l.val = [head1 l] := by
  obtain ⟨l, hl⟩ := l
  match l, hl with
  | [π], _ => rfl

theorem realLoop_map (Z : ViewEnv lam IVK X W Pf) (isk : ISK) (V : AdvVerifier lam X Pf) :
    ∀ (n : ℕ) (v : Gen.View (rom lam) IVK X Pf),
      (Gen.realLoop (toGen A) (envTo Z) isk (advTo V) n v).bind (fun v' => .pure (viewOf v'))
        = toRom (ZKCP.realLoop A Z isk V n (viewOf v)) := by
  induction V with
  | halt => intro n v; rfl
  | query q k ih =>
    intro n v
    simp only [advTo, Gen.realLoop, ZKCP.realLoop, Rom.OComp.bind, ih]
    simp [viewOf, Rom.toRom, Rom.trOf]
    rfl
  | sample m k ih =>
    intro n v
    simp only [advTo, Gen.realLoop, ZKCP.realLoop, Rom.OComp.bind, ih]
    simp [viewOf, Rom.toRom]
  | request k ih =>
    intro n v
    cases n with
    | zero => simp only [advTo, Gen.realLoop, ZKCP.realLoop]; rfl
    | succ n =>
      cases hz : Z (viewOf v) with
      | none => simp only [advTo, Gen.realLoop, ZKCP.realLoop, envTo, hz, Option.map_none]; rfl
      | some xw =>
        obtain ⟨x, w⟩ := xw
        simp only [advTo, Gen.realLoop, ZKCP.realLoop, envTo, hz, Option.map_some, bind_assoc]
        have h := proveAll_single A isk x w fun πs =>
          (Gen.realLoop (toGen A) (envTo Z) isk
            (match Gen.Batch.released [(x, w, true)] πs with
              | [(x, π)] => advTo (k x π)
              | _ => .halt) n
            { v with sessions := v.sessions ++ [Gen.Batch.released [(x, w, true)] πs] }).bind
            fun v' => .pure (viewOf v')
        refine Eq.trans h ?_
        rw [Rom.toRom_bind]
        congr 1
        funext π
        have hrel : Gen.Batch.released [(x, w, true)] [π] = [(x, π)] := rfl
        simp only [hrel]
        rw [ih]
        simp [viewOf]

theorem idealLoop_map (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (Z : ViewEnv lam IVK X W Pf)
    (V : AdvVerifier lam X Pf) :
    ∀ (n : ℕ) (v : Gen.View (rom lam) IVK X Pf) (s : Sim.St),
      (Gen.idealLoop Sim (envTo Z) (advTo V) n v s).map viewOf
        = ZKCP.idealLoop (simOf Sim) Z V n (viewOf v) s := by
  induction V with
  | halt => intro n v s; simp only [advTo, Gen.idealLoop, ZKCP.idealLoop, PMF.pure_map]
  | query q k ih =>
    intro n v s
    simp only [advTo, Gen.idealLoop, ZKCP.idealLoop, PMF.map_bind, ih]
    simp [viewOf, simOf, Rom.trOf]
    rfl
  | sample m k ih =>
    intro n v s
    simp only [advTo, Gen.idealLoop, ZKCP.idealLoop, PMF.map_bind, ih]
    simp [viewOf]
  | request k ih =>
    intro n v s
    cases n with
    | zero => simp only [advTo, Gen.idealLoop, ZKCP.idealLoop, PMF.pure_map]
    | succ n =>
      cases hz : Z (viewOf v) with
      | none =>
        simp only [advTo, Gen.idealLoop, ZKCP.idealLoop, envTo, hz, Option.map_none, PMF.pure_map]
      | some xw =>
        obtain ⟨x, w⟩ := xw
        simp only [advTo, Gen.idealLoop, ZKCP.idealLoop, envTo, hz, Option.map_some, PMF.map_bind]
        show (Sim.prove s [x]).bind _ = ((Sim.prove s [x]).map _).bind _
        rw [PMF.bind_map]
        congr 1
        funext out
        have hzip : ([x] : List X).zip out.1.val = [(x, head1 out.1)] := by rw [val_eq out.1]; rfl
        show (Gen.idealLoop Sim (envTo Z)
          (match ([x] : List X).zip out.1.val with
            | [(x, π)] => advTo (k x π)
            | _ => .halt) n { v with sessions := v.sessions ++ [([x] : List X).zip out.1.val] } out.2).map viewOf = _
        rw [hzip]
        simp only [Function.comp]
        rw [ih]
        simp [viewOf]

theorem mem_trOf (tr : Rom.Trace (rom lam)) (q : Str) (r : Digest lam) :
    (q, r) ∈ trOf tr ↔ (⟨(), q, r⟩ : Rom.QA (rom lam)) ∈ tr := by
  simp only [Rom.trOf, List.mem_map]
  constructor
  · rintro ⟨⟨⟨⟩, q', r'⟩, h, e⟩
    cases e
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem consistent_iff (tr : Rom.Trace (rom lam)) :
    Gen.TraceConsistent tr ↔ (trOf tr).Consistent := by
  constructor
  · intro h q r r' h1 h2
    exact h () q r r' ((mem_trOf tr q r).1 h1) ((mem_trOf tr q r').1 h2)
  · rintro h ⟨⟩ q r r' h1 h2
    exact h q r r' ((mem_trOf tr q r).2 h1) ((mem_trOf tr q r').2 h2)

/-- For `toPair R` and `toGen A`: Gen's privacy at batches of one gives the strong form of
`HasIndexPrivacy` of Defs.lean, with the same simulator (`simOf Sim`) and error. -/
theorem strongPrivacy_of_gen (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.HasIndexPrivacyWith (toPair R) (toGen A) 1 Sim ζ) :
    ZKCP.HasStrongIndexPrivacyWith R A (simOf Sim) ζ := by
  intro i Z hZ tV Vt N hb
  have hval : (envTo Z).IsValid (toPair R) 1 i := by
    intro v b hbv
    simp only [envTo, Option.map_eq_some_iff] at hbv
    obtain ⟨⟨x, w⟩, hz, rfl⟩ := hbv
    exact ⟨by simp [Gen.Batch.pairs], by simpa [Gen.Batch.pairs, toPair] using hZ _ x w hz⟩
  obtain ⟨h1, h2⟩ :=
    h i (envTo Z) hval tV (fun ivk => advTo (Vt ivk)) N fun ivk => queryBound_advTo _ _ (hb ivk)
  have hreal : ∀ T, ZKCP.Pr (ZKCP.realExp A Vt Z i N) (fun _ => T) =
      Rom.Pr (Gen.realExp (toGen A) (fun ivk => advTo (Vt ivk)) (envTo Z) i N)
        (fun _ => viewOf ⁻¹' T) := by
    intro T
    have e : (Gen.realExp (toGen A) (fun ivk => advTo (Vt ivk)) (envTo Z) i N).bind
          (fun v' => .pure (viewOf v')) =
        toRom (ZKCP.realExp A Vt Z i N) := by
      have e1 : Gen.realExp (toGen A) (fun ivk => advTo (Vt ivk)) (envTo Z) i N = (toRom (A.C i)).bind fun key =>
          Gen.realLoop (toGen A) (envTo Z) key.2 (advTo (Vt key.1)) N ⟨key.1, [], [], []⟩ := rfl
      have e2 : ZKCP.realExp A Vt Z i N = (A.C i).bind fun key =>
          ZKCP.realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩ := rfl
      rw [e1, e2, bind_assoc, Rom.toRom_bind]
      congr 1
      funext key
      rw [realLoop_map]
      rfl
    rw [← Rom.Pr_bind_pure (φ := viewOf) (T := fun _ => T), e, Rom.Pr_toRom]
  have hideal : ∀ T, ZKCP.prob (ZKCP.idealExp R (simOf Sim) Vt Z i N) T =
      Prob.pr (Gen.idealExp (toPair R) Sim (fun ivk => advTo (Vt ivk)) (envTo Z) i N)
        (viewOf ⁻¹' T) := by
    intro T
    rw [← Prob.pr_map]
    have e : (Gen.idealExp (toPair R) Sim (fun ivk => advTo (Vt ivk)) (envTo Z) i N).map viewOf
        = ZKCP.idealExp R (simOf Sim) Vt Z i N := by
      simp only [Gen.idealExp, ZKCP.idealExp, PMF.map_bind, idealLoop_map]
      rfl
    rw [e]; rfl
  constructor
  · show Prob.sd _ _ ≤ _
    simp only [hreal, hideal]
    exact (Prob.sd_comap_le _ _ viewOf).trans h1
  · rw [hideal]
    refine le_antisymm (le_trans (Prob.pr_mono _ ?_) (le_of_eq h2)) (zero_le _)
    intro v hv
    simpa [consistent_iff] using hv

/-- All three together, at B = 1, for `toPair R` and `toGen A`, with extractor and simulator named:
`Gen.IsZKCPArgWith` → `IsZKCPArgWith` of ZKCP/Defs.lean. -/
theorem isZKCPArgWith_of_gen (E : Extractor lam I X W IVK Pf)
    (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.IsZKCPArgWith (toPair R) (toGen A) 1 (extTo E) Sim α ε ζ) :
    ZKCP.IsZKCPArgWith R A E (simOf Sim) α ε ζ where
  completeness := (completeness_iff R A α).1 h.completeness
  indexBinding := (bindingWith_iff R A E ε).1 h.indexBinding
  indexPrivacy := strongPrivacy_of_gen R A Sim ζ h.indexPrivacy

/-- The form without names: for `toPair R` and `toGen A`, Gen's primitive at batches of one gives
the primitive of ZKCP/Defs.lean, with the same three bounds. -/
theorem isZKCPArg_of_gen (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.IsZKCPArg (toPair R) (toGen A) 1 α ε ζ) : ZKCP.IsZKCPArg R A α ε ζ where
  completeness := (completeness_iff R A α).1 h.completeness
  indexBinding := (binding_iff R A ε).1 h.indexBinding
  indexPrivacy := by
    obtain ⟨Sim, hS⟩ := h.indexPrivacy
    exact ⟨simOf Sim, (strongPrivacy_of_gen R A Sim ζ hS).toHasIndexPrivacyWith⟩

end ZKCP.Special
