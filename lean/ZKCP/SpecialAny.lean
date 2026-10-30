-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/SpecialAny.lean: any scheme of ZKCP/Gen.lean over one oracle, used with one request in each
call, is a scheme of ZKCP/Defs.lean, and at R_yes = R_no (`toPair R`) what Gen.lean says of it for
batches of at most B ≥ 1 gives what Defs.lean asks.

Why: ZKCP/Special.lean ties Gen.lean to Defs.lean for the schemes `toGen A`, whose prover proves a
batch slot by slot with a prover of Defs.lean. A scheme with real batches (shared rounds) is not of
that form.

Main names:
  `oneOf G`: the scheme of Defs.lean that G gives: its prover calls G.P on the batch [(x, w)] and
    returns the one proof.
  `isZKCPArg_one`: Gen.IsZKCPArg (toPair R) G B α ε ζ with 1 ≤ B → IsZKCPArg R (oneOf G) α ε ζ of
    ZKCP/Defs.lean. isZKCPArg_one ends in `HasIndexPrivacy`, isZKCPArgWith_one
    in the stronger form.
  `mono_B`, `mono_B_with`: Gen's primitive for batches of at most B gives it for batches of at most
    B' ≤ B, with the same three bounds.
  `Agrees G A`: G, called with one request, is A: the same committer and verifier, and
    G.P isk [(x, w)] returns the one-entry list of what A.P isk x w returns.
  For G and A with `Agrees G A`, G at `toPair R`, A at R:
  `completeness_of_gen`: Gen's completeness at B = 1 → ZKCP/Defs.lean, `HasCompletenessError`.
  `bindingWith_of_gen`: Gen's binding, extractor extTo E → ZKCP/Defs.lean, `HasIndexBinding`,
    extractor E.
  `strongPrivacy_of_gen`: Gen's privacy at B = 1, simulator S → the strong form of ZKCP/Defs.lean,
    `HasIndexPrivacy`, same simulator (`simOf S`) and ζ.
  `isZKCPArgWith_of_gen`, `isZKCPArg_of_gen`: all three together.

Notation: ZKCP: see `IsZKCPArg`, ZKCP/Defs.lean; from there too: `HasCompletenessError`,
`HasIndexBinding`, `HasIndexPrivacy`; Gen.lean:
ZKCP/Gen.lean, which has families of oracles, two relations and batches; `extTo E`: a
`Gen.Extractor`: E, an extractor of ZKCP/Defs.lean, translated into the form of Gen.lean; `simOf S`:
a `Simulator` of ZKCP/Defs.lean: S, a `Gen.Simulator`, translated back (both: ZKCP/SpecialDefs.lean,
its head).

Limits: a theorem with R_yes ≠ R_no has no way back here. Only implications. The converses are false
in general: Defs.lean says nothing of what G does on other batches. A session of Defs.lean becomes a
batch with one entry, which is the adversary's own; so N, which counts batches in Gen.lean, counts
requests here, and nothing of what Gen.lean says about hidden entries is used. The three bounds stay
those of B slots, though one slot is filled. Nothing but the three clauses is carried: no refined or
adaptive completeness, no session-augmented index binding, no correctness of extraction.
(`HasExtractionError`, ZKCP/Optional.lean: `extraction_oneOf`, ZKCP/ExtractionMaps.lean.)
-/
import ZKCP.Special

open scoped ENNReal

namespace ZKCP.SpecialAny

open Rom (rom toRom ofRom trTo trOf famOf)
open ZKCP.Special

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-! ### Smaller batches -/

theorem mono_B {S : Rom.OSpec} (R : Gen.RelPair I X W PP) (G : Gen.Arg S I X W IVK ISK Pf)
    {B B' : ℕ} (h : B' ≤ B) {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (H : Gen.IsZKCPArg R G B α ε ζ) :
    Gen.IsZKCPArg R G B' α ε ζ :=
  ⟨fun i b hb => H.completeness i b ⟨le_trans hb.1 h, hb.2⟩, H.indexBinding,
    let ⟨Sim, hS⟩ := H.indexPrivacy
    ⟨Sim, fun i Z hZ => hS i Z fun v b hv => ⟨le_trans (hZ v b hv).1 h, (hZ v b hv).2⟩⟩⟩

theorem mono_B_with {S : Rom.OSpec} (R : Gen.RelPair I X W PP) (G : Gen.Arg S I X W IVK ISK Pf)
    {B B' : ℕ} (h : B' ≤ B) (E : Gen.Extractor S I X W IVK Pf) (Sim : Gen.Simulator S PP IVK X Pf)
    {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (H : Gen.IsZKCPArgWith R G B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R G B' E Sim α ε ζ :=
  ⟨fun i b hb => H.completeness i b ⟨le_trans hb.1 h, hb.2⟩, H.indexBinding,
    fun i Z hZ => H.indexPrivacy i Z fun v b hv => ⟨le_trans (hZ v b hv).1 h, (hZ v b hv).2⟩⟩

/-! ### One request in each call -/

/-- G, called with one request, is A. -/
structure Agrees (G : Gen.Arg (rom lam) I X W IVK ISK Pf) (A : Arg lam I X W IVK ISK Pf) :
    Prop where
  C : ∀ i, G.C i = toRom (A.C i)
  V : ∀ ivk x π, G.V ivk x π = toRom (A.V ivk x π)
  P : ∀ isk x w,
    (G.P isk [(x, w)]).bind (fun πs => .pure πs.val) = (toRom (A.P isk x w)).bind fun π => .pure [π]

/-- The scheme of Defs.lean that G gives. -/
def oneOf (G : Gen.Arg (rom lam) I X W IVK ISK Pf) : Arg lam I X W IVK ISK Pf where
  C i := ofRom (G.C i)
  P isk x w := ofRom ((G.P isk [(x, w)]).bind fun πs => .pure (head1 πs))
  V ivk x π := ofRom (G.V ivk x π)

theorem agrees_oneOf (G : Gen.Arg (rom lam) I X W IVK ISK Pf) : Agrees G (oneOf G) where
  C _ := (Rom.toRom_ofRom _).symm
  V _ _ _ := (Rom.toRom_ofRom _).symm
  P isk x w := by
    show _ =
      (toRom (ofRom ((G.P isk [(x, w)]).bind fun πs => .pure (head1 πs)))).bind fun π => .pure [π]
    rw [Rom.toRom_ofRom, bind_assoc]
    congr 1
    funext πs
    show Rom.OComp.pure πs.val = Rom.OComp.pure [head1 πs]
    rw [val_eq πs]

/-- `toGen A` agrees with A: the case of ZKCP/Special.lean. -/
theorem agrees_toGen (A : Arg lam I X W IVK ISK Pf) : Agrees (toGen A) A :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun isk x w => proveAll_single A isk x w fun l => .pure l⟩

variable (R : IndexedRelation I X W PP)
  {G : Gen.Arg (rom lam) I X W IVK ISK Pf} {A : Arg lam I X W IVK ISK Pf} (h : Agrees G A)

include h

/-- P on a batch of one, followed by anything that reads the list of proofs. -/
theorem P_bind {β : Type} (isk : ISK) (x : X) (w : W) (K : List Pf → Rom.OComp (rom lam) β) :
    (G.P isk [(x, w)]).bind (fun πs => K πs.val) = (toRom (A.P isk x w)).bind fun π => K [π] := by
  have e := congrArg (fun c => c.bind K) (h.P isk x w)
  simpa only [bind_assoc, Rom.OComp.bind] using e

/-! ### Completeness -/

theorem sessionExp_single (ivk : IVK) (isk : ISK) (x : X) (w : W) :
    Gen.sessionExp G ivk isk [(x, w)] = toRom (ZKCP.sessionExp A ivk isk x w) := by
  have h1 := P_bind h isk x w fun πs => Gen.verifyAll G ivk (([(x, w)].map Prod.fst).zip πs)
  have e : Gen.sessionExp G ivk isk [(x, w)] =
      (G.P isk [(x, w)]).bind fun πs => Gen.verifyAll G ivk (([(x, w)].map Prod.fst).zip πs.val) :=
    rfl
  rw [e, h1]
  have e2 : ZKCP.sessionExp A ivk isk x w = (A.P isk x w).bind fun π => A.V ivk x π := rfl
  rw [e2, Rom.toRom_bind]
  congr 1
  funext π
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, Gen.verifyAll,
    rbind_eq, rpure_eq, Rom.OComp.bind, Bool.and_true, h.V]
  exact bind_pure _

theorem completenessExp_single (i : I) (x : X) (w : W) :
    Gen.completenessExp G i [(x, w)] = toRom (ZKCP.completenessExp A i x w) := by
  have e : Gen.completenessExp G i [(x, w)] =
      (G.C i).bind fun key => Gen.sessionExp G key.1 key.2 [(x, w)] := rfl
  have e2 : ZKCP.completenessExp A i x w =
      (A.C i).bind fun key => ZKCP.sessionExp A key.1 key.2 x w := rfl
  rw [e, e2, Rom.toRom_bind, h.C]
  simp only [sessionExp_single h]

theorem completeness_of_gen (α : ℝ≥0∞) (H : Gen.HasCompletenessError (toPair R) G 1 α) :
    ZKCP.HasCompletenessError R A α := by
  intro i x w hR
  have := H i [(x, w)] ⟨by simp, by simpa [toPair] using hR⟩
  rwa [completenessExp_single h, Rom.Pr_toRom] at this

/-! ### Index binding -/

theorem bindingExp_toRom {St : Type} (E : Extractor lam I X W IVK Pf)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    Gen.bindingExp G (extTo E) (toRom Ct) (fun st => toRom (Pt st)) =
      toRom (ZKCP.bindingExp A E Ct Pt) := by
  have e : ZKCP.bindingExp A E Ct Pt = Ct.withTrace.bind fun o1 => (Pt o1.1.2).withTrace.bind fun o2 =>
      (A.V o1.1.1 o2.1.1 o2.1.2).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 o1.2, o2.1.1, E.Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ := rfl
  have e' : Gen.bindingExp G (extTo E) (toRom Ct) (fun st => toRom (Pt st))
      = (toRom Ct).withTrace.bind fun o1 => (toRom (Pt o1.1.2)).withTrace.bind fun o2 =>
        (G.V o1.1.1 o2.1.1 o2.1.2).bind fun c =>
          .pure ⟨c, E.Ei o1.1.1 (trOf o1.2), o2.1.1,
              E.Ew o1.1.1 (trOf o1.2) o2.1.1 o2.1.2 (trOf o2.2)⟩ := rfl
  rw [e, e']
  simp only [h.V, Rom.toRom_bind, Rom.toRom_withTrace, Rom.toRom_pure, bind_assoc, Rom.OComp.bind]

theorem bindingWith_of_gen (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞)
    (H : Gen.HasIndexBindingWith (toPair R) G (extTo E) ε) :
    ZKCP.HasIndexBindingWith R A E ε := by
  intro tC tP St Ct Pt hC hP
  have := H tC tP St (toRom Ct) (fun st => toRom (Pt st)) ((Rom.queryBound_toRom _ _).2 hC)
    fun st => (Rom.queryBound_toRom _ _).2 (hP st)
  rwa [bindingExp_toRom h, Rom.Pr_toRom, bindingBad_eq] at this

theorem binding_of_gen (ε : ℕ → ℕ → ℝ≥0∞) (H : Gen.HasIndexBinding (toPair R) G ε) :
    ZKCP.HasIndexBinding R A ε := by
  obtain ⟨E, hE⟩ := H
  exact ⟨extOf E, bindingWith_of_gen R h (extOf E) ε (by rwa [extTo_extOf])⟩

/-! ### Index privacy -/

theorem realLoop_map (Z : ViewEnv lam IVK X W Pf) (isk : ISK) (V : AdvVerifier lam X Pf) :
    ∀ (n : ℕ) (v : Gen.View (rom lam) IVK X Pf),
      (Gen.realLoop G (envTo Z) isk (advTo V) n v).bind (fun v' => .pure (viewOf v')) =
        toRom (ZKCP.realLoop A Z isk V n (viewOf v)) := by
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
        have h1 := P_bind h isk x w fun πs =>
          (Gen.realLoop G (envTo Z) isk
            (match Gen.Batch.released [(x, w, true)] πs with
              | [(x, π)] => advTo (k x π)
              | _ => .halt) n
            { v with sessions := v.sessions ++ [Gen.Batch.released [(x, w, true)] πs] }).bind
            fun v' => .pure (viewOf v')
        refine Eq.trans h1 ?_
        rw [Rom.toRom_bind]
        congr 1
        funext π
        have hrel : Gen.Batch.released [(x, w, true)] [π] = [(x, π)] := rfl
        simp only [hrel]
        rw [ih]
        simp [viewOf]

/-- Under `h : Agrees G A`, G at `toPair R`, A at R: Gen's privacy at batches of one gives the
strong form of `HasIndexPrivacy` of Defs.lean, with the same simulator (`simOf Sim`) and error. -/
theorem strongPrivacy_of_gen (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (H : Gen.HasIndexPrivacyWith (toPair R) G 1 Sim ζ) :
    ZKCP.HasStrongIndexPrivacyWith R A (simOf Sim) ζ := by
  intro i Z hZ tV Vt N hb
  have hval : (envTo Z).IsValid (toPair R) 1 i := by
    intro v b hbv
    simp only [envTo, Option.map_eq_some_iff] at hbv
    obtain ⟨⟨x, w⟩, hz, rfl⟩ := hbv
    exact ⟨by simp [Gen.Batch.pairs], by simpa [Gen.Batch.pairs, toPair] using hZ _ x w hz⟩
  obtain ⟨h1, h2⟩ :=
    H i (envTo Z) hval tV (fun ivk => advTo (Vt ivk)) N fun ivk => queryBound_advTo _ _ (hb ivk)
  have hreal : ∀ T, ZKCP.Pr (ZKCP.realExp A Vt Z i N) (fun _ => T) =
      Rom.Pr (Gen.realExp G (fun ivk => advTo (Vt ivk)) (envTo Z) i N) (fun _ => viewOf ⁻¹' T) := by
    intro T
    have e : (Gen.realExp G (fun ivk => advTo (Vt ivk)) (envTo Z) i N).bind
          (fun v' => .pure (viewOf v')) =
        toRom (ZKCP.realExp A Vt Z i N) := by
      have e1 : Gen.realExp G (fun ivk => advTo (Vt ivk)) (envTo Z) i N = (G.C i).bind fun key =>
          Gen.realLoop G (envTo Z) key.2 (advTo (Vt key.1)) N ⟨key.1, [], [], []⟩ := rfl
      have e2 : ZKCP.realExp A Vt Z i N =
          (A.C i).bind fun key => ZKCP.realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩ := rfl
      rw [e1, e2, h.C, bind_assoc, Rom.toRom_bind]
      congr 1
      funext key
      rw [realLoop_map h]
      rfl
    rw [← Rom.Pr_bind_pure (φ := viewOf) (T := fun _ => T), e, Rom.Pr_toRom]
  have hideal : ∀ T, ZKCP.prob (ZKCP.idealExp R (simOf Sim) Vt Z i N) T =
      Prob.pr (Gen.idealExp (toPair R) Sim (fun ivk => advTo (Vt ivk)) (envTo Z) i N)
        (viewOf ⁻¹' T) := by
    intro T
    rw [← Prob.pr_map]
    have e : (Gen.idealExp (toPair R) Sim (fun ivk => advTo (Vt ivk)) (envTo Z) i N).map viewOf =
        ZKCP.idealExp R (simOf Sim) Vt Z i N := by
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

/-! ### All three together -/

theorem isZKCPArgWith_of_gen (E : Extractor lam I X W IVK Pf)
    (Sim : Gen.Simulator (rom lam) PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞)
    (H : Gen.IsZKCPArgWith (toPair R) G 1 (extTo E) Sim α ε ζ) :
    ZKCP.IsZKCPArgWith R A E (simOf Sim) α ε ζ where
  completeness := completeness_of_gen R h α H.completeness
  indexBinding := bindingWith_of_gen R h E ε H.indexBinding
  indexPrivacy := strongPrivacy_of_gen R h Sim ζ H.indexPrivacy

theorem isZKCPArg_of_gen (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) (H : Gen.IsZKCPArg (toPair R) G 1 α ε ζ) :
    ZKCP.IsZKCPArg R A α ε ζ where
  completeness := completeness_of_gen R h α H.completeness
  indexBinding := binding_of_gen R h ε H.indexBinding
  indexPrivacy := by
    obtain ⟨Sim, hS⟩ := H.indexPrivacy
    exact ⟨simOf Sim, (strongPrivacy_of_gen R h Sim ζ hS).toHasIndexPrivacyWith⟩

omit h

/-- A scheme over one oracle that has `Gen.IsZKCPArg` at `toPair R` for batches of at most B ≥ 1,
used with one request in each call, meets the definition (ZKCP/Defs.lean), with the same three
bounds. -/
theorem isZKCPArg_one (G : Gen.Arg (rom lam) I X W IVK ISK Pf) {B : ℕ} (hB : 1 ≤ B) (α : ℝ≥0∞)
    (ε ζ : ℕ → ℕ → ℝ≥0∞) (H : Gen.IsZKCPArg (toPair R) G B α ε ζ) :
    ZKCP.IsZKCPArg R (oneOf G) α ε ζ :=
  isZKCPArg_of_gen R (agrees_oneOf G) α ε ζ (mono_B _ G hB H)

/-- The same with extractor and simulator named. -/
theorem isZKCPArgWith_one (G : Gen.Arg (rom lam) I X W IVK ISK Pf) {B : ℕ} (hB : 1 ≤ B)
    (E : Gen.Extractor (rom lam) I X W IVK Pf) (Sim : Gen.Simulator (rom lam) PP IVK X Pf)
    (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) (H : Gen.IsZKCPArgWith (toPair R) G B E Sim α ε ζ) :
    ZKCP.IsZKCPArgWith R (oneOf G) (extOf E) (simOf Sim) α ε ζ :=
  isZKCPArgWith_of_gen R (agrees_oneOf G) (extOf E) Sim α ε ζ
    (by rw [extTo_extOf]; exact mono_B_with _ G hB E Sim H)

end ZKCP.SpecialAny
