-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesTop.lean: (a) from what is asked of the three parts.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

`Three.soundB_of_laws`: if a family of three parts meets `Three.Laws`
(OnBytes/TypedOracleCompiler/Slice/Shapes.lean), then over a uniformly random oracle, for every committer and
prover, the verifier on bytes says yes while the outcome is not fine with probability at most the
three parts' bounds at tC + tP, the term for a stable root, the ID's term (tC + tP + 2)^2 / 2^256
and the term for a clash in the checkers' logs.

How. `join_id_at3` (OnBytes/Slice/JoinOut3.lean) as it lies, (1) with the parts at cut tables, so
that under the oracle with two tables put over it the oracle's own public values ARE these tables
(`pub₀_ov`, `pub₁_ov`, `ov_eq`), and a checker that is deaf to the public strings has one value
under both oracles; (2) with the parts read along "the prover's files" (`PartO.comap`;
`PartO.OK.comap`); (3) with the outcomes let go in which the files themselves show a clash, at that
term; (4) with "not fine" taken into the yes and "false" for the join's own "fine": so what is fine
may hang on the oracle, the seed under the oracle stands in `FineB` itself, and no committer is made
to ask anything.

What is not claimed. AN IMPLICATION: no parts are given that meet `Laws`. All limits
in the heads of Shapes.lean, JoinOut3.lean and JoinDecRec.lean hold here too. The bound says nothing
once it reaches 1.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesMeas
import OnBytes.Tie.IdOff

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {γ γ' Sg : Type}

/-- A part read along a function of the maker's output: its checker looks at f of the output.
All other fields are the part's own. -/
def PartO.comap (s : PartO lam γ Sg) (f : γ' → γ) : PartO lam γ' Sg :=
  { s with chk := fun x => s.chk (f x) }

/-- The maker that puts out f of a maker's output has that maker's log. -/
theorem runEager_withTrace_map (g : Fam (rom lam)) (A : OComp (rom lam) γ') (f : γ' → γ) :
    (A.bind fun x => OComp.pure (f x)).withTrace.runEager g =
      (A.withTrace.runEager g).map fun z => (f z.1, z.2) := by
  rw [Rom.withTrace_bind, OComp.runEager_bind, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun z => ?_)
  show PMF.pure (f z.1, z.2 ++ []) = PMF.pure (f z.1, z.2)
  rw [List.append_nil]

/-- Under every oracle the event of the part read along f, for a maker, is the part's event for the
maker that puts out f of its output. -/
theorem PartO.prCoins_comap (s : PartO lam γ Sg) (f : γ' → γ) (A : OComp (rom lam) γ')
    (g : Fam (rom lam)) :
    PrCoins g A.withTrace ((s.comap f).lose g) =
      PrCoins g (A.bind fun x => OComp.pure (f x)).withTrace (s.lose g) := by
  unfold PrCoins
  rw [runEager_withTrace_map, Prob.pr_map]
  rfl

/-- What the join asks of every part carries over. -/
theorem PartO.OK.comap {s : PartO lam γ Sg} (h : s.OK) (f : γ' → γ) : (s.comap f).OK where
  rare := fun A t hA => by
    have e : Rom.Pr A.withTrace (s.comap f).lose =
        Rom.Pr (A.bind fun x => OComp.pure (f x)).withTrace s.lose :=
      lintegral_congr fun g => s.prCoins_comap f A g
    rw [e]
    have hq : (A.bind fun x => (OComp.pure (f x) : OComp (rom lam) γ)).QueryBound (t + 0) :=
      OComp.QueryBound.bind hA fun _ => trivial
    exact h.rare _ t hq
  meas := fun A => by
    have e : (fun g => PrCoins g A.withTrace ((s.comap f).lose g)) =
        fun g => PrCoins g (A.bind fun x => OComp.pure (f x)).withTrace (s.lose g) :=
      funext fun g => s.prCoins_comap f A g
    rw [e]
    exact h.meas _

namespace Shapes
open OnBytes.Tie (IdKey idCode firstId)

variable {D : DecR} {Xi : Type}

/-- Two tables put over an oracle, one after the other, are their merge put over it once. -/
theorem over_merge (S₀ S₁ : Finset (List Bool)) (T₀ T₁ : Tab) (g : Fam (rom 256)) :
    over S₀ T₀ (over S₁ T₁ g) = over (S₀ ∪ S₁) (mergeT S₀ T₀ T₁) g :=
  over_over S₀ S₁ T₀ T₁ g

/-- Putting a table over an oracle sees the table on its set alone. -/
theorem over_congr (S : Finset (List Bool)) (T T' : Tab) (g : Fam (rom 256))
    (h : ∀ s ∈ S, T s = T' s) : over S T g = over S T' g := by
  funext o s
  cases o
  by_cases hs : s ∈ S
  · rw [over_mem _ _ hs, over_mem _ _ hs, h s hs]
  · rw [over_not_mem _ _ hs, over_not_mem _ _ hs]

namespace Three
variable (Θ : Three D Xi)

/-- The second public strings, at a table cut to the first. -/
def S₁c (T₀ : Tab) : Finset (List Bool) := Θ.S₁ (cutT Θ.S₀ T₀)

/-- The second table as the parts take it: the merge, cut to the second public strings. -/
def T₁c (T₀ T₁ : Tab) : Tab := cutT (Θ.S₁c T₀) (mergeT Θ.S₀ T₀ T₁)

/-- The oracle with two tables put over it. -/
noncomputable def ov (T₀ T₁ : Tab) (g : Fam (rom 256)) : Fam (rom 256) :=
  over Θ.S₀ T₀ (over (Θ.S₁c T₀) T₁ g)

/-- Its values at the first public strings are the first table's. -/
theorem pub₀_ov (T₀ T₁ : Tab) (g : Fam (rom 256)) : Θ.pub₀ (Θ.ov T₀ T₁ g) = cutT Θ.S₀ T₀ := by
  funext s
  unfold pub₀ cutT own ov
  by_cases hs : s ∈ Θ.S₀
  · rw [if_pos hs, if_pos hs, over_mem _ _ hs]
  · rw [if_neg hs, if_neg hs]

/-- Its values at the second public strings are the merge's. -/
theorem pub₁_ov (T₀ T₁ : Tab) (g : Fam (rom 256)) : Θ.pub₁ (Θ.ov T₀ T₁ g) = Θ.T₁c T₀ T₁ := by
  unfold pub₁
  rw [pub₀_ov]
  funext s
  show (if s ∈ Θ.S₁c T₀ then own (Θ.ov T₀ T₁ g) s else default) =
    if s ∈ Θ.S₁c T₀ then mergeT Θ.S₀ T₀ T₁ s else default
  by_cases hs : s ∈ Θ.S₁c T₀
  · rw [if_pos hs, if_pos hs]
    unfold own ov mergeT
    by_cases h0 : s ∈ Θ.S₀
    · rw [over_mem _ _ h0, if_pos h0]
    · rw [over_not_mem _ _ h0, over_mem _ _ hs, if_neg h0]
  · rw [if_neg hs, if_neg hs]

/-- It is the oracle with the parts' own two tables, merged, put over it. -/
theorem ov_eq (T₀ T₁ : Tab) (g : Fam (rom 256)) :
    Θ.ov T₀ T₁ g = over (Θ.S₀ ∪ Θ.S₁ (cutT Θ.S₀ T₀))
      (mergeT Θ.S₀ (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)) g := by
  unfold ov
  rw [over_merge]
  refine over_congr _ _ _ g fun s hs => ?_
  unfold mergeT T₁c cutT mergeT
  by_cases h0 : s ∈ Θ.S₀
  · rw [if_pos h0, if_pos h0, if_pos h0]
  · have h1 : s ∈ Θ.S₁c T₀ := (Finset.mem_union.1 hs).resolve_left h0
    rw [if_neg h0, if_neg h0, if_pos h1]

variable {Θ}

/-- The first key of an ID does not see the entries at strings that are no key's string. -/
theorem firstId_offSet_of_apart (S : Finset (List Bool)) (h : ∀ k s, idCode k = some s → s ∉ S)
    (id : ZKCP.Digest 256) (σ : Trace (rom 256)) : firstId id (offSet S σ) = firstId id σ :=
  OnBytes.Tie.firstId_filter id _ σ fun e _ he => by
    have hm : e.2.1 ∈ S := by simpa using he
    cases hr : OnBytes.Tie.idRead e.2.1 with
    | none => rfl
    | some k => exact absurd hm (h k _ ((OnBytes.Tie.idRead_iff k _).1 hr))

/-- So at the public strings, from the clause `apart`. -/
theorem idOff_of_apart (h : ∀ k s, idCode k = some s → s ∉ Θ.S₀ ∧ ∀ T₀, s ∉ Θ.S₁ T₀)
    (S : Finset (List Bool)) (hS : S = Θ.S₀ ∨ ∃ T₀, S = Θ.S₁ T₀) (id : ZKCP.Digest 256)
    (σ : Trace (rom 256)) : firstId id (offSet S σ) = firstId id σ :=
  firstId_offSet_of_apart S (fun k s hk => by
    rcases hS with rfl | ⟨T₀, rfl⟩
    · exact (h k s hk).1
    · exact (h k s hk).2 T₀) id σ

/-- What is not fine stays so when the entries at public strings are left out of both logs. -/
theorem not_fineB_off {bK bE bF bC : ℕ → ℝ≥0∞} {bS : ℕ → ℕ → ℝ≥0∞}
    (hΘ : Θ.Laws bK bE bF bC bS) (S : Finset (List Bool))
    (hS : S = Θ.S₀ ∨ ∃ T₀, S = Θ.S₁ T₀) (St : Type) (g : Fam (rom 256)) (w : Outcome St)
    (h : ¬ Θ.FineB St g w) : ¬ Θ.FineB St g (offBoth S w) := by
  rintro ⟨k, rec, hk, ho, hr, hg⟩
  refine h ⟨k, rec, ?_, ho, hr, ?_⟩
  · rw [← idOff_of_apart hΘ.apart S hS]
    exact hk
  · rw [← hΘ.rawOff S k _ _ hS]
    exact hg

/-- Where the committer's log shows no key for the ID nothing is fine: so "fine" is the empty set of
oracles there. -/
theorem measF_none {St : Type} {w : Outcome St} (hk : firstId w.1.1.1.1 w.1.1.2 = none) :
    MeasurableSet {g | Θ.FineB St g w} := by
  have e : {g | Θ.FineB St g w} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨k, rec, hk', -⟩
    rw [hk] at hk'
    cases hk'
  rw [e]
  exact MeasurableSet.empty

/-- Where it shows the key k, "fine" is a property of k's record under the oracle. -/
theorem measF_some {bK bE bF bC : ℕ → ℝ≥0∞} {bS : ℕ → ℕ → ℝ≥0∞}
    (hΘ : Θ.Laws bK bE bF bC bS) {St : Type} {w : Outcome St} {k : IdKey}
    (hk : firstId w.1.1.1.1 w.1.1.2 = some k) : MeasurableSet {g | Θ.FineB St g w} := by
  have e : {g | Θ.FineB St g w} = {g | ∃ rec, Θ.recU g k = some rec ∧ (Θ.okKey k ∧
      goodDecR Θ.A (Θ.xReq w.1.2) rec (Θ.rawU k w.1.1.2 (Run.bytesToDig k.2.2.root)))} := by
    ext g
    constructor
    · rintro ⟨k', rec, hk', ho, hr, hg⟩
      rw [hk] at hk'
      cases hk'
      exact ⟨rec, hr, ho, hg⟩
    · rintro ⟨rec, hr, ho, hg⟩
      exact ⟨k, rec, hk, ho, hr, hg⟩
  rw [e]
  exact hΘ.measR k _

/-- Yes-and-not-fine is a measurable set of oracles. -/
theorem measurableSet_event {bK bE bF bC : ℕ → ℝ≥0∞} {bS : ℕ → ℕ → ℝ≥0∞}
    (hΘ : Θ.Laws bK bE bF bC bS) (St : Type) (w : Outcome St) :
    MeasurableSet {g | Θ.VerifyB g w.1.1.1.1 w.1.2 = true ∧ ¬ Θ.FineB St g w} := by
  refine (Θ.measurableSet_verifyB hΘ.measR _ _).inter (MeasurableSet.compl ?_)
  have key : ∀ o, firstId w.1.1.1.1 w.1.1.2 = o → MeasurableSet {g | Θ.FineB St g w} := by
    intro o hk
    cases o with
    | none => exact measF_none hk
    | some k => exact measF_some hΘ hk
  exact key _ rfl

/-- (a) FROM WHAT IS ASKED. By `join_id_at3` (OnBytes/Slice/JoinOut3.lean) as it lies: the parts
at cut tables, read along "the prover's files"; the outcomes let go in which the files show a clash;
"not fine" taken into the yes, so that what is fine may hang on the oracle. -/
theorem soundB_of_laws {bK bE bF bC : ℕ → ℝ≥0∞} {bS : ℕ → ℕ → ℝ≥0∞}
    (hΘ : Θ.Laws bK bE bF bC bS) :
    Θ.SoundB (eps bK bE bF bC bS) := by
  intro St C P tC tP hC hP
  have hX : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (Θ.S₁c T₀) T₁ (pinOn Θ.S₀ T₀ C))
      fun b => pinOn (Θ.S₁c T₀) T₁ (pinOn Θ.S₀ T₀ (P b))).withTrace
      (fun g => {w | Θ.ClashB (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁) g w.1.2}) ≤ bC (tC + tP) :=
    fun T₀ T₁ => hΘ.clash (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁) _
      (twoExp (pinOn (Θ.S₁c T₀) T₁ (pinOn Θ.S₀ T₀ C))
        fun b => pinOn (Θ.S₁c T₀) T₁ (pinOn Θ.S₀ T₀ (P b)))
      (fun z => z.2) (tC + tP)
      (queryBound_twoExp _ _ tC tP (queryBound_pinOn _ _ _ tC (queryBound_pinOn _ _ C tC hC))
        fun b => queryBound_pinOn _ _ _ tP (queryBound_pinOn _ _ (P b) tP (hP b)))
  have h := join_id_at3 Θ.S₀ Θ.S₁c C Prod.fst P
    (fun T₀ T₁ => Θ.key (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)) tC tP hC hP
    (fun T₀ T₁ => (Θ.K (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)).comap fun z => z.2)
    (fun T₀ T₁ => (Θ.E (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)).comap fun z => z.2)
    (fun T₀ T₁ => (Θ.F (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)).comap fun z => z.2)
    (fun _ _ => (hΘ.okK _ _).comap _) (fun _ _ => (hΘ.okE _ _).comap _)
    (fun _ _ => (hΘ.okF _ _).comap _) bS (fun _ _ => hΘ.stable _ _)
    (fun _ _ => hΘ.sameKE _ _) (fun _ _ => hΘ.sameEF _ _)
    (fun T₀ T₁ => good3R Θ.A (DecR.wayColl D) (Θ.recK (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁))
      (Θ.recE₀ (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)) (Θ.recE₁ (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁))
      (Θ.recF (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)) (Θ.xOf (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁)))
    (fun _ _ oK oE oF Y₀ Y₁ lK lE lF =>
      ⟨Y₁, hΘ.langK _ _ oK Y₀ lK, hΘ.langE _ _ oE Y₀ Y₁ lE, hΘ.langF _ _ oF Y₁ lF⟩)
    (fun T₀ T₁ g => {w | Θ.ClashB (cutT Θ.S₀ T₀) (Θ.T₁c T₀ T₁) g w.1.2}) (bC (tC + tP)) hX
    (fun k s hs => ⟨(hΘ.apart k s hs).1, fun T₀ => (hΘ.apart k s hs).2 _⟩)
    (fun g => {w | Θ.VerifyB g w.1.1.1.1 w.1.2 = true ∧ ¬ Θ.FineB St g w})
    (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ _ hf => hf)
    (fun w => by
      have e : {g | w ∈ {w : Outcome St | Θ.VerifyB g w.1.1.1.1 w.1.2 = true ∧
          ¬ Θ.FineB St g w} ∧ ¬ False} =
          {g | Θ.VerifyB g w.1.1.1.1 w.1.2 = true ∧ ¬ Θ.FineB St g w} := by
        ext g
        simp
      rw [e]
      exact measurableSet_event hΘ St w)
    (fun g w hy _ => ⟨⟨hy.1, not_fineB_off hΘ _ (Or.inl rfl) St g w hy.2⟩, not_false⟩)
    (fun T₀ g w hy _ => ⟨⟨hy.1, not_fineB_off hΘ _ (Or.inr ⟨_, rfl⟩) St g w hy.2⟩, not_false⟩)
    (fun T₀ T₁ g w hy hx => by
      have hy0 := (Θ.verifyB_iff _ _ _).1 hy.1
      change Θ.Accepts (Θ.pub₀ (Θ.ov T₀ T₁ g)) (Θ.pub₁ (Θ.ov T₀ T₁ g)) (Θ.ov T₀ T₁ g)
        (Θ.ov T₀ T₁ g) w.1.1.1.1 w.1.2 ∨
        Θ.ClashB (Θ.pub₀ (Θ.ov T₀ T₁ g)) (Θ.pub₁ (Θ.ov T₀ T₁ g)) (Θ.ov T₀ T₁ g) w.1.2 at hy0
      rw [Θ.pub₀_ov, Θ.pub₁_ov] at hy0
      have hy1 := hy0.resolve_right fun hc => hx (by
        rw [Θ.ov_eq] at hc
        exact hΘ.deafC _ _ _ _ hc)
      obtain ⟨hI, oK, oE, oF, cK, cE, cF, rK, rE, rF, uK, u0, u1, uF, hx⟩ := hy1
      rw [Θ.ov_eq, hΘ.deafK] at cK
      rw [Θ.ov_eq, hΘ.deafE] at cE
      rw [Θ.ov_eq, hΘ.deafF] at cF
      refine ⟨hI, oK, oE, oF, _, cK, cE, cF, rK, rE, rF, fun hf hc hs hg => ?_⟩
      have t0 : Θ.recE₀ _ _ oE = Θ.recK _ _ oK := Option.some.inj (u0.symm.trans uK)
      have t1 : Θ.recF _ _ oF = Θ.recE₁ _ _ oE := Option.some.inj (uF.symm.trans u1)
      have hg' := goodDecR_of_good3R _ (DecR.wayColl D) _ _ _ _ _ oK oE oF _ t0 t1 hg
      rw [hx] at hg'
      obtain ⟨τ, hτ⟩ := hs
      have hcC : NoClash w.1.1.2 := hc.of_subset fun e he => by
        rw [hτ]
        exact List.mem_append_left _ he
      refine hy.2 ⟨_, _, hf, hΘ.keyOK _ _ _, uK, ?_⟩
      rw [← hΘ.rawTie _ _ w.1.2 _ _ hcC]
      exact hg')
    (eps bK bE bF bC bS tC tP) (fun T₀ T₁ =>
      add_le_add (hΘ.flatK _ _ _) (add_le_add (hΘ.flatE _ _ _)
        (add_le_add (hΘ.flatF _ _ _) le_rfl)))
  refine le_trans (Rom.Pr_mono _ fun g w hw => ?_) h
  exact ⟨hw, not_false⟩

end Three

end Shapes

end OnBytes.Slice
