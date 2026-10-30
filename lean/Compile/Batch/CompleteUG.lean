-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUG.lean: completeness of the compiled scheme with free empty slots (no query
for an empty slot: `proveBU`, Compile/Batch/ProverU.lean) whose rounds may have proof-of-work bits
(`Spec.completeBatchUGr`, Compile/Batch/SpecUGr.lean), from seven hypotheses:
`Spec.acceptsHonestBUG`, `lawTUG`, `lawLUG`, `lawBUG`, `unifTG`, `unifLG`, `unifBUG` (words of this
library: lean/GLOSSARY.md).

    theorem completeOfUG : Spec.completeOfUG (Compile/Batch/SpecCompleteUG.lean)

The honest run is the instrumented run (`runAllBUX`, Compile/Batch/StarUX.lean) with the further
output forgotten (`runAllBU_eq`: an equation of programs). For fixed oracle functions, V rejects
some request only if the instrumented run is bad: Test, the Link of the sampled copy, or the slot of
some request (`PrCoins_leUX`, from `Spec.acceptsHonestBUG` and the lemma's further hypotheses; bad,
`Ref.badAt`: the proof string is `none`, or a search over nonces has failed). Each of these events
has, for every fixed family, the distribution of a small experiment (the hypotheses `lawTUG`,
`lawLUG`, `lawBUG`); so it has that experiment's probability under lazily sampled oracles
(`pr_law_eqUX`). A union bound gives `alphaBG W M`: the sum of pT + pL + maxBatchSize pO and of the
probabilities of the failed searches (those of Batch maxBatchSize times).

Notation: `L`: an `BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with
the honest sides; `W`: a `QueryLayout lam L` (Iop/BatchWire.lean): a wire record (lean/GLOSSARY.md: wire);
`WP`: a `WireBP L` (Iop/BatchWireP.lean): the prover's data for the three protocols, and the
enumeration of the encoding randomness; `p`: a `Params` (Compile/Star.lean), with the fields sMT,
sFS, M, s1; the number of copies is `p.M` + 1; `M`: an `LH.Nums` (Iop/InteractiveOracleProof.lean): all numbers of
the interface; `Ryes`, `Rno`: `I → X → Prop`: the two indexed relations of a `Gen.RelPair`
(ZKCP/Gen.lean), by `relPair` (Compile/Spec.lean); `b`: a `List (X × Unit)`: a batch, as P of a
`Gen.Arg S I X W ..` (ZKCP/Gen.lean) takes it: a `List (X × W)`, here with W = `Unit`; `pT`, `pL`,
`pO`: fields of `M`, in ℝ≥0∞; `L.maxBatchSize`: a natural number: the number of slots (`BatchProtocol`, Iop/Batch.lean);
`cFail` (Compile/Batch/SpecGrind.lean): in ℝ≥0∞: the sum, over the rounds of one slot's transcript,
of the probability that the round's search fails; a copy: C encodes the index once (the first
encoding) and `p.M` + 1 more times (the copies) (the head of Compile/Batch/Star.lean); `W.OKG`
(`QueryLayout.OKG`, Iop/BatchWire.lean): the laws of a wire whose rounds may have tests; `GrFitB W Ryes`
(Compile/Batch/SpecFit.lean): `GrFit` for the three protocols of a record of protocols; `Fmt`
(`RoundSplits.Fmt`, Iop/BatchFmt.lean): a proposition: every round has a format, and an unsent component is
empty.

Limits: it proves none of its seven hypotheses (Compile/Batch/CompleteUMainG.lean puts them in).
-/
import Compile.Batch.SpecCompleteUG
import Compile.Batch.CompleteU

noncomputable section

namespace Compile.Batch
open Iop Rom Prob MeasureTheory RefU
open scoped ENNReal

namespace CompleteBUG

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (f : Fam (spec lam W.K L)) (i : I) (b : List (X × Unit))

/-- The honest run is the instrumented run with the further output forgotten. -/
theorem runAllBU_eq :
    runAllBU W WP p i b = (runAllBUX W WP p i b).bind fun z => OComp.pure z.1 := by
  unfold runAllBU runAllBUX
  rw [C_eq]
  simp only [PU_eq, OComp.bind_assoc]
  rfl

/-- the completeness experiment, for fixed oracle functions, in terms of the instrumented run -/
theorem runEager_completenessExpUX :
    (ZKCP.Gen.completenessExp (argBU W WP p) i b).runEager f =
      ((runAllBUX W WP p i b).runEager f).bind fun z =>
        (ZKCP.Gen.verifyAll (argBU W WP p) z.1.1 ((b.map Prod.fst).zip z.1.2)).runEager f := by
  rw [CompleteBU.runEager_completenessExp, runAllBU_eq, OComp.runEager_bind, PMF.bind_bind]
  refine congrArg _ (funext fun z => ?_)
  show (PMF.pure z.1).bind _ = _
  rw [PMF.pure_bind]

/-- the instrumented run is bad: Test, the Link of the sampled copy, or the slot of some request -/
def BadUX (hlen : b.length ≤ L.maxBatchSize) : Set ((IVK lam L × List (Prf lam L)) × RunX lam W.K L) :=
  {z | z.2.badT WP = true} ∪ {z | z.2.badL WP = true} ∪
    {z | ∃ a : Fin b.length, z.2.badB WP ⟨a.val, lt_of_lt_of_le a.isLt hlen⟩ (b[a.val]).1 = true}

variable {Ryes Rno : I → X → Prop} {M : LH.Nums}

/-- For fixed oracle functions, under the hypotheses below: V rejects some request only if the
instrumented run is bad. -/
theorem PrCoins_leUX (hAcc : Spec.acceptsHonestBUG)
    (hL : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitB W Ryes)
    (hF : L.onlineBatch.ann.Fmt) (hlen : b.length ≤ L.maxBatchSize) (hyes : ∀ xw ∈ b, Ryes i xw.1) :
    PrCoins f (ZKCP.Gen.completenessExp (argBU W WP p) i b) {c | c = false} ≤
      PrCoins f (runAllBUX W WP p i b) (BadUX W WP b hlen) := by
  unfold PrCoins
  rw [runEager_completenessExpUX]
  refine le_trans (pr_bind_le_add _ _ _ (BadUX W WP b hlen) (ε := 0) fun z hz hn => ?_)
    (le_of_eq (add_zero _))
  have hall : ∀ xp ∈ (b.map Prod.fst).zip z.1.2,
      (V W p z.1.1 xp.1 xp.2).runEager f = PMF.pure true := by
    rintro ⟨x, π⟩ hxp
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hxp
    obtain ⟨ha1, ha2⟩ := List.getElem?_zip_eq_some.mp ha
    have halt : a < b.length := by
      have := (List.getElem?_eq_some_iff.mp ha1).1
      simpa using this
    have hx : x = (b[a]).1 := by
      rw [List.getElem?_map, List.getElem?_eq_getElem halt] at ha1
      exact (Option.some.inj ha1).symm
    refine hAcc I X lam L W WP p Ryes Rno M hL hW hG hF f i b hyes z hz
      ⟨a, lt_of_lt_of_le halt hlen⟩ x π ha1 ha2 ?_ ?_ ?_
    · exact Bool.eq_false_iff.2 fun h => hn (Or.inl (Or.inl h))
    · exact Bool.eq_false_iff.2 fun h => hn (Or.inl (Or.inr h))
    · exact Bool.eq_false_iff.2 fun h => hn (Or.inr ⟨⟨a, halt⟩, by rw [← hx]; exact h⟩)
  rw [CompleteBU.verifyAll_true W WP p f z.1.1 _ hall, pr_pure]
  simp

/-- An event of the instrumented run that has, for every fixed family, the distribution of a small
experiment c, has under lazy oracles the probability that c outputs true. -/
theorem pr_law_eqUX {c : TypedOracleComputation lam W.K L Bool}
    (φ : (IVK lam L × List (Prf lam L)) × RunX lam W.K L → Bool)
    (h : ∀ f, ((runAllBUX W WP p i b).runEager f).map φ = c.runEager f) :
    pr (runAllBUX W WP p i b).law {z | φ z = true} = pr c.law {x | x = true} := by
  have h1 := Rom.map_runLazy_congr
    (c₁ := runAllBUX W WP p i b) (c₂ := c) φ id (fun f => by rw [h f, PMF.map_id]) (Table.empty _)
  have h2 : (runAllBUX W WP p i b).law.map φ = c.law := by
    unfold OComp.law
    rw [PMF.map_comp]
    exact h1
  rw [← h2, pr_map]
  rfl

end CompleteBUG

open CompleteBUG in
/-- From its seven hypotheses: `Spec.completeBatchUGr`. -/
theorem completeOfUG : Spec.completeOfUG := by
  intro hAcc hT hLk hB uT uL uB I X lam L W WP p Ryes Rno M hL hW hG hWP hF i b hb
  obtain ⟨hlen, hyes⟩ := hb
  have hyes' : ∀ xw ∈ b, Ryes i xw.1 := hyes
  have h1 : Rom.Pr (ZKCP.Gen.completenessExp (argBU W WP p) i b) (fun _ => {c | c = false}) ≤
      pr (runAllBUX W WP p i b).law (BadUX W WP b hlen) := by
    rw [← Pr_eq_law]
    exact lintegral_mono fun f => PrCoins_leUX W WP p f i b hAcc hL hW hG hF hlen hyes'
  refine h1.trans ?_
  have hBs : pr (runAllBUX W WP p i b).law
        {z | ∃ a : Fin b.length,
          z.2.badB WP ⟨a.val, lt_of_lt_of_le a.isLt hlen⟩ (b[a.val]).1 = true} ≤
      L.maxBatchSize * (M.pO + cFail L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh) := by
    refine (pr_exists_le_mul _ _
      (M.pO + cFail L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh) fun a => ?_).trans ?_
    · have hx : (b.map Prod.fst)[a.val]? = some (b[a.val]).1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem a.isLt]
        rfl
      have e := pr_law_eqUX W WP p i b
        (c := RBU W WP p i (b.map Prod.fst) ⟨a.val, lt_of_lt_of_le a.isLt hlen⟩ (b[a.val]).1)
        (fun z : (IVK lam L × List (Prf lam L)) × RunX lam W.K L =>
          z.2.badB WP ⟨a.val, lt_of_lt_of_le a.isLt hlen⟩ (b[a.val]).1)
        (fun f =>
          hB I X lam L W WP p hW hF f i b ⟨a.val, lt_of_lt_of_le a.isLt hlen⟩ (b[a.val]).1 hx)
      exact (le_of_eq e).trans
        (uB I X lam L W WP p Ryes Rno M hL hW hG hWP hF i (b.map Prod.fst)
          ⟨a.val, lt_of_lt_of_le a.isLt hlen⟩ (b[a.val]).1 hx (hyes' _ (List.getElem_mem a.isLt)))
    · rw [Fintype.card_fin]
      gcongr
  have hTs : pr (runAllBUX W WP p i b).law {z | z.2.badT WP = true} ≤
      M.pT + cFail L.offline.shape _ W.T.sh := by
    have e := pr_law_eqUX W WP p i b (c := Ref.RT W WP p i)
      (fun z : (IVK lam L × List (Prf lam L)) × RunX lam W.K L => z.2.badT WP)
      (fun f => hT I X lam L W WP p f i b)
    exact (le_of_eq e).trans (uT I X lam L W WP p Ryes Rno M hL hW hG hWP i)
  have hLs : pr (runAllBUX W WP p i b).law {z | z.2.badL WP = true} ≤
      M.pL + cFail L.link.shape _ W.Lk.sh := by
    have e := pr_law_eqUX W WP p i b (c := Ref.RL W WP p i)
      (fun z : (IVK lam L × List (Prf lam L)) × RunX lam W.K L => z.2.badL WP)
      (fun f => hLk I X lam L W WP p f i b)
    exact (le_of_eq e).trans (uL I X lam L W WP p Ryes Rno M hL hW hG hWP i)
  refine ((pr_union_le _ _ _).trans
      (add_le_add ((pr_union_le _ _ _).trans (add_le_add hTs hLs)) hBs)).trans (le_of_eq ?_)
  unfold alphaBG alphaB
  rw [mul_add]
  ring

end Compile.Batch
