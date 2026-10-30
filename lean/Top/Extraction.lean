-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/Extraction.lean: the step to one random oracle for the optional requirement of
  ZKCP/Optional.lean (`ZKCP.HasExtractionError`). (Terms: lean/GLOSSARY.md.)
  The requirement guards against an extractor that satisfies index binding for a trivial reason.
    `extraction_overOne`     If the extractor is `LocalTo` m, the probability that it misses the
                             honest committer's index is the same over the one random oracle, by
                             `overOne m`, and over the typed oracles.

  Limits: No statement here is a security level.
-/
import Rom.ExitPriv
import Iop.WireOf
import Iop.PullProofs
import Code.FieldEnum
import ZKCP.Defs
import Mathlib.Data.Matrix.Mul
import Code.RS
import Code.Field
import Iop.Univ
import Blocks.Opens
import Blocks.Numbering
import Blocks.LowerKit
import Blocks.SerS
import Iop.WireOK
import Blocks.Small
import Blocks.Leaves
import Compile.Extraction
import Compile.GlueBinding
import ZKCP.Optional
import Blocks.ErrSup
import Blocks.LevelAcc
import Blocks.LevelLocal
import Blocks.LevelSound
import Blocks.LinkHVZK_rs
import Blocks.LinkSound
import Blocks.Reads
import Compile.CompleteStrict
import Compile.CompleteUnif
import Compile.GluePrivacy
import Compile.LifeStar
import Compile.Local
import Iop.RbrLast
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin.Basic
import ZKCP.Special
import Compile.DisciplineWorld
import Compile.Step1_defc_Prob
import Compile.Step1_life2_Erase
import Prob.Tail
import Rom.Forget
import Rom.HopCost
import Rom.UpToBad

noncomputable section

namespace Top
open Iop Rom Compile Prob MeasureTheory
open scoped ENNReal

namespace Extr

variable {S : OSpec} {lam : ℕ} {α : Type}

/-- The trace of querying the one oracle at n strings. -/
def trAll (g : Fam (rom lam)) (n : ℕ) (pts : Fin n → List Bool) : Trace (rom lam) :=
  List.ofFn fun j => (⟨(), pts j, g () (pts j)⟩ : QA (rom lam))

theorem withTrace_askAll (g : Fam (rom lam)) : ∀ (n : ℕ) (pts : Fin n → List Bool),
    (askAll lam n pts).withTrace.runEager g = PMF.pure (fun j => g () (pts j), trAll g n pts)
  | 0, _ => by
    simp only [askAll, OComp.withTrace, OComp.runEager, trAll, List.ofFn_zero]
    congr 2; funext j; exact j.elim0
  | n + 1, pts => by
    simp only [askAll, OComp.withTrace, OComp.runEager, withTrace_bind, OComp.runEager_bind,
      withTrace_askAll g n, trAll, List.ofFn_succ, PMF.bind_bind]
    refine (PMF.pure_bind _ _).trans ((PMF.pure_bind _ _).trans ((PMF.pure_bind _ _).trans ?_))
    simp only [List.append_nil]
    congr 2; funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- What `singleTr` makes of one entry, as a function of the typed query and block that its string
encodes, and of the answer. -/
def one (m : OracleCoding S lam) (pt : m.Pt) (r : Fin lam → Bool) : Option (QA S) :=
  if m.blocks pt.1 = 1 then some ⟨pt.1, pt.2.1, (m.rng pt.1).symm fun _ => r⟩ else none

theorem singleTr_eq (m : OracleCoding S lam) (tr : Trace (rom lam)) :
    singleTr m tr = tr.filterMap fun e => one m (m.dec e.2.1) e.2.2 := rfl

theorem singleTr_append (m : OracleCoding S lam) (a b : Trace (rom lam)) :
    singleTr m (a ++ b) = singleTr m a ++ singleTr m b := by
  simp only [singleTr, List.filterMap_append]

/-- The blocks of one typed answer: if there is one block, the entry over the typed oracles;
otherwise nothing. -/
theorem singleTr_trAll (m : OracleCoding S lam) (g : Fam (rom lam)) (o : S.ι) (q : S.Dom o) :
    singleTr m (trAll g (m.blocks o) (m.code o q)) = single m [⟨o, q, readBlocks m g o q⟩] := by
  have h1 : singleTr m (trAll g (m.blocks o) (m.code o q))
      = (List.finRange (m.blocks o)).filterMap fun j => one m ⟨o, q, j⟩ (g () (m.code o q j)) := by
    rw [singleTr_eq, trAll, List.ofFn_eq_map, List.filterMap_map]
    refine List.filterMap_congr fun j _ => ?_
    simp only [Function.comp_apply, m.dec_code]
  rw [h1]
  by_cases hb : m.blocks o = 1
  · have hsub : Subsingleton (Fin (m.blocks o)) := by rw [hb]; infer_instance
    have h2 : ∀ j : Fin (m.blocks o),
        one m ⟨o, q, j⟩ (g () (m.code o q j)) = some ⟨o, q, readBlocks m g o q⟩ := fun j => by
      simp only [one, hb, if_true]
      congr 4
      funext j'
      rw [Subsingleton.elim j' j]
      rfl
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1
      (show (List.finRange (m.blocks o)).length = 1 by rw [List.length_finRange, hb])
    simp [ha, h2, single, hb]
  · have h2 : ∀ j : Fin (m.blocks o), one m ⟨o, q, j⟩ (g () (m.code o q j)) = none := fun j => by
      simp only [one, hb, if_false]
    simp [h2, single, hb]

theorem single_cons (m : OracleCoding S lam) (e : QA S) (tr : Trace S) :
    single m (e :: tr) = single m [e] ++ single m tr := by
  simp only [single, ← List.filter_append, List.singleton_append]

/-- The one-block entries of the trace over the one oracle are those of the trace over the typed
oracles. -/
theorem withTrace_overOne (m : OracleCoding S lam) (g : Fam (rom lam)) (c : OComp S α) :
    ((c.overOne m).withTrace.runEager g).map (fun o => (o.1, singleTr m o.2))
      = (c.withTrace.runEager (readBlocks m g)).map fun o => (o.1, single m o.2) := by
  induction c with
  | pure a => simp [OComp.overOne, OComp.withTrace, OComp.runEager, PMF.pure_map, singleTr, single]
  | sample n k ih => simp only [OComp.overOne, OComp.withTrace, OComp.runEager, PMF.map_bind, ih]
  | query o q k ih =>
    have hL : (((OComp.query o q k).overOne m).withTrace.runEager g).map
          (fun x => (x.1, singleTr m x.2)) =
        ((((k (readBlocks m g o q)).overOne m).withTrace.runEager g).map fun x =>
            (x.1, singleTr m x.2)).map
          fun y => (y.1, single m [⟨o, q, readBlocks m g o q⟩] ++ y.2) := by
      simp only [OComp.overOne, withTrace_bind, OComp.runEager_bind, withTrace_askAll,
        OComp.runEager, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind]
      refine (PMF.pure_bind _ _).trans (congrArg _ (funext fun x => ?_))
      rw [PMF.pure_bind, PMF.pure_bind, singleTr_append, singleTr_trAll]
    have hR : ((OComp.query o q k).withTrace.runEager (readBlocks m g)).map
          (fun x => (x.1, single m x.2)) =
        (((k (readBlocks m g o q)).withTrace.runEager (readBlocks m g)).map fun x =>
            (x.1, single m x.2)).map
          fun y => (y.1, single m [⟨o, q, readBlocks m g o q⟩] ++ y.2) := by
      simp only [OComp.withTrace, OComp.runEager, OComp.runEager_bind, ← PMF.bind_pure_comp,
        Function.comp_def, PMF.bind_bind]
      refine congrArg _ (funext fun x => ?_)
      rw [PMF.pure_bind, PMF.pure_bind, single_cons]
    rw [hL, hR, ih]

end Extr

variable {I X : Type} {lam : ℕ}

/-- Under `LocalTo` (the extractor reads only oracles whose answer is one hash block), the
extraction error over the one oracle equals that over the typed oracles. -/
theorem extraction_overOne {S : OSpec} {I X W IVK ISK Pf : Type} (m : OracleCoding S lam)
    (A : ZKCP.Gen.Arg S I X W IVK ISK Pf) (E : ZKCP.Gen.Extractor S I X W IVK Pf)
    (hE : LocalTo E m) (i : I) :
    Rom.Pr ((A.C i).overOne m).withTrace (fun _ => {o | (extractorOverOneHashFunction m E).Ei o.1.1 o.2 ≠ some i}) =
      Rom.Pr (A.C i).withTrace (fun _ => {o | E.Ei o.1.1 o.2 ≠ some i}) := by
  have h1 : ∀ g : Fam (rom lam),
      PrCoins g ((A.C i).overOne m).withTrace {o | (extractorOverOneHashFunction m E).Ei o.1.1 o.2 ≠ some i} =
        PrCoins (readBlocks m g) (A.C i).withTrace {o | E.Ei o.1.1 o.2 ≠ some i} := fun g => by
    have e1 : {o : (IVK × ISK) × Trace (rom lam) | (extractorOverOneHashFunction m E).Ei o.1.1 o.2 ≠ some i} =
        (fun o => (o.1, singleTr m o.2))
          ⁻¹' {y : (IVK × ISK) × Trace S | E.Ei y.1.1 y.2 ≠ some i} := rfl
    have e2 : {o : (IVK × ISK) × Trace S | E.Ei o.1.1 o.2 ≠ some i} = (fun o => (o.1, single m o.2))
        ⁻¹' {y : (IVK × ISK) × Trace S | E.Ei y.1.1 y.2 ≠ some i} := by
      ext o
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ← hE.1]
    unfold PrCoins
    rw [e1, ← pr_map, Extr.withTrace_overOne, pr_map, ← e2]
  unfold Rom.Pr
  simp only [h1]
  rw [← U_map_readBlocks m, lintegral_map (measurable_PrCoins _ _) (measurable_readBlocks m)]

end Top
