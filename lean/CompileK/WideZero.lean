-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WideZero.lean: a witness map that reads the encoded index, the oracles and the plain parts,
but no verifier message: lemmas for a witness extractor that looks up no Fiat-Shamir answer.




Statements and proofs.


`Spec.compileWireT_any` of CompileK/WideMain.lean (for a map
with `TrBlind j wit`: it does not read the verifier messages from round j on) has one hypothesis on
the compiled scheme (κ: an accepted proof's chain queries before round j stand in the two traces)
and stands over the typed oracles only. Both limits come from verifier messages. At j = 0 nothing of
the chain is followed.

Main names, each statement under its hypotheses:
  `rhoTo_zero`: the extractor looks up no Fiat-Shamir answer.
  `missLe_zero`: κ = 0: it says none only for a proof without a slot's string, and such a proof the
    verifier rejects.
  `localTo_zero`: under `hl` and `hn` (the leaf and the node oracle answer in one block) it reads
    Merkle entries only, so the passage to one oracle applies (`LocalTo`, Rom/Family.lean).











Limits:
Status beside the compilation of this protocol's technical report (lean/CREDITS.md; a comparison by
reading, of one of its prints, not held against the report's latest edition; that report is
unrefereed): its witness extractor recomputes the witness from the extracted
index and the instance, so this file renders no step of it. Here a
witness is read out of what the prover sent.
This file says nothing for a map that reads a verifier message (a seed, a fold's coefficient):
CompileK/WideMain.lean. The index decoder reads the encoded index alone. A session has at least one
round. What the heads of CompileK/Main.lean and CompileK/GrindMain.lean list as not said is not said
here either.

Terms: lean/GLOSSARY.md.
-/
import CompileK.WideMain
import CompileK.KnowLocal

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Top.Batch Top.ProgDraw Compile.GenMap Compile.GenPub
open Compile.BatchLife (Sims)
open scoped ENNReal

section Zero
variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)

/-- At j = 0 no query is followed. -/
theorem rhoTo_zero (tr : Tc W) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    rhoTo W 0 tr cm x π = some (Rho.dflt _) := by
  unfold rhoTo chainSTo chainTo
  rfl

/-- The verifier rejects a proof without a slot's string. -/
theorem V_piB_none (p : Params) (v : IVK lam L) (x : X) (π : Prf lam L) (h : π.piB = none) :
    V W p v x π = .pure false := by
  unfold V
  split
  · rename_i h3
    rw [h] at h3
    cases h3
  · rfl

/-- At j = 0: the verifier never accepts where the extractor says none. -/
theorem missLe_zero (WP : WireBP L) (p : Params)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) :
    Gen.MissLe (argBKE W WP p) (extractorBKTo W 0 wit) fun _ _ => 0 := by
  intro tC tP St Ct Pt _ _
  refine le_of_eq ?_
  unfold Rom.Pr
  refine (MeasureTheory.lintegral_congr fun f => ?_).trans MeasureTheory.lintegral_zero
  unfold Rom.PrCoins
  refine le_antisymm (le_trans (pr_mono_support _ (F := ∅) ?_) (le_of_eq (pr_empty _))) (zero_le _)
  rintro o ho ⟨hacc, hn⟩
  simp only [Gen.bindingExp, bind_eq, pure_eq, OComp.runEager_bind, OComp.runEager,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at ho
  obtain ⟨a, -, b, -, c, hc, rfl⟩ := ho
  have hn' : ((reK a.1.1.2 (liftK b.1.2)).piB.bind fun πB =>
        (rhoTo W 0 (a.2 ++ b.2) (reK a.1.1.2 (liftK b.1.2)).cm b.1.1 πB).map fun ρ =>
          wit b.1.1 (extEnc W (a.2 ++ b.2) (reK a.1.1.2 (liftK b.1.2)).cm)
            (starB W (a.2 ++ b.2) πB ρ)) = none := hn
  have hpi : (reK a.1.1.2 (liftK b.1.2)).piB = none := by
    cases hq : (reK a.1.1.2 (liftK b.1.2)).piB with
    | none => rfl
    | some πB =>
      rw [hq] at hn'
      simp only [Option.bind_some, rhoTo_zero, Option.map_some] at hn'
      cases hn'
  have hV : (Gen.withW (Option Wn) (argBKE W WP p)).V a.1.1 b.1.1 b.1.2 = Rom.OComp.pure false :=
    V_piB_none W p a.1.1.1 b.1.1 _ hpi
  rw [hV] at hc
  simp only [Rom.OComp.runEager, PMF.mem_support_pure_iff] at hc
  subst hc
  cases hacc

theorem starB_single (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Tc W) (π : OneProtocolProof lam L.onlineBatch) (ρ : Rho L.onlineBatch.loc.shape) :
    starB W (single m tr) π ρ = starB W tr π ρ :=
  trStar_congr _ _ _ _ _ _ _ fun c _ d j => extLeaf_single m hl hn tr d c j

/-- Under `hl` and `hn`, at j = 0 the extractor reads entries at one-block oracles only. -/
theorem localTo_zero (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (w0 : Wn)
    (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) :
    LocalTo (Gen.totalE w0 (extractorBKTo W 0 wit)) m := by
  refine ⟨fun v tr => ?_, fun v trC x π trP => ?_⟩
  · show L.decodeIndex (extEnc W tr v.1.cm) = L.decodeIndex (extEnc W (single m tr) v.1.cm)
    rw [extEnc_single W m hl hn]
  · show ((reK v.2 (liftK π)).piB.bind fun πB =>
        (rhoTo W 0 (trC ++ trP) (reK v.2 (liftK π)).cm x πB).map fun ρ =>
          wit x (extEnc W (trC ++ trP) (reK v.2 (liftK π)).cm)
            (starB W (trC ++ trP) πB ρ)).getD w0 =
      ((reK v.2 (liftK π)).piB.bind fun πB =>
        (rhoTo W 0 (single m trC ++ single m trP) (reK v.2 (liftK π)).cm x πB).map fun ρ =>
          wit x (extEnc W (single m trC ++ single m trP) (reK v.2 (liftK π)).cm)
            (starB W (single m trC ++ single m trP) πB ρ)).getD w0
    simp only [rhoTo_zero, ← single_append, extEnc_single W m hl hn, starB_single W m hl hn]

end Zero

end Compile.Batch
