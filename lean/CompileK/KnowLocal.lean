-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowLocal.lean: the named witness extractor reads entries at one-block oracles only, if
the leaf and the node oracle answer in one block.

Statement and proof. Terms (lean/GLOSSARY.md): link, typed oracle.
A coding (`OracleCoding`, Rom/Family.lean) splits each typed oracle's answers into blocks of λ bits. A named
extractor is one that a statement gives as a term (`HasIndexBindingWith`, ZKCP/Gen.lean).

Why: the passage from the compiler's family of typed oracles to one oracle {0,1}* → {0,1}^λ
(`IsZKCPArgWith.overOne`, Rom/Carry.lean) asks of a named extractor that its two parts depend on
their traces only through the entries at oracles whose answer is one block (`LocalTo`,
Rom/Family.lean; that file says why the passage is false without it). For the extractors without
witnesses the second part is constant, so only the index extractor has to be looked at
(`extractorB_local`, Compile/Batch/GlueBinding.lean). Here the second part reads the committer's
trace followed by the prover's.
Why `readStar_single`: the oracles under given roots are read through the Merkle extractor for
leaves, which looks at the leaf and node oracles only.

Main names:
  `Spec.knowLocal`: the title's statement, for every witness map "wit" and every default value, as
    `LocalTo` of `extractorBKW` (CompileK/KnowExt.lean).

Limits: this file says nothing on what the extracted witness is good for
(CompileK/KnowBinding.lean), and nothing on codings in which a Merkle oracle has several blocks.
-/
import CompileK.KnowExt
import Compile.Batch.Local

set_option autoImplicit false

namespace Rom

/-- The one-block entries of a trace followed by another. -/
theorem single_append {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) (a b : Trace S) :
    single m (a ++ b) = single m a ++ single m b :=
  List.filter_append a b

end Rom

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap Compile.GenPub

section Generic
variable {S : OSpec} {I X Wn IVK ISK Pf Pf' Λ : Type} {lam : ℕ}

/-- Locality (`LocalTo`) is preserved when a proof is read through a map. -/
theorem localTo_pullE {E : Gen.Extractor S I X Wn IVK Pf} {m : OracleCoding S lam}
    (σ : Pf' → Pf) (h : LocalTo E m) : LocalTo (pullE σ E) m :=
  ⟨h.1, fun v tr x π tr' => h.2 v tr x (σ π) tr'⟩

/-- Locality is preserved when a published datum is in the key. -/
theorem localTo_pubE {E : Gen.Extractor S I X Wn IVK Pf} {m : OracleCoding S lam}
    (u : Pub IVK ISK Pf Λ) (h : LocalTo E m) : LocalTo (pubE u E) m :=
  ⟨fun v tr => h.1 v.1 tr, fun v tr x π tr' => h.2 v.1 tr x (u.re v.2 π) tr'⟩

end Generic

variable {I X Wn : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- Under `hl` and `hn`, the oracles under given roots are read from one-block entries. -/
theorem readStar_single (m : OracleCoding (spec lam K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Trace (spec lam K L)) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s)
        (pls : Plains s) (p : OPos s),
      readStar (single m tr) s A ws prjS rts pls p = readStar tr s A ws prjS rts pls p
  | [], _, _, _, _, _, p => nomatch p
  | _ :: _, (_, _), (w, _), prjS, (rt, _), (pl, _), .inl p => by
      show Round.rd _ (msgStar (single m tr) w (fun p => prjS (.inl p)) rt pl).1 p =
        Round.rd _ (msgStar tr w (fun p => prjS (.inl p)) rt pl).1 p
      rw [msgStar_congr w _ pl fun c _ d j => extLeaf_single m hl hn tr d c j]
  | _ :: s, (_, A), (_, ws), prjS, (_, rts), (_, pls), .inr p =>
    readStar_single m hl hn tr s A ws (fun p => prjS (.inr p)) rts pls p

/-- The same, under `hl` and `hn`, for the oracles of a slot's local transcript. -/
theorem readB_single (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Tc W) (π : OneProtocolProof lam L.onlineBatch) :
    readB W (single m tr) π = readB W tr π :=
  funext fun p => readStar_single m hl hn tr _ _ _ _ _ _ p

/-- Under `hl` and `hn`, the extractor of the scheme with the links in the proofs has `LocalTo`. -/
theorem extractorBW_local (W : QueryLayout lam L) (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (w0 : Wn)
    (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) :
    LocalTo (extractorBW W wit w0) m := by
  refine ⟨fun v tr => ?_, fun v trC x π trP => ?_⟩
  · show L.decodeIndex (extEnc W tr v.cm) = L.decodeIndex (extEnc W (single m tr) v.cm)
    rw [extEnc_single W m hl hn]
  · show (match π.piB with | some πB => wit x (readB W (trC ++ trP) πB) | none => w0) =
      (match π.piB with | some πB => wit x (readB W (single m trC ++ single m trP) πB) | none => w0)
    cases π.piB with
    | none => rfl
    | some πB =>
      show wit x (readB W (trC ++ trP) πB) = wit x (readB W (single m trC ++ single m trP) πB)
      rw [← single_append, readB_single W m hl hn]

namespace Spec

/-- States: under the hypotheses below, the named extractor of the scheme with the links in the key
reads entries at one-block oracles only. -/
def knowLocal : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (w0 : Wn) (m : OracleCoding (spec lam W.K L) lam),
    m.blocks OracleName.leaf = 1 → m.blocks OracleName.node = 1 → LocalTo (extractorBKW W wit w0) m

end Spec

theorem knowLocal : Spec.knowLocal := fun _ _ _ _ _ W wit w0 m hl hn =>
  localTo_pullE liftK (localTo_pubE pubK (extractorBW_local W wit w0 m hl hn))

end Compile.Batch
