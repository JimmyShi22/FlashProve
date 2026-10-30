-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Rules.lean: A TREE AND THE CHAIN OF A COMPILED RUN, AS TOKEN PROGRAMS, KEEP THE
RULES OF DEFERRED PROGRAMMING: the two statements with the clauses on the rules and the counts
alone, out of this folder's lemmas.

General statements. This file states no goal of the release. The token programs are a device of one
step of a proof of index privacy and stand in no statement on the scheme.

The lemmas of this folder on a tree (safe_treeT, Johnson/TokenRel/Trees.lean) and on the chain
(safe_chainT, Johnson/TokenRel/Chain.lean) say what the rules ask and what the rule of release asks.
The files that put the scheme's programs together for the rules and the counts
(Johnson/TokenRules/EndC.lean, Table.lean, Scheme.lean) want the first alone:
  Spec.safeTree, safeTree     one tree.
  Spec.safeChain, safeChain   THE CHAIN, from every round and phase.

-/
import Johnson.TokenRel.Chain

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

namespace Spec

/-- **One tree**: its evaluations hold of the old tokens only us and are charged to new ones; they
go to the leaf oracle alone; its tokens are new and can be shown together with us. -/
def safeTree : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop)
      (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (dp : ℕ) (body : ℕ → Body L)
      (d : DSt (typedOracleFamily lam K L)),
    bl ≤ ℓ → TidyO (rulesT K L lam bl bf sd) d → (∀ u ∈ us, u < d.vals.length) →
    SafeO (rulesT K L lam bl bf sd) (treeT (K := K) ℓ us pre dp body) d fun T d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO noTok (fun u => u ∈ us) noTok (cnt1 OracleName.node (2 ^ dp)) (cnt1 OracleName.leaf (2 ^ dp)) d d' ∧
      KeepsFree (fun o => o = OracleName.leaf) d d' ∧ TreeOKT d' us T ∧ TreeNewT d.vals.length T

/-- **The chain**, from every round and phase: it keeps the rules; of the old tokens its evaluations
hold the first salt and the phase's tokens alone; it shows nothing; it stays within the counts; and
if it has a value, ChainEnd holds. -/
def safeChain : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop)
      (t : Tag) (cms : List (Dig lam)) (x : Option X) (ℓ : ℕ) (pre : ℕ → Bool → Bits → Bits)
      (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) (sFS : ℕ)
      (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ : Strat s Unit)
      (V : List Tok) (n : ℕ) (d : DSt (typedOracleFamily lam K L)),
    bl ≤ ℓ → bf ≤ sFS → bf ≤ lam → n ≤ d.vals.length →
    TidyO (rulesT K L lam bl bf sd) d → CI d t salt sFS V ph →
    SafeO (rulesT K L lam bl bf sd) (chainT t cms x ℓ pre salt cd cap s A W embS embP i ph σ) d
      fun r d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (PhTok salt ph) (PhTok salt ph) noTok (eRun s A W)
        (mChain t s A W cap cd.path.length i ph) d d' ∧
      ∀ z, r = Res.ok z → ChainEnd n d' salt V z

end Spec


theorem safeTree : Spec.safeTree := by
  intro I X lam K L bl bf sd ℓ us pre dp body d hbl hd hus
  exact SafeO.mono (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩) _ d
    (safe_treeT hbl us pre dp body hd hus)

/-- **The chain keeps the rules.** -/
theorem safeChain : Spec.safeChain := by
  intro I X lam K L bl bf sd t cms x ℓ pre salt cd cap sFS s A W embS embP i ph σ V n d hbl hbS hbL
    hn hd hci
  exact SafeO.mono (fun _ _ h => ⟨h.1, h.2.1, fun z hz => (h.2.2.2 z hz).1⟩) _ d
    (safe_chainT t cms x ℓ pre salt cd cap sFS _ hbl hbS hbL s A W embS embP i ph σ V n d hn hd hci
      rfl)

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.safeTree
#print axioms OnBytes.TokenRel.safeChain
