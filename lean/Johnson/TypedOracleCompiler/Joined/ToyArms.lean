-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/ToyArms.lean: a test of `three_arms` (Johnson/TypedOracleCompiler/RecCompile/ThreeArms.lean).
`three_arms` is one bound for three checks run in one experiment, one each for the key file, the
entry file and the proof file; each check is the test of a record's seed (for the entry file: of
both records' seeds) followed by the compiled verifier of that file's protocol. Here every
hypothesis of it but the two bounds on the committer's and the prover's queries (hC, hP) is proved,
at one small interface with records, one wire record (`WR`) and one coding, and the theorem is
applied with these two alone left (`toy_three_arms`). Three controls: each bundle of conditions on
the wire record fails at `WR` spoilt in one field.

A test of a theorem's premises. Nothing on any program.


The interface, the wire records and most laws are those of Johnson/TypedOracleCompiler/Joined/ToyVC.lean: a key's
file and a proof's file of three joined hash chains each; the index is one bit; a record is a seed
of one bit and an answer.

Limits: those of Johnson/TypedOracleCompiler/Joined/ToyVC.lean's head, all of them. A test of one thing alone: that
the premises of `three_arms` can be met together. IT SHOWS NOTHING ON THE NUMBER: hash values have
one bit, so each of the three terms of the bound is at least 1 (`one_le_term`). Met emptily: the
link has no round; there is no external string, so the clauses on where a word's positions lie in a
tree speak of no position; all errors of the two files are 0; every type of witnesses is Unit. One
coding stands for all three, so that the codings agree on the trees says nothing here. The coding is
not the programs'. The three checks are the lax ones (`armTL`, `armL`, `armBL`): the strict ones are
not applied here. It is not shown that any of the three checks accepts anything.

Terms: lean/GLOSSARY.md.
-/
import Johnson.TypedOracleCompiler.Joined.ToyVC
import Johnson.TypedOracleCompiler.RecCompile.ThreeArms
import Johnson.Top.Toy.CompilerSoundnessConditionsAtSmallExample

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open scoped ENNReal

/-! ## The wires: the three checks' conditions at one wire record -/

theorem okta : OKTA WR :=
  ⟨okc.T, we1_ok, wr_okg.prjE_emb, wr_okg.prjT_emb, rfl, wr_okg.extT⟩

theorem okla : OKLA WR :=
  ⟨okc.Lk, we1_ok, wr_okg.prjE_emb, wr_okg.prjL_emb, rfl, wr_okg.extL⟩

theorem okba : OKBA WR :=
  ⟨okc.B, we1_ok, wr_okg.prjE_emb, wr_okg.prjB_emb, rfl, wr_okg.extB, wr_okg.slots⟩

/-! ### controls: each of the three bundles fails at a wire record that is spoilt in one field -/

/-- `WR`, but a symbol of Test is never read back from a leaf -/
def WRnoT : QueryLayout 1 (typedOracleCarrier LR Bd0 G.ann PUnit.unit) := { WR with prjT := fun _ _ => none }

theorem not_okta : ¬ OKTA WRnoT := fun h => by
  have h1 := h.prjT_emb (pos₁ 0) (show OSym G.sh (pos₁ 0) from false)
  cases h1

/-- `WR`, but the tree over an encoded index has another depth than the wires say. The field is
common to the three bundles: all three fail here, not Link's alone. At a link without a round and
without an external string no clause of Link's own can fail; Johnson/TypedOracleCompiler/Joined/ToyArmsExt.lean has
such a control. -/
def WRdeep : QueryLayout 1 (typedOracleCarrier LR Bd0 G.ann PUnit.unit) := { WR with depth := 1 }

theorem not_okla : ¬ OKLA WRdeep := fun h => absurd h.extDepth (by decide)

/-- `WR`, but the request tree has one leaf for the two slots -/
def WRflat : QueryLayout 1 (typedOracleCarrier LR Bd0 G.ann PUnit.unit) := { WR with depthReq := 0 }

theorem not_okba : ¬ OKBA WRflat := fun h => absurd h.slots (by decide)

/-! ## The answers' code -/

/-- an answer is written as one digest -/
def cA3 : LR.OutOfDomainAnswer → List (Dig 1) := fun b => [fun _ => b]

theorem ansOK3 : AnsOK (L := LR) cA3 :=
  ⟨fun _ _ h => congrFun (List.cons.inj h).1 0, fun _ _ => rfl⟩

/-! ## The three protocols -/

theorem soundAt : LR.SoundAtR Rn (fun _ _ _ => ()) 1 CT.err () (CB.errN LR.maxBatchSize) :=
  soundAtR_of_files_late LR DT DB (CT := CT) (CB := CB) Rn (fun _ _ _ => ()) 1 () rfl rfl 1 rfl
    noneColl rcd sndL knowsT decidesT tieT laws knowsB decidesB early_idem Nat.one_pos
    (Nat.le_refl 1) fun x rec y τ h _ => tieB x rec y τ h

/-! ## A coding -/

/-- positions, symbols and plain parts of the file's rounds are countable -/
theorem ctbG : CtbS G.sh G.ann := by
  repeat' (first
    | (show True; exact trivial)
    | (show _ ∧ _; refine And.intro ?_ ?_)
    | infer_instance
    | (show Countable Unit; infer_instance))

theorem ctbAll (t : Tag) : CtbS (shapeOf (typedOracleCarrier LR Bd0 G.ann PUnit.unit) t)
    (annOf (typedOracleCarrier LR Bd0 G.ann PUnit.unit) t) := by
  cases t
  · exact ctbG
  · exact trivial
  · exact ctbG

theorem countable_pts0 :
    Countable (RealPts 1 WR.K (typedOracleCarrier LR Bd0 G.ann PUnit.unit)) ∧
      Countable (GhostPts 1 WR.K (typedOracleCarrier LR Bd0 G.ann PUnit.unit)) :=
  haveI : Countable (_root_.Compile.SymAny G.sh) := _root_.Compile.Batch.countable_symAny _ _ ctbG
  countable_pts 1 WR.K (typedOracleCarrier LR Bd0 G.ann PUnit.unit)
    (inferInstanceAs (Countable (Option Y2 × Rec0 × Rec0)))
    (inferInstanceAs (Countable (Option (_root_.Compile.SymAny G.sh)))) ctbAll

/-- a coding of the typed oracles of this carrier: the library's `implOf` at codes by choice -/
def m0 : OracleCoding (typedOracleFamily 1 WR.K (typedOracleCarrier LR Bd0 G.ann PUnit.unit)) 1 :=
  haveI := countable_pts0.1
  haveI := countable_pts0.2
  implOf 1 WR.K (typedOracleCarrier LR Bd0 G.ann PUnit.unit) (StrCode.ofCountable _) (StrCode.ofCountable _)

end TypedOracleCompiler.Joined.Toy

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A coding agrees with itself on the leaf and node oracles, if lam is not 0. -/
theorem sameTrees_refl {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} (hlam : 0 < lam)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) : SameTrees W m m := by
  have h1 : Subsingleton (Fin (m.blocks OracleName.leaf)) := by
    rw [blocks_leaf hlam m]
    infer_instance
  have h2 : Subsingleton (Fin (m.blocks OracleName.node)) := by
    rw [blocks_node hlam m]
    infer_instance
  exact ⟨fun q j j' => by rw [Subsingleton.elim j j'], fun q j j' => by rw [Subsingleton.elim j j'],
    fun _ => rfl, fun _ => rfl⟩

end TypedOracleCompiler.Compile.Batch.Cms

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-- the fixed record in a session's request -/
def rec3 : LR.Rec := (fun _ _ => false, false)

/-- **Every hypothesis of `three_arms` but hC and hP is met at this interface, this wire record and
this coding**: the theorem applied with hC and hP alone left: for every committer and every prover
with bounded queries. -/
theorem toy_three_arms {St : Type} (Ct : OComp (rom 1) ((Dig 1 × LR.Rec) × St))
    (Pt : St → OComp (rom 1) (OutP3 1 LR G.ann PUnit.unit)) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (exp3A WR (armTL WR SR cA3) (armL WR SR cA3) (armBL WR SR cA3 rec3) m0 m0 m0 Ct Pt)
        (fun _ => {x | x.2.2.1 = true ∧ x.2.2.2.1 = true ∧ x.2.2.2.2 = true ∧
          ¬ ∃ i, LR.decodeIndex (extEnc WR (singleTr m0 x.1.2) x.1.1.1.1) x.1.1.1.2 = some i ∧
            ∃ w, Rn i x.2.1.1.2.2.1 w}) ≤
      ((((tC + tP + 1 + tVT WR) * (1 + 2) : ℕ) : ℝ≥0∞) * (1 / 2) +
        2 * (((tC + tP + 1 + tVT WR) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1) +
      (((((tC + tP + 1 + tVL WR) * (1 + 4) : ℕ) : ℝ≥0∞) * (1 / 2) +
        2 * (((tC + tP + 1 + tVL WR) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1) +
      ((((tC + tP + tVB WR) * (1 + 2) : ℕ) : ℝ≥0∞) * (1 / 2) +
        2 * (((tC + tP + tVB WR) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1)) :=
  three_arms Rn (fun _ _ _ => ()) soundAt.sndT (isLocal_of_eq LR.offline rfl isLocalT)
    (coherent_of_test DT laws LR.offline rfl G.ann HEq.rfl) okta (below_err0 _ G.sh)
    (isArmT_armTL WR SR cA3) soundAt.sndL isLocalLk trivial okla trivial (isArm_armL WR SR cA3)
    (headSeeds_armL SR cA3) soundAt.sndB
    (isLocal_of_eq LR.onlineBatch.loc (congrArg BatchInteractiveOracleProof.loc rfl) isLocalB)
    (coherent_of_bat DB laws LR.onlineBatch rfl) okba (below_err0 _ G.sh) (isArmB_armBL WR SR cA3 rec3)
    (headSeedB_armBL SR cA3 rec3) ansOK3 hSd Nat.one_pos m0 m0 m0 (sameTrees_refl Nat.one_pos m0)
    (sameTrees_refl Nat.one_pos m0) Ct Pt tC tP hC hP

/-- At hash values of one bit each term of the bound is at least 1, whatever the error of a query:
the bound says nothing on the number. -/
theorem one_le_term (εs : ℝ≥0∞) (n : ℕ) :
    1 ≤ (n : ℝ≥0∞) * εs + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1 := by
  refine le_trans ?_ le_add_self
  rw [pow_one, mul_comm, mul_div_assoc, ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  refine one_le_pow₀ ?_
  exact_mod_cast Nat.le_add_left 1 n

end TypedOracleCompiler.Joined.Toy
