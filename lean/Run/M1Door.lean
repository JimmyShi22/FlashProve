-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1Door.lean: the first toy's protocol, as the Test protocol of an interface, meets formal side
conditions of the library's compilation theorems (the record `Met`); the conditions with content are
not met. (Test, Link and Batch are the three protocols of an interface: fields `offline`, `link`, `onlineBatch`
of `BatchProtocol`, Iop/Batch.lean.)

The first toy is a product test, for which the programs (the C++ implementation that comes with
this Lean code) write proof files. The library's compilation theorems ask a list of conditions of
an interface and of its wiring (the data that say how deep the trees are, where a position stands
among a tree's leaves, and how blocks of a hash answer give a verifier message). This file proves,
at six descriptions of the toy and with nothing assumed, the twelve conditions of the record `Met`.
What is left is named below (part 4), not all of it. The library's theorem `bcsSoundBatchG`
(Compile/Batch/SpecSoundG.lean) applies, and its conclusion is empty here.

The terms. L := LtS (ckP ..) (rds S) dec is the interface whose Test is the toy's protocol
(Run/PlanQS.lean). It has no index (an encoded index of length 0; the decoder accepts every
string), and Link and Batch have no rounds. W is the wiring W* of Run/M1RunTieP.lean: Test's wiring
comes from the description.

Two interfaces. The run functions do not stand at (L, W). The theorems of part 3 are at the
interface `LtS`. The run functions stand at the interface `LbS`, whose Batch is the same protocol.
At the six descriptions, what is evaluated behind the reader (`VPP`, Run/PlanQSP.lean) is the run
of Compile.Batch.vBS (Wb W.K W.T) .. at `LbS`. That is shown by `vbsP_A` to `vbsP_K` of
Run/M1RunTieP.lean. W.T, the Test's wiring of which this file speaks, is the slot's wiring at `LbS`
(the field B of Wb W.K W.T). What is met at `LbS` is in Run/BatchDoor.lean (`metB`). What is said
here of `LtS`, of its Test and of the wirings W* holds as it stands: these are facts about terms
(Run/BatchS.lean: `batch_same`).

1. What the file contains.
   `Met L W`: a record of twelve conditions:
      `okg`: the laws of the whole wiring (W.OKG): the laws of the three wirings, exactly uniform
        verifier messages among them (this needs the form in which a round's verifier message is
        its hash blocks); the external oracles' wiring; depths; slots.
      `wired`: the honest sides' external strings are encodings.
      `reads`: no external position is read (all counts 0).
      `localT`, `localL`, `localB`: the three verifiers depend on the oracles only at the positions
        read (Test's: whatever the decision, by the form of the view: Run/PlanQSLaws.lean).
      `cohB`: the batch's annotation is coherent.
      `pointT`, `pointL`, `pointB`: the three shapes are read symbol by symbol.
      `sound`: L.Sound (everything) 0.
      `low`: Compile.Batch.BcsAt W (everything) 0, the conclusion of `bcsSoundBatchG`.
   `zErr`, `lts_sound`, `lts_wired`, `lts_reads`, `ptSL`, `lts_pointT`, `we0_ok`, `weL_ok`, `okgW`,
     `metOf`: the generic parts, for every choice of challenge types (for each round the type of
     the verifier's message, and the map from such a message to the format's record of what was
     drawn; `CK` in the code), list of rounds and decision.

2. What is checked when the file compiles. Only the types.

3. Theorems. Many statements of this library are written twice: a definition in the namespace `Spec`
   states a proposition, and a theorem of the same name outside that namespace proves it
   (lean/GLOSSARY.md).
   `met_A` to `met_K`: Met L W at all six descriptions. A, B: this library's own small sizes. T, R:
     the programs' tiny parameters. F, K: their full parameters, 30 rounds.
   `metF_T`, `metF_R`, `metF_F`: the same at the wiring with whole paths, where each opened leaf
     has an authentication path of its own (in the code: without the flag for pruned sets; the W of
     Run/M1RunTiePF.lean at the programs' own parameters: tiny (T, R) and full (that file's F,
     which is the description K above)). In these two respects (challenges as hash blocks; whole
     paths) this is the form of the wiring that the library's theorems with a witness use.

Notation:
  `BatchProtocol Unit Unit`: interfaces whose indices and instances have the type `Unit` (`BatchProtocol`,
    Iop/Batch.lean);
  `QueryLayout 256 L`: the whole wirings of the interface `L` (Iop/BatchWire.lean);
  the last 0 of `L.Sound All 0`: `εs`, the second argument of `Err.Below` in its three fields
    (`BatchProtocol.Sound`, Iop/Batch.lean);
  the last 0 of `BcsAt W All 0`: its argument `εs` (Compile/Batch/SpecSoundG.lean);
  `All`: the relation `fun _ _ => True`.

4. What is not claimed.
   No statement on soundness follows. The fields `sound` and `low` are true and empty. A Test's
   language is a property of the external string ("it decodes"). Here every string decodes, and
   Link's and Batch's languages are "everything" too. So no statement lies outside a language, and
   nothing is asked of any round. The clause of `bcsSoundBatchG` on an accepted Test string is "the
   external string under cm decodes", which is true of everything. It says nothing about the toy's
   claim.
   Of the thirteen fields of the interface's properties (Iop/Batch.lean: `BatchProtocol.Props`) eleven are met
   here: ten are fields of `Met` (all but `okg` and `low`, which speak of the wiring), and "sub" is
   trivial at "everything". One is not met, and not to be had from a description: complete (an
   honest prover that is accepted: LtS's honest sides are placeholders, which send each round's
   fixed substitute). The other, hidden (honest-verifier zero knowledge of that honest prover), the
   field `hidden` of `BatchProtocol.Props`, Iop/Batch.lean, is not shown of this interface, in this file or
   elsewhere in Run/.
   The one condition with content is round-by-round (knowledge) soundness of the toy's protocol for
   a named relation ("the prover knows a, b, c with a_i b_i = c_i"). It is neither stated nor proved
   in Run/ or Fmt/. As a Test it cannot even be asked, since a Test's language speaks of the
   external string alone. The form in which a clause has content is the toy as the interface's
   Batch, with the map that reads a witness off the prover's own oracle messages, run under the tag
   of Batch (Hiop/Interface.lean: PropsK.soundK; Hiop/GrindK.lean: SoundKG).
   Other hypotheses of the theorems with a witness, for the record (not restated here; not all are
   named: see `FitK`, CompileK/Main.lean, and `FitWk`, CompileK/GrindMain.lean):
     the samplers' law with its bias, and the number of blocks: Run/PlanDrawsQ.lean (`planQ_good`,
       `planQ_blocks`);
     work at most 64 bits, nonces read back: as in `okgP_A` to `okgP_K`;
     counts of openings: Run/PlanQWireLaws.lean, Run/PlanQSLaws.lean.
   Shown in other files:
     that the protocol with challenges as hash blocks is the library's own construction from the
       protocol with drawn values, with its tests (Run/PlanPullProtoProofs.lean: `planPull_proto`),
     and that a round's wiring with whole paths is the library's own (Run/PlanPullWire.lean,
       Run/PlanPullWireT.lean);
     and, in a file not in this library, at three descriptions only (the programs' own parameters:
       T, R, F of Run/M1RunTiePF.lean) and at the wiring with whole paths only, that interface and
       wiring as a pair are those of the library's compilation with work at data that are written
       down (Run/PlanPullJoin.lean [not in this library; so here read: not proved in this library]).
   Not shown: the same at the other descriptions, or at the wiring with pruned openings (which has
   no such equation); the hiding budget (`FitK.budget`, CompileK/Main.lean). Near the first of
   these: `planPull_join`, Run/PlanPullJoin.lean [not in this library; so here read: not proved in
   this library], is that
   equation for both of the format's fields (`Fmt.Fld`), every list of rounds, decision, number of
   salt bytes and K with (Dv ..).dr.K = K, with challenges as hash blocks and at the wiring with
   whole paths (`wqSF`), of the pair `packW ..`; that this pair is (`LtS ..`, the W of
   Run/M1RunTiePF.lean) is stated in Run/ or Fmt/ at the three descriptions alone (`pack_T`,
   `pack_R`, `pack_F`).
   Nothing is said about bytes: these are statements on typed terms and uniform typed oracles. It
   is not claimed that the decision is the one that the programs compute.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.M1RunTieP
import Run.M1RunTiePF
import Compile.Batch.Sound

set_option autoImplicit false

namespace Run.M1Door
open Iop Rom Compile Compile.Batch Prob Run.PQ
open scoped ENNReal

/-- the relation "everything" -/
abbrev All : Unit → Unit → Prop := fun _ _ => True

/-- A record of twelve conditions. In this file's theorems the fields `sound` and `low` are true
and empty: the head, 4. -/
structure Met (L : BatchProtocol Unit Unit) (W : QueryLayout 256 L) : Prop where
  okg    : W.OKG
  wired  : L.Wired
  reads  : L.Reads 0 0 0 0 0
  localT : L.offline.IsLocal
  localL : L.link.IsLocal
  localB : L.onlineBatch.loc.IsLocal
  cohB   : L.onlineBatch.ann.Coherent
  pointT : Nonempty L.offline.shape.IsPoint
  pointL : Nonempty L.link.shape.IsPoint
  pointB : Nonempty L.onlineBatch.loc.shape.IsPoint
  sound  : L.Sound All 0
  low    : BcsAt W All 0

/-! ## For every choice of challenge types, list of rounds and decision -/

/-- the list of errors 0 -/
def zErr : (s : Shape) → Err s
  | [] => ()
  | _ :: s => (0, zErr s)

theorem zErr_below : ∀ (s : Shape) (c : ℝ≥0∞), Err.Below (zErr s) c
  | [], _ => trivial
  | _ :: s, c => ⟨by show ((0 : ℕ) : ℝ≥0∞) ≤ _; rw [Nat.cast_zero]; exact zero_le _, zErr_below s c⟩

theorem lts_sound (C : CK) (ds : List RD) (dec : View → Bool) : (LtS C ds dec).Sound All 0 where
  sndT := ⟨zErr _, zErr_below _ _,
    fun _ _ h => absurd (fun e : (some () : Option Unit) = none => by cases e) h⟩
  sndL := ⟨(), trivial, fun _ _ h => absurd (Or.inr rfl) h⟩
  sndB := by
    have lang : ∀ _ : Fin 0 → Unit,
        (some () : Option Unit) = none ∨ ∃ i, (some () : Option Unit) = some i ∧ All i () :=
      fun _ => Or.inr ⟨(), rfl, trivial⟩
    refine ⟨(), trivial, fun n h => ?_, fun _ _ _ => true, ?_, ?_, ?_, ?_, ?_⟩
    · exact absurd h (by show (none : Option ℕ) ≠ some n; exact fun e => by cases e)
    · intro y x h
      exact absurd (lang y) h
    · intro y x τ
      exact Empty.elim τ
    · intro y x τ
      exact Empty.elim τ
    · intro y x τ h
      exact absurd (lang y) h
    · intro y x
      exact trivial

theorem lts_wired (C : CK) (ds : List RD) (dec : View → Bool) : (LtS C ds dec).Wired :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem lts_reads (C : CK) (ds : List RD) (dec : View → Bool) : (LtS C ds dec).Reads 0 0 0 0 0 where
  cntT := fun _ _ => le_refl 0
  cntLp := fun _ _ => le_refl 0
  cntLc := fun _ _ => le_refl 0
  cntB := fun x _ => by
    simp only [BatchInteractiveOracleProof.allReads]
    simp
    cases x 0 <;> rfl
  hidE := fun _ _ _ _ => rfl

/-- the shape after the trivial round is read symbol by symbol -/
def ptSL (C : CK) : (ds : List RD) → Shape.IsPoint (uL C ds)
  | [] => ()
  | d :: ds =>
    (⟨inferInstanceAs (Fintype (Fin (posN d.tree))),
        inferInstanceAs (DecidableEq (Fin (posN d.tree))), fun f => f, fun _ _ => rfl,
        fun _ => rfl, fun _ _ => 0⟩,
      ptSL C ds)

theorem lts_pointT (C : CK) (ds : List RD) (dec : View → Bool) :
    Nonempty (LtS C ds dec).offline.shape.IsPoint :=
  ⟨(⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
      fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩,
    ptSL C ds)⟩

theorem we0_ok : we0.OK := ⟨List.nodup_nil, fun p => p.elim0, fun _ p => p.elim0⟩
theorem weL_ok : weL.OK :=
  ⟨List.nodup_nil, fun p => p.elim (·.elim0) (·.elim0), fun _ p => p.elim (·.elim0) (·.elim0)⟩

/-- the whole wiring obeys the laws if Test's does (`hT`) and Test's wiring of the external oracles
is `we0` (`he`) -/
theorem okgW (C : CK) (ds : List RD) (dec : View → Bool) (K : ℕ)
    (T : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline)) (hT : T.OKG) (he : T.ext = we0) :
    (⟨K, T, ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩,
    ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩, 0, 0⟩ : QueryLayout 256 (LtS C ds dec)).OKG :=
  { T := hT
    Lk := { sh := trivial, ext := weL_ok, opens := fun _ _ _ => le_refl 0, depth := trivial }
    B := { sh := trivial, ext := we0_ok, opens := fun _ _ _ => le_refl 0, depth := trivial }
    fits := Nat.zero_le _
    slots := rfl
    extDepth := ⟨by rw [he]; rfl, rfl, rfl⟩
    depthT := Nat.zero_le _, depthL := le_refl 0, depthB := le_refl 0
    extT := fun p => p.elim0
    extB := fun p => p.elim0
    extL := ⟨fun p => p.elim0, fun p => p.elim0⟩ }

/-- all of Met from the laws of the whole wiring -/
theorem metOf (C : CK) (ds : List RD) (dec : View → Bool)
    (W : QueryLayout 256 (LtS C ds dec)) (h : W.OKG) : Met (LtS C ds dec) W where
  okg := h
  wired := lts_wired C ds dec
  reads := lts_reads C ds dec
  localT := psof_local C ds dec
  localL := fun _ _ _ _ _ _ _ _ _ => rfl
  localB := fun _ _ _ _ _ _ _ _ _ => rfl
  cohB := BatchOne.BAnn.allLocal_coherent _
  pointT := lts_pointT C ds dec
  pointL := ⟨()⟩
  pointB := ⟨()⟩
  sound := lts_sound C ds dec
  low := bcsSoundBatchG Unit Unit 256 _ W All 0 (lts_sound C ds dec) (psof_local C ds dec)
    (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl)
    (BatchOne.BAnn.allLocal_coherent _) h

/-! ## At the six descriptions -/

def Spec.met_A : Prop := Met _ M1RunTieP.WA

theorem met_A : Spec.met_A :=
  metOf _ _ _ M1RunTieP.WA (okgW _ _ _ _ M1RunTieP.WA.T M1RunTieP.okgP_A rfl)

def Spec.met_B : Prop := Met _ M1RunTieP.WB

theorem met_B : Spec.met_B :=
  metOf _ _ _ M1RunTieP.WB (okgW _ _ _ _ M1RunTieP.WB.T M1RunTieP.okgP_B rfl)

def Spec.met_T : Prop := Met _ M1RunTieP.WT

theorem met_T : Spec.met_T :=
  metOf _ _ _ M1RunTieP.WT (okgW _ _ _ _ M1RunTieP.WT.T M1RunTieP.okgP_T rfl)

def Spec.met_F : Prop := Met _ M1RunTieP.WF

theorem met_F : Spec.met_F :=
  metOf _ _ _ M1RunTieP.WF (okgW _ _ _ _ M1RunTieP.WF.T M1RunTieP.okgP_F rfl)

def Spec.met_R : Prop := Met _ M1RunTieP.WR

theorem met_R : Spec.met_R :=
  metOf _ _ _ M1RunTieP.WR (okgW _ _ _ _ M1RunTieP.WR.T M1RunTieP.okgP_R rfl)

def Spec.met_K : Prop := Met _ M1RunTieP.WK

theorem met_K : Spec.met_K :=
  metOf _ _ _ M1RunTieP.WK (okgW _ _ _ _ M1RunTieP.WK.T M1RunTieP.okgP_K rfl)

/-! ## The same at the wiring without the flag for pruned sets -/

def Spec.metF_T : Prop := Met _ M1RunTiePF.WT

theorem metF_T : Spec.metF_T :=
  metOf _ _ _ M1RunTiePF.WT (okgW _ _ _ _ M1RunTiePF.WT.T M1RunTiePF.okgPF_T rfl)

def Spec.metF_R : Prop := Met _ M1RunTiePF.WR

theorem metF_R : Spec.metF_R :=
  metOf _ _ _ M1RunTiePF.WR (okgW _ _ _ _ M1RunTiePF.WR.T M1RunTiePF.okgPF_R rfl)

def Spec.metF_F : Prop := Met _ M1RunTiePF.WF

theorem metF_F : Spec.metF_F :=
  metOf _ _ _ M1RunTiePF.WF (okgW _ _ _ _ M1RunTiePF.WF.T M1RunTiePF.okgPF_F rfl)

end Run.M1Door
