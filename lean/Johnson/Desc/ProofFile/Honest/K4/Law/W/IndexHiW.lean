-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexHiW.lean: CONDITIONAL.

What is here. THE HYPOTHESIS hiW OF THE LAWS ON THE OWN ITEM OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4), FROM THE ONE HYPOTHESIS ON THE WEIGHTS `K4IndexIs` (Law/IndexIs.lean), asked once
under the thread's parameter Vd of the thread's own input, at the thread with the library's own
values (`lettersHead`, Honest/Thread/FirstHead.lean). In two forms, each wherever `ThrS` stands: the
equation of functions, in every group (`hiWeq_of_index`); and the image under the library's `embR`,
under «the group is the first», which is the binder hiW of `k4_exchange_tenth`
(Law/ExchangeTenth.lean) to the letter (`hiW_of_index`). Each proof is a call or two: `indexIs_thr`
and `wm_of_entries` (Law/IndexIs.lean). `k4_exchange_own_at` (Law/ExchangeOwnAt.lean) calls the
second, which calls the first.

  `hiWeq_of_index`   the script's cells hold an index whose matrix's images are the weights that
      the honest side's reader reads, at every row and column; in every group.
  `hiW_of_index`   **the two embeddings are one, under «the group is the first».**

Not shown here. hI: THAT `K4IndexIs` HOLDS OF ANY SCRIPT AND INPUT: a hypothesis; Law/IndexIs.lean's
head says what an input must be for it to hold: its reader answers with the index's own matrix, so
with 0 outside the table; the type of an input does not give that. IT ASKS MORE THAN `hiW_of_index`
SPENDS: the second form reads the entries of the embedding's unit alone. THAT THE THREAD STANDS AT
ANY RUN. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), through `lettersHead`;
THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). The side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hI no example is known to us; `indexIsAt_member` (Law/IndexIsAt.lean)
has a member of hI's form without a script. No test stands beside it. Nothing on soundness, on
completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 16 modules under Johnson/Goal/ and at 4 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 20 is not counted: the numbers are floors. They come with h,
through Law/IndexIs.lean. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.IndexIs
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Inst.Model.FF.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (Forest.Heard)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (embR)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) (k : ℕ)
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}

/-- CONDITIONAL: on hI. **THE EQUATION OF FUNCTIONS, IN EVERY GROUP**, wherever `ThrS` stands. -/
theorem hiWeq_of_index (hI : Vd w₁ → K4IndexIs Q weights w₁) :
    ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∃ i : Cm.Idx, Holds (Q.cells mm.st.input) i ∧
        wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w =
          fun a b => ((i.mat a b : ℤ) : Cb.Gl.E) := by
  intro _ _ mm _ hT
  obtain ⟨i, hH, he⟩ := indexIs_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hI hT.1
  exact ⟨i, hH, wm_of_entries Qp cells weights tokens (look Qp) mm.st.input he⟩

/-- CONDITIONAL: on hI. **THE TWO EMBEDDINGS ARE ONE, under «the group is the first».** g: the
group. -/
theorem hiW_of_index (hI : Vd w₁ → K4IndexIs Q weights w₁) (g : ℕ) :
    ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∃ i : Cm.Idx, Holds (Q.cells mm.st.input) i ∧ (g = 0 →
        embR ppref kRef (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w) =
          embR ppref kRef fun a b => ((i.mat a b : ℤ) : Cb.Gl.E)) := by
  intro c s mm E hT
  obtain ⟨i, hH, e⟩ :=
    hiWeq_of_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said k (cells := cells)
      (tokens := tokens) (look := look) (Qp := Qp) hI c s mm E hT
  exact ⟨i, hH, fun _ => congrArg (embR ppref kRef) e⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.hiWeq_of_index
#print axioms ProofFile.Honest.K4.W.hiW_of_index
