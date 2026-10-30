-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LayersTie.lean: CONDITIONAL.

What is here. THE TIE ON THE WEIGHTS BETWEEN THE SCRIPT's WITNESS AND THE HONEST SIDE's INPUT, AS
ONE HYPOTHESIS. The lookup's own sentence on the keys, at a layers' link, reads the committed
matrix of the weights off the witness by the lookup's caller's reading (wOfE of layMu,
Johnson/Desc/First/Look/K3CallerLay.lean and K3LayGoodIn.lean); the laws on the feed-forward
layers' own rounds (sub-protocol K4) read it off the honest side's input (wmOf of the small input
k4Wit). K4LayersTieAt says that layerR cuts the same matrices out of the two at layer 4 g + l, at
every l (there is no bound: also behind the group's four layers and behind the model's last layer)
and at every continuation of the challenges heard. layers_of_tie hands it over in the spelling of
the hypothesis hW of forK_lay_at (Johnson/Road/K4/C/KeysLetters.lean), at the small input.

  `K4LayersTieAt`   the tie; it defines a hypothesis.
  `layers_of_tie`   the tie at wmOf of the small input's weights.

Not shown here. THAT THE TIE HOLDS AT ANY SCRIPT: no example is known. Outside nr rows and nc
columns the caller reads 0: WHERE layerR READS SUCH PLACES, THE TIE SAYS THAT WHAT IT MAKES OF THE
INPUT's ENTRIES THERE IS WHAT IT MAKES OF ZEROS: a sentence on the input's reader outside the
table, which a reader that is 0 there meets and another may fail. WHETHER nr AND nc COVER WHAT
layerR READS AT THE GROUP's OWN LAYERS IS NOT SHOWN: nothing here ties them to the reference layout
of the weights. That a tie at the group's own layers would do is not shown. THE FULL SIZE ALONE.
What Law/W/OneTie.lean imports, this file imports. TWO MORE TIES ON THE SAME MATRIX STAND
ELSEWHERE: K4WeightsTieAt (Law/WoTies.lean: the witness's matrix, entry by entry, for the merge's
own claim) and the hypothesis hiW of the law on the own item in the first group (the small input's
weights are the casts of an index's matrix): that one of the three gives another is not shown.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OneTie
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart
import Johnson.Desc.First.Look.K3LayGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (layerR)
open VerifiableInference.Desc.First.Look (Sent sigListCalls wOfE)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (layMu)
open P5J (CellsM)
open ProofFile.Honest.FirstThread (Script WtF)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X' : Type}

/-- **THE TIE ON THE WEIGHTS**, at a stand in front of the member: at every continuation d of the
challenges heard and every l, without a bound: the matrices of layer 4 g + l, as layerR cuts them
out of what the lookup's caller reads off the witness, are those that it cuts out of the input's
entries, cast into the field. xl: the lookup's place. Ds, rad, oW, wOf, nr, nc, seatT, arr, msgW:
the lookup's caller's own parameters. This defines a hypothesis; the definition claims nothing. -/
def K4LayersTieAt
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (weights : W₀ → Weights) (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2)
    (Ds : Sent) (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (seatT : Fin (sigListCalls Ds rad xl.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (msgW : WtF → oW.Msg) (g : ℕ) (c : Coins Bk)
    (mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X') : Prop :=
  ∀ d l,
    layerR ppref kRef
        (wOfE (layMu xl tl Ds rad oW wOf nr nc seatT arr msgW
          (Q.wit c mm.st.input (mm.st.heard ++ d)))) (4 * g + l) =
      layerR ppref kRef
        (fun r c' => algebraMap Cb.Gl.F Cb.Gl.E ((weights mm.st.input.w₀).entry r c')) (4 * g + l)

/-- **The tie at wmOf of the small input's weights.** CONDITIONAL: on the tie. -/
theorem layers_of_tie
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {weights : W₀ → Weights} {xl : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    {Ds : Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
    {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
    {seatT : Fin (sigListCalls Ds rad xl.link).length → ℕ × ℕ} {arr : ℕ → ℕ → ℕ}
    {msgW : WtF → oW.Msg} {g : ℕ} {c : Coins Bk} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    (tie : K4LayersTieAt Q weights xl tl Ds rad oW wOf nr nc seatT arr msgW g c mm)
    (Qp : K4Pub) (cells : Tr → Cells) (tokens : ProofFile.Inst → Array Nat)
    (look : List Fmt.Drawn → Forest.Heard) (d : List Fmt.Drawn) (l : ℕ) :
    layerR ppref kRef
        (wOfE (layMu xl tl Ds rad oW wOf nr nc seatT arr msgW
          (Q.wit c mm.st.input (mm.st.heard ++ d)))) (4 * g + l) =
      layerR ppref kRef (wmOf (k4Wit Qp cells weights tokens look mm.st.input).w) (4 * g + l) := by
  have e : wmOf (k4Wit Qp cells weights tokens look mm.st.input).w =
      fun r c' => algebraMap Cb.Gl.F Cb.Gl.E ((weights mm.st.input.w₀).entry r c') := by
    funext r c'
    show OnBytes.Slice.readE (OnBytes.ofF (OnBytes.Slice.ofF _)) = _
    rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]
  rw [e]
  exact tie d l

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.layers_of_tie
