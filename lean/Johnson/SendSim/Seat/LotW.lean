-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotW.lean: the sender's row (sendRow, "our row") at the place where the
request's own table is sent. Without the simulators, the lot of that row is the place's honest side
wSide.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. wit (how the input is read), no (the number of the place's first new oracle
message) and D (the data) are arbitrary.
  wJobs             The job of the honest side wSide, if linMessageW gives the oracle messages of
                    that sending; else the empty list.
  sendLot_is_wSide  Proved here. Without the simulators (SLot.toHLot), sendLot at the lot's name,
                    wit and wJobs no D is wSide wit no D.
  seated_w          Proved here. Let linMessageW give the oracle messages msg and K1.wAt the
                    sub-protocol b. If Side.seated returns a side for our row at that job, and the
                    side's sub-protocol is K13.atM4 p b (b with a sub-protocol of the kind K13
                    joined behind it), the side is Seated. By w_member: the joined sub-protocol adds
                    no round and no oracle message.

Limits.
  - seated_w is true, but it cannot be applied at the proof file's description. Its premise "the
    side's sub-protocol is the lot's" cannot hold there: the description's list holds that
    sub-protocol with the type of its claims changed and wrapped. What it proves is that the other
    kind's sub-protocol, joined behind, adds no round and no oracle message. For the description's
    own member at that place, Seated is proved as seatedAt_w (AtDesc.lean), if the maker
    (ProofFile.onlineDescription) succeeds.
  - At the full size the table that is sent along with the request's own table has two rows (said
    here without a theorem). So the statements over Seated that require "one row" (BookClear) are
    vacuous at the part that spends its coefficients. The wider ones (BookClearAny) keep premises on
    the book and on queried positions.
    Where each premise is proved for the release's files: the table of premises in
    Johnson/SendSim/Defs.lean.
  - wit, no and D are free variables. Nothing says which wit, no and D are the honest prover's. The
    rows of the request's own table are made elsewhere.
  - If linMessageW gives nothing, there is no job, and the honest side has nothing at the place.
  - What the joined sub-protocol decides is not spoken of.
  - The statements are about single values: no distribution is named.

How it fits. wSide, wJobAt and w_member are in Johnson/Desc/ProofFile/Honest/K1/PlaceW.lean, sendLot
in LotOf.lean, seated_of_block in Lot.lean. wJobs is the second of the two lists of jobs of
Spec.fieldsAtLots, and sendLot_is_wSide gives sendLots_toHLot (AtDescLots.lean). No file uses
seated_w: at the description seatedAt_w takes its place.

The other names. wHalves_eq: the honest side's list wHalves is placeHalf of the jobs wJobs.
-/
import Johnson.SendSim.Seat.Lot
import Johnson.Desc.ProofFile.Honest.K1.PlaceW

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {V W X Xi Pb : Type}

/-- The job of the honest side wSide at the place where the request's own table is sent, if
linMessageW gives that sending's oracle messages; else the empty list. -/
def wJobs (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) : List (SendJob (PlaceIn Xi) X) :=
  ((linMessageW Z.first.lin).map fun msg =>
    wJobAt Z.first (wGp Z) 4 msg (no ⟨1, none, 4, .K1⟩) (D Z G)).toList

/-- The honest side's list wHalves is placeHalf applied to the jobs wJobs. -/
theorem wHalves_eq (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    wHalves (V := V) (X := X) wit no D Z G = (wJobs no D Z G).map (placeHalf wit) := by
  unfold wHalves wJobs
  cases linMessageW Z.first.lin <;> rfl

/-- Without the simulators (SLot.toHLot), our lot at the jobs wJobs is the honest side wSide. -/
theorem sendLot_is_wSide (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    (sendLot (V := V) (Pb := Pb)
      "K1 and K13: W's commitment, the request's own group and the row (Eval)" wit
      (wJobs (X := X) no D)).toHLot = wSide wit no D := by
  rw [sendLot_toHLot]
  show (⟨_, _⟩ : HLot V W X) = ⟨_, wHalves wit no D⟩
  congr 1
  funext Z G
  exact (wHalves_eq wit no D Z G).symm

/-- If linMessageW gives msg (hm), K1.wAt gives b (hw), Side.seated returns a side for our row at
the job wJobAt, and the side's sub-protocol is K13.atM4 p b, the side is Seated. The last premise
cannot hold at the proof file's description (see the head, Limits). -/
theorem seated_w {bs : List (Block First.S Unit)} {fs₀ : List (Fall First.S)}
    {σ₀ : Side First.S Unit V W X Pb} (wit : W → PlaceIn Xi) (q : Params.First)
    (gp : _root_.Desc.Plain.GPar) (piece first : Nat) (msg : Array OracleNotice)
    (D : RowDataOf Xi) (b : Block First.S Unit) (p : K13.Where)
    (hm : linMessageW q.lin = some msg) (hw : K1.wAt q gp piece = some b)
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb)
        (wJobAt (X := X) q gp piece msg first D).P.place
        (jobOver (wJobAt (X := X) q gp piece msg first D) wit)).place
      (sendRow (V := V) (Pb := Pb) (wJobAt (X := X) q gp piece msg first D).P.place
        (jobOver (wJobAt (X := X) q gp piece msg first D) wit)).row fs₀ = some σ₀)
    (hb : σ₀.block = K13.atM4 p b) :
    Seated σ₀ (jobOver (wJobAt (X := X) q gp piece msg first D) wit) :=
  seated_of_block _ wit hσ _ hb (w_member q gp piece first msg D b p hm hw).1
    (w_member q gp piece first msg D b p hm hw).2.1

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.sendLot_is_wSide
#print axioms OnBytes.SendSim.Seat.seated_w
