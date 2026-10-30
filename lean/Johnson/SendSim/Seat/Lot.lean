-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/Lot.lean: the sender's rows (sendRow, "our rows") at the places of K1's own
lot. Without the simulators, the lot of these rows is that lot's honest side lotSide.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. wit (how the input is read), no (the number of each place's first new oracle
message) and D (the data) are arbitrary.
  lotJobs             The jobs of the honest side lotSide, in its order and with its parameters: the
                      first segment's opening, then the reads and digits of each segment for which
                      K1.linkNumbers gives numbers.
  sendLot_is_lotSide  Proved here. Without the simulators (SLot.toHLot), sendLot at the lot's name,
                      wit and lotJobs no D is lotSide wit no D.
  fits_of_seat        Proved here. If the library's public test placeSeatOk accepts, the job fits
                      its place (sendFits). By seat_job.
  seated_of_block     Proved here. If Side.seated returns a side for our row at a job, and the
                      side's sub-protocol is a given b with K1's rounds and oracle messages at the
                      job's P, the side is Seated at jobOver J wit.
  seated_first, seated_later, seated_reads   Proved here: seated_of_block where b is the lot's own
                      sub-protocol at the opening (K1.firstSegmentOpening), at a later sending (K1.laterAt),
                      and at a segment's reads with a step without rounds joined behind it
                      (IM.k1Reads).

Limits.
  - seated_first, seated_later and seated_reads are true, but they cannot be applied at the proof
    file's description. Their premise "the side's sub-protocol is the lot's" cannot hold there. They
    are stated for claims of the type Unit, as the lot's own sub-protocols have them, and the
    description's list holds each such sub-protocol with the type of its claims changed and wrapped
    (AtDesc.lean, "Why it is needed", lists what the wrapper adds). What they prove is that the
    steps which the lot itself joins add no round and no oracle message. For the members of the
    description's first chain at these places, Seated is proved in AtDesc.lean and AtDescStands.lean
    (seatedAt_job), if the maker (ProofFile.onlineDescription) succeeds.
  - The premises on the book, on queried positions and on challenges in the statements over Seated
    remain. Where each premise is proved for the release's files: the table of premises in
    Johnson/SendSim/Defs.lean.
  - wit, no and D are free variables, as in the honest side's file. Nothing says which wit, no and D
    are the honest prover's.
  - What a joined step decides is not spoken of: Seated requires the rounds, the oracle messages and
    the row.
  - The statements are about single values: no distribution is named.

How it fits. lotSide, placeJob, placeSeatOk and seat_job are in
Johnson/Desc/ProofFile/Honest/K1/PlaceJob.lean, reads_member in
Johnson/Desc/ProofFile/Honest/K1/PlaceQuiet.lean, sendLot in LotOf.lean. lotJobs is one of the two
lists of jobs of Spec.fieldsAtLots, and sendLot_is_lotSide gives sendLots_toHLot (AtDescLots.lean).
No file uses fits_of_seat or the three special cases: at the description FitsAtLots.lean and
AtDesc.lean take their place.

The other names.
  placeHalf_eq        the part that the honest side has at a job, placeHalf, is liftedHalf
                      (LotOf.lean), by rfl.
  lotHalves_eq        the honest side's list lotHalves is placeHalf of the jobs lotJobs.
-/
import Johnson.SendSim.Seat.LotOf
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.K1.PlaceQuiet

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At

variable {S Cl V W X Xi Pb : Type}

/-- What the honest side has at a job's place, placeHalf, is liftedHalf. -/
theorem placeHalf_eq (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) :
    placeHalf (V := V) wit J = liftedHalf wit J := rfl

/-- The jobs of the honest side lotSide of K1's own lot, in its order and with its parameters: the
first segment's opening, then the reads and digits of each segment for which K1.linkNumbers gives
numbers. -/
def lotJobs (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) : List (SendJob (PlaceIn Xi) X) :=
  placeJob (K1.firstPar G.first (K1.gpOf Z)) (no ⟨1, some 0, 1, .K1⟩) (firstFold G.first) (D Z G) ::
    G.built.toList.zipIdx.flatMap fun (Y, l) =>
      match K1.linkNumbers G Y with
      | none => []
      | some (pr, pd, _, _) =>
        [laterJobAt G.first (K1.gpOf Z) l pr 1 (no ⟨1, some l, pr, .K1⟩) (D Z G),
         laterJobAt G.first (K1.gpOf Z) l pd 2 (no ⟨1, some l, pd, .K1⟩) (D Z G)]

/-- The honest side's list lotHalves is placeHalf applied to the jobs lotJobs. -/
theorem lotHalves_eq (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    lotHalves (V := V) (X := X) wit no D Z G = (lotJobs no D Z G).map (placeHalf wit) := by
  unfold lotHalves lotJobs
  rw [List.map_cons, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨Y, l⟩ := x
  rcases hn : K1.linkNumbers G Y with _ | ⟨pr, pd, reads, digits⟩
  · simp only [hn]
    rfl
  · simp only [hn]
    rfl

/-- Without the simulators (SLot.toHLot), our lot at the jobs lotJobs is the honest side lotSide of
K1's own lot. -/
theorem sendLot_is_lotSide (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    (sendLot (V := V) (Pb := Pb) "K1: the first segment's opening, each link's reads and digits"
      wit (lotJobs (X := X) no D)).toHLot = lotSide wit no D := by
  rw [sendLot_toHLot]
  show (⟨_, _⟩ : HLot V W X) = ⟨_, lotHalves wit no D⟩
  congr 1
  funext Z G
  exact (lotHalves_eq wit no D Z G).symm

/-- If Side.seated returns a side for our row at J's place and at jobOver J wit, and the side's
sub-protocol is b, which has K1's rounds and oracle messages at J.P, the side is Seated at jobOver J
wit. -/
theorem seated_of_block {bs : List (Block S Cl)} {fs₀ : List (Fall S)}
    {σ₀ : Side S Cl V W X Pb} (J : SendJob (PlaceIn Xi) X) (wit : W → PlaceIn Xi)
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
      (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs₀ = some σ₀)
    (b : Block S Cl) (hb : σ₀.block = b) (hr : b.rounds = K1.rounds J.P)
    (ho : b.oracles = K1.oracles J.P) : Seated σ₀ (jobOver J wit) :=
  seated_lifted J wit hσ (hb ▸ hr) (hb ▸ ho)

/-- seated_of_block at the opening's job, if the side's sub-protocol is the lot's own K1.firstSegmentOpening.
This premise cannot hold at the proof file's description (see the head, Limits). -/
theorem seated_first {bs : List (Block First.S Unit)} {fs₀ : List (Fall First.S)}
    {σ₀ : Side First.S Unit V W X Pb} (wit : W → PlaceIn Xi) (first : Nat) (D : RowDataOf Xi)
    (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb)
        (placeJob (X := X) (K1.firstPar G.first (K1.gpOf Z)) first (firstFold G.first) D).P.place
        (jobOver (placeJob (X := X) (K1.firstPar G.first (K1.gpOf Z)) first (firstFold G.first) D)
          wit)).place
      (sendRow (V := V) (Pb := Pb)
        (placeJob (X := X) (K1.firstPar G.first (K1.gpOf Z)) first (firstFold G.first) D).P.place
        (jobOver (placeJob (X := X) (K1.firstPar G.first (K1.gpOf Z)) first (firstFold G.first) D)
          wit)).row fs₀ = some σ₀)
    (hb : σ₀.block = K1.firstSegmentOpening G.first (K1.gpOf Z)) :
    Seated σ₀ (jobOver
      (placeJob (X := X) (K1.firstPar G.first (K1.gpOf Z)) first (firstFold G.first) D) wit) :=
  seated_of_block _ wit hσ _ hb rfl rfl

/-- seated_of_block at the job of a later sending, if the side's sub-protocol is the lot's own
K1.laterAt. This premise cannot hold at the proof file's description (see the head, Limits). -/
theorem seated_later {bs : List (Block First.S Unit)} {fs₀ : List (Fall First.S)}
    {σ₀ : Side First.S Unit V W X Pb} (wit : W → PlaceIn Xi) (q : Params.First)
    (gp : _root_.Desc.Plain.GPar) (link piece moment first : Nat) (D : RowDataOf Xi)
    (arrays : Option (List Nat))
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb)
        (laterJobAt (X := X) q gp link piece moment first D).P.place
        (jobOver (laterJobAt (X := X) q gp link piece moment first D) wit)).place
      (sendRow (V := V) (Pb := Pb) (laterJobAt (X := X) q gp link piece moment first D).P.place
        (jobOver (laterJobAt (X := X) q gp link piece moment first D) wit)).row fs₀ = some σ₀)
    (hb : σ₀.block = K1.laterAt q gp link piece moment arrays) :
    Seated σ₀ (jobOver (laterJobAt (X := X) q gp link piece moment first D) wit) :=
  seated_of_block _ wit hσ _ hb (later_rounds q gp link piece moment first D arrays).1
    (later_rounds q gp link piece moment first D arrays).2.1

/-- seated_of_block at the job of a segment's reads, if the side's sub-protocol is IM.k1Reads: the
reads' sub-protocol with a step without rounds or oracle messages joined behind it. This premise
cannot hold at the proof file's description (see the head, Limits). -/
theorem seated_reads {bs : List (Block First.S Unit)} {fs₀ : List (Fall First.S)}
    {σ₀ : Side First.S Unit V W X Pb} (wit : W → PlaceIn Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (l : Nat) (Y : OnBytes.Model.Stages.LinkH) (pr : Nat) (reads : Option (List Nat))
    (first : Nat) (D : RowDataOf Xi)
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb)
        (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D).P.place
        (jobOver (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D) wit)).place
      (sendRow (V := V) (Pb := Pb) (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D).P.place
        (jobOver (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D) wit)).row fs₀ = some σ₀)
    (hb : σ₀.block = IM.k1Reads Z G l Y pr reads) :
    Seated σ₀ (jobOver (laterJobAt (X := X) G.first (K1.gpOf Z) l pr 1 first D) wit) :=
  seated_of_block _ wit hσ _ hb (reads_member Z G l Y pr reads first D).1
    (reads_member Z G l Y pr reads first D).2.1

/-- If the library's public test placeSeatOk accepts, the job placeJob, read through wit, fits its
place (sendFits). -/
theorem fits_of_seat (wit : W → PlaceIn Xi) (P : K1.Par) (first : Nat)
    (fold : Option (Nat × FoldShape)) (D : RowDataOf Xi) (x : Xi) (hs : List Fmt.Drawn)
    (part : Nat) (h : placeSeatOk P fold (D x) hs part = true) :
    sendFits (jobOver (placeJob (X := X) P first fold D part) wit).P
      (jobOver (placeJob (X := X) P first fold D part) wit).ride = true :=
  (seat_job (X := X) P first fold D x hs part h).2

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.sendLot_is_lotSide
#print axioms OnBytes.SendSim.Seat.seated_first
#print axioms OnBytes.SendSim.Seat.seated_later
#print axioms OnBytes.SendSim.Seat.seated_reads
#print axioms OnBytes.SendSim.Seat.fits_of_seat
