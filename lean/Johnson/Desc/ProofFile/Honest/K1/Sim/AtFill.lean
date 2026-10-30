-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Sim/AtFill.lean: the shared "sending" (the kind K1): its two lots on
the first chain WITH THEIR SIMULATORS, as two values of SLot, at the letters of the filling
OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O); and, at what the maker onlineProverFromPublicFiles returns at that
filling, what the frame's rule asks of these rows. Four definitions; the rest are theorems.
The filling of the online honest prover (E2E/TheHonestProver.lean, onlineFilling) is this filling at
g := id, rd := tableCoins files, d' := matrixInput.dummy, I := matrixInput, o := secondHashFunction, S := Sz.ref,
O := openHonest.

  witAt            how a job reads the prover's input: the filling's own reader, read through g, rd
  lotS, wS         THE TWO VALUES: the row jobRow (Johnson/SendSim/Seat/AtDescLots.lean: the sender
                   sendPart beside its simulator sendSim, On := True, bud := budAt) at each job of
                   lotJobs and of wJobs, at the filling's own numbers and data
  half_thru        a row's half is the filling's half, read through
  lotS_toHLot, wS_toHLot   WITHOUT THE SIMULATORS THE TWO VALUES ARE THE FILLING'S OWN LOTS
  lots_split       where they lie in the filling's list: the first and the last
  others_not_k1    no other lot of the filling has a half at a place of the kind K1
  lotS_toHLot_base, wS_toHLot_base, lots_split_base, others_not_k1_base   THE SAME AT THE BASE
                   FILLING onlineProverPartsInUse I o S O, not read through: there the two values stand at
                   g := id, rd := id
  k1_rows_only, k1_rows_only_base   whoever lays all the filling's lots with simulators, ours first
                   and last: every row at a place of the kind K1 is one of our 52
  open_at          what onlineProverFromPublicFiles returns can be opened (IM.Open), at its own public part and ground
  k1Jobs, rows_eq  the 52 jobs; the rows of the two values are jobRow at these jobs
  handIn_at_return in scope, where the gate accepts, at what onlineProverFromPublicFiles returns AT ANY FILLING (the index's
                   and the randomness's types are letters): JOB BY JOB the four
                   premises that the rule file_owed_rows (Honest/Thread/Rows.lean) asks of a row: a
                   member is at the row's place; every side of the row has Good for some A₁, B₁, IF
                   THE BOOK IS CLEAR AT THAT JOB's OWN SENDER; bud holds at every due list of
                   challenges; On follows from every thread. AND, FREE OF ANY BOOK: every side of the
                   row has fits and exact
  clear_of_idle, clear_of_no_entry, clear_of_ok_at, clear_of_lotsOk   roads to that premise: nobody
                   spends a coin of the sender; the public test lotsOkB at that one sender; the same
                   test over all owners of the book
  rows_52          there are 52 rows, at 52 places
  rows_never_stop  the sender has no first and no second stop
  due_at_return, side_at_return   the premises inside the clauses can be met: a list of challenges is
                   due; each row has a side, Seated at its job, whose rounds can draw a list

Why two values and not sendLots. sendLots wit no D has one D and a fixed wit and no. In the filling
the two lots have two data (lotData S; K13.wDataAt O.pile), and the reader and the numbers hang on
the public part. The laws are those of Johnson/SendSim/, called once for each lot.

On := True is earned, not laid: the sender spends and carries nothing and never stops, and exact at
that On is had from Seated alone, at every state and any two data (sendExactAt,
Johnson/SendSim/At/ExactAt.lean). So K1's On hangs on nobody's plays.

Teeth, in the ground. exact's equation fails where a seed's factor is 0 and where one position too
many is read, at small places: said here without a theorem; no theorem of this folder shows it. The
test behind bud rejects one position more at a tree (readsW_rejects,
Johnson/SendSim/Seat/ReadsAtWritten.lean, at the written numbers).

Who calls. The step from the kinds' lots to Owed (KindPays at the kind K1, BudDebts, OnDebts) and,
beneath it, file_owed_rows. KindPays at K1 also runs over the shared chain, where the kind has two
more places: these rows are not here.

Limits. Good is had at predicates A₁, B₁ that never hold: its fields plays and acc are met for
nothing; fits, exact and fresh alone say something. THE PREMISE ON THE BOOK STANDS IN
handIn_at_return, job by job: until it is paid at the maker's own book at a job's sender, Good is not
had at that job's row.
That the maker returns at the filling, and that some public files pass both tests, is not shown
here: where it does not return, handIn_at_return and rows_52 say nothing. That A.F is the description
that the online prover plays is not shown here. exact and fresh speak of one sender at a time, at lists
of challenges that its rounds can draw and at positions within budAt. The first chain alone: the
kind has two more sendings on the shared chain, five in the key file's description and one in a
copy's. One request. All limits of Johnson/SendSim/Seat/AtDescLots.lean. No property of the
protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.SendSim.Seat.ReadsAtLive
import Johnson.SendSim.Seat.AtDescLotsProof
import Johnson.SendSim.Seat.AtDescLotsSpenders
import Johnson.SendSim.Seat.LotsGuardTie
import Johnson.SendSim.Seat.LotCount
import Johnson.SendSim.Seat.LotPlaces
import Johnson.SendSim.Seat.LotsPublic
import Johnson.SendSim.Seat.DueAtLive
import Johnson.SendSim.At.DrawsSome

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1.Sim
open VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open ProofFile.Honest.AtPlace (alone_gives of_find k13_m4_alone)

variable {W₀ W₀' Rc' : Type}

/-! ## 1 The two values -/

/-- **How a job reads the prover's input**: the public instance; the trace; the index through g and
the filling's reader at the public part; the stored tables' randomness through rd. -/
def witAt (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (Zp : Pub) :
    Local W₀' Rc' Inst Cells → PlaceIn Inst :=
  fun v => ⟨v.x, ⟨v.trace, I.weights Zp (g v.w₀), rd v.rc⟩⟩

/-- **K1's own lot with its simulators**: the first segment's opening, each link's reads and
digits. -/
def lotS (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) :
    SLot (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst :=
  ⟨"K1: the first segment's opening, each link's reads and digits",
    fun Zp G => (lotJobs (lotNo o Zp) (lotData S) Zp G).map (jobRow (witAt I g rd Zp))⟩

/-- **The sending of W with its simulator.** -/
def wS (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) :
    SLot (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst :=
  ⟨"K1 and K13: W's commitment, the request's own group and the row (Eval)",
    fun Zp G => (wJobs (lotNo o Zp) (K13.wDataAt O.pile) Zp G).map (jobRow (witAt I g rd Zp))⟩

/-! ## 2 They are the filling's own -/

/-- A row's half is the honest side's half, read through. -/
theorem half_thru {V V' W W' X Xi Pb : Type} (see : V' → V) (t : W' → W) (wit : W → PlaceIn Xi)
    (J : SendJob (PlaceIn Xi) X) :
    (jobRow (V := V') (Pb := Pb) (wit ∘ t) J).half = (placeHalf (V := V) wit J).thru see t := rfl

/-- **Without the simulators, lotS is the filling's first lot.** -/
theorem lotS_toHLot (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (lotS I g rd o S).toHLot =
      (HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k1).thru (Local.thru g rd)
        (Local.thru g rd) := by
  refine HLot.ext' rfl (funext fun Zp => funext fun G => ?_)
  have e1 : (lotS I g rd o S).toHLot.halves Zp G =
      ((lotJobs (lotNo o Zp) (lotData S) Zp G).map (jobRow (witAt I g rd Zp))).map
        Unlettered.half := rfl
  have e2 : ((HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k1).thru (Local.thru g rd)
      (Local.thru g rd)).halves Zp G =
      (lotHalves (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights Zp v.w₀, v.rc⟩⟩)
        (lotNo o Zp) (lotData S) Zp G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) := rfl
  rw [e1, e2, lotHalves_eq, List.map_map, List.map_map]
  exact List.map_congr_left fun J _ => rfl

/-- **Without the simulator, wS is the filling's last lot.** -/
theorem wS_toHLot (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (O : OnlineProverArguments) :
    (wS I g rd o O).toHLot =
      (wLotAt (X := Unit) I o O).thru (Local.thru g rd) (Local.thru g rd) := by
  refine HLot.ext' rfl (funext fun Zp => funext fun G => ?_)
  have e1 : (wS I g rd o O).toHLot.halves Zp G =
      ((wJobs (lotNo o Zp) (K13.wDataAt O.pile) Zp G).map (jobRow (witAt I g rd Zp))).map
        Unlettered.half := rfl
  have e2 : ((wLotAt (X := Unit) I o O).thru (Local.thru g rd) (Local.thru g rd)).halves Zp G =
      (wHalves (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights Zp v.w₀, v.rc⟩⟩)
        (lotNo o Zp) (K13.wDataAt O.pile) Zp G).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := rfl
  rw [e1, e2, wHalves_eq, List.map_map, List.map_map]
  exact List.map_congr_left fun J _ => rfl

/-- **Where the two lie in the filling's list**: the first and the last. -/
theorem lots_split (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots =
      (lotS I g rd o S).toHLot ::
        (((widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]).map
          (HLot.thru (Local.thru g rd) (Local.thru g rd)) ++ [(wS I g rd o O).toHLot]) := by
  rw [lotS_toHLot I g rd o S O, wS_toHLot]
  show (onlineProverPartsInUse I o S O).lots.map _ = _
  rw [widerFillAtCPUOWM_lots]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]
  rfl

/-- **No other lot of the base filling has a half at a place of the kind K1.** -/
theorem others_not_k1_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zp : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S],
      ∀ x ∈ M.halves Zp G, x.place.kind ≠ .K1 := by
  intro M hM x hx e
  rcases List.mem_append.1 hM with h | h
  · have h' : M ∈ ((widerPairs I o S O).tail).map (·.1) := h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h'
    have hk := (FirstFill.widerKinds I o S O Zp G).all q (List.mem_of_mem_tail hq) x hx
    have hn : (KindName.K1 :: (widerPairs I o S O).tail.map (·.2)).Nodup :=
      widerPairs_nodup (I := I) (o := o) (S := S) (O := O)
    refine (List.nodup_cons.1 hn).1 ?_
    rw [← e, hk]
    exact List.mem_map.2 ⟨q, hq, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · have hk := closeLotAt_kinds I S Zp G x hx
      rw [e] at hk
      cases hk
    · have hk := proxLotAt_kinds I S Zp G x hx
      rw [e] at hk
      cases hk

/-- **No other lot of the filling read through has a half at a place of the kind K1.** -/
theorem others_not_k1 (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zp : Pub) (G : Ground) :
    ∀ M ∈ ((widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]).map
        (HLot.thru (Local.thru g rd) (Local.thru g rd)),
      ∀ x ∈ M.halves Zp G, x.place.kind ≠ .K1 := by
  intro M hM x hx
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
  obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.1 (show x ∈ (M₀.halves Zp G).map _ from hx)
  exact others_not_k1_base I o S O Zp G M₀ hM₀ x₀ hx₀

/-! ### The same at the base filling, not read through -/

/-- **Without the simulators, lotS at the identities is the base filling's first lot.** -/
theorem lotS_toHLot_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    (lotS I id id o S).toHLot = HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k1 := by
  refine HLot.ext' rfl (funext fun Zp => funext fun G => ?_)
  have e1 : (lotS I id id o S).toHLot.halves Zp G =
      ((lotJobs (lotNo o Zp) (lotData S) Zp G).map (jobRow (witAt I id id Zp))).map
        Unlettered.half := rfl
  have e2 : (HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k1).halves Zp G =
      lotHalves (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights Zp v.w₀, v.rc⟩⟩)
        (lotNo o Zp) (lotData S) Zp G := rfl
  rw [e1, e2, lotHalves_eq, List.map_map]
  exact List.map_congr_left fun J _ => rfl

/-- **Without the simulator, wS at the identities is the base filling's last lot.** -/
theorem wS_toHLot_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) :
    (wS I id id o O).toHLot = wLotAt (X := Unit) I o O := by
  refine HLot.ext' rfl (funext fun Zp => funext fun G => ?_)
  have e1 : (wS I id id o O).toHLot.halves Zp G =
      ((wJobs (lotNo o Zp) (K13.wDataAt O.pile) Zp G).map (jobRow (witAt I id id Zp))).map
        Unlettered.half := rfl
  have e2 : (wLotAt (X := Unit) I o O).halves Zp G =
      wHalves (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights Zp v.w₀, v.rc⟩⟩)
        (lotNo o Zp) (K13.wDataAt O.pile) Zp G := rfl
  rw [e1, e2, wHalves_eq, List.map_map]
  exact List.map_congr_left fun J _ => rfl

/-- **Where the two lie in the base filling's list**: the first and the last. -/
theorem lots_split_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    (onlineProverPartsInUse I o S O).lots =
      (lotS I id id o S).toHLot ::
        (((widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]) ++
          [(wS I id id o O).toHLot]) := by
  rw [lotS_toHLot_base I o S O, wS_toHLot_base, widerFillAtCPUOWM_lots]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-! ### Among the rows of all lots, those at places of the kind K1 are these -/

/-- Between two lots lie lots none of whose halves stands at a place of the kind K1: then a row of
the whole list at such a place is a row of the two. -/
theorem rows_only {V W X Pb : Type} {a b : SLot V W X Pb} {mid : List (SLot V W X Pb)} {Zp : Pub}
    {G : Ground} (hO : ∀ l ∈ mid, ∀ x ∈ l.toHLot.halves Zp G, x.place.kind ≠ .K1) :
    ∀ r ∈ rowsOfLots Zp G (a :: (mid ++ [b])), r.place.kind = .K1 →
      r ∈ rowsOfLots Zp G [a, b] := by
  intro r hr hk
  obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
  rcases List.mem_cons.1 hl with rfl | hl
  · exact List.mem_flatMap.2 ⟨_, List.Mem.head _, hrl⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact absurd hk (hO l hl r.half (List.mem_map.2 ⟨r, hrl, rfl⟩))
  · obtain rfl := List.mem_singleton.1 hl
    exact List.mem_flatMap.2 ⟨_, List.Mem.tail _ (List.Mem.head _), hrl⟩

/-- **WHOEVER LAYS ALL THE FILLING's LOTS WITH SIMULATORS, OURS FIRST AND LAST: EVERY ROW AT A PLACE
OF THE KIND K1 IS ONE OF OUR 52.** mid: the other houses' lots, whose halves are the filling's. -/
theorem k1_rows_only (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zp : Pub) (G : Ground)
    (mid : List (SLot (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst))
    (hm : mid.map SLot.toHLot =
      ((widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]).map
        (HLot.thru (Local.thru g rd) (Local.thru g rd))) :
    ∀ r ∈ rowsOfLots Zp G (lotS I g rd o S :: (mid ++ [wS I g rd o O])), r.place.kind = .K1 →
      r ∈ rowsOfLots Zp G [lotS I g rd o S, wS I g rd o O] :=
  rows_only fun l hl => others_not_k1 I g rd o S O Zp G _ (hm ▸ List.mem_map.2 ⟨l, hl, rfl⟩)

/-- The same at the base filling. -/
theorem k1_rows_only_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zp : Pub) (G : Ground)
    (mid : List (SLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit Inst))
    (hm : mid.map SLot.toHLot =
      (widerFillAt I o S O).lots.tail ++ [closeLotAt I S, proxLotAt I S]) :
    ∀ r ∈ rowsOfLots Zp G (lotS I id id o S :: (mid ++ [wS I id id o O])), r.place.kind = .K1 →
      r ∈ rowsOfLots Zp G [lotS I id id o S, wS I id id o O] :=
  rows_only fun l hl => others_not_k1_base I o S O Zp G _ (hm ▸ List.mem_map.2 ⟨l, hl, rfl⟩)

/-! ## 3 At what the maker returns -/

section
variable {Rc Tr X₀ X : Type}

/-- **What onlineProverFromPublicFiles returns can be opened**, at its own public part, ground and description. -/
theorem open_at {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ Bs base c S₂ S₃, IM.Open o pol lay KL A.F A.Z Bs base c S₂ S₃ ∧ Bs.G₀ = A.G := by
  obtain ⟨m, -⟩ := K5.parts_of_atPure hA
  obtain ⟨Z', Bs, base, c, S₂, S₃, O⟩ := IM.seat_open m.desc
  obtain rfl : Z' = A.Z := Except.ok.inj (O.pub.symm.trans m.pub)
  exact ⟨Bs, base, c, S₂, S₃, O, Option.some.inj (O.blank.symm.trans m.ground)⟩

end

/-- **The 52 jobs**, at the filling's own numbers and data: K1's own lot's, then W's. -/
def k1Jobs (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zp : Pub) (G : Ground) :
    List (SendJob (PlaceIn Inst) Unit) :=
  lotJobs (lotNo o Zp) (lotData S) Zp G ++ wJobs (lotNo o Zp) (K13.wDataAt O.pile) Zp G

/-- **The rows of the two values are jobRow at the 52 jobs**, in order. -/
theorem rows_eq (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zp : Pub) (G : Ground) :
    rowsOfLots Zp G [lotS I g rd o S, wS I g rd o O] =
      (k1Jobs o S O Zp G).map (jobRow (witAt I g rd Zp)) := by
  show (lotJobs _ _ _ _).map _ ++ ((wJobs _ _ _ _).map _ ++ []) = _
  rw [List.append_nil, k1Jobs, List.map_append]

/-- A job of the two lists has its row among the rows of sendLots. -/
theorem row_mem {V W X Xi Pb : Type} (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Zp : Pub) (G : Ground) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Zp G ++ wJobs no D Zp G) :
    jobRow (V := V) (Pb := Pb) wit J ∈ rowsOfLots Zp G (sendLots wit no D) := by
  unfold rowsOfLots sendLots
  rcases List.mem_append.1 hJ with h | h
  · exact List.mem_flatMap.2 ⟨_, List.Mem.head _, List.mem_map.2 ⟨J, h, rfl⟩⟩
  · exact List.mem_flatMap.2 ⟨_, List.Mem.tail _ (List.Mem.head _), List.mem_map.2 ⟨J, h, rfl⟩⟩

/-- Each of the 52 jobs is a job of the two lists at ONE datum: its own lot's. -/
theorem job_mem {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {Zp : Pub} {G : Ground}
    {J : SendJob (PlaceIn Inst) Unit} (hJ : J ∈ k1Jobs o S O Zp G) :
    ∃ D : Pub → Ground → RowDataOf Inst,
      J ∈ lotJobs (lotNo o Zp) D Zp G ++ wJobs (lotNo o Zp) D Zp G := by
  rcases List.mem_append.1 hJ with h | h
  · exact ⟨_, List.mem_append_left _ h⟩
  · exact ⟨_, List.mem_append_right _ h⟩

/-- **IN SCOPE, WHERE THE GATE ACCEPTS, AT WHAT THE MAKER RETURNS (AT ANY FILLING P: the public part,
the ground and the description that it returns do not hang on P): JOB BY JOB, THE FOUR PREMISES THAT
THE RULE ASKS OF A ROW, AND, FREE OF ANY BOOK, fits AND exact.** Good for some A₁ and B₁ holds at a
job if the book is clear AT THAT JOB's SENDER, at the addresses that spend a coin of it
(SpendersClearAny, Johnson/SendSim/At/SpendersAlone.lean): a premise on that one owner's entries,
which fresh alone spends. All other clauses hold with no further premise. -/
theorem handIn_at_return {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} {Z : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (φ : Face (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Inst) (Bk : ProverCoinCounts)
    (ord : List Place) (chain ft : Nat)
    (T : Local W₀' Rc' Inst Cells → Thread Bk A.F.S₁ A.F.Cl (Local W₀' Rc' Inst Cells)
      (Local W₀' Rc' Inst Cells) Unit Inst)
    (Sd : Local W₀' Rc' Inst Cells → Nat → Coins Bk → Mid (Local W₀' Rc' Inst Cells) Unit → Prop)
    (fs : List (Fall A.F.S₁)) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G,
      ∀ r : Unlettered (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst,
      r = jobRow (witAt I g rd A.Z) J →
      A.F.first.blocksInOrder.any (fun b => b.place == r.place) = true ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
        σ.fits = true ∧ ExactAt φ σ chain ft r.On r.bud) ∧
      (SpendersClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
        ∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
          ∃ A₁ B₁, Good pre₀ φ σ Bk ord chain ft A₁ B₁ (r.lay T Sd A.F.first.blocksInOrder).On
            (r.lay T Sd A.F.first.blocksInOrder).bud) ∧
      (∀ σ, (r.lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
        A.F.first.blocksInOrder = pre ++ σ.block :: t →
        n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
        ∀ ρ : ProofFile.Honest.Draws, ρ.due A.F = true →
        (r.lay T Sd A.F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
          (asksFrom (treeAsks A.F ρ 0) (u.rounds.map (·.2.length))
            (((rowsOfChain A.F.first.blocksInOrder).take n).map (·.2.length)).sum)) ∧
      ∀ w b len, OnFromS (T w) (Sd w) (r.lay T Sd A.F.first.blocksInOrder) b len := by
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  rw [← hG]
  rintro J hJ r rfl
  obtain ⟨D, hD⟩ := job_mem hJ
  have H := handIn_of_live (pre₀ := pre₀) hS hL Op φ (witAt I g rd A.Z) (lotNo OnBytes.secondHashFunction A.Z) D
    Bk ord chain ft T Sd fs _ (row_mem _ _ D A.Z Bs.G₀ hD)
  obtain ⟨-, h⟩ := fieldsAtLots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Op φ (witAt I g rd A.Z)
    (lotNo OnBytes.secondHashFunction A.Z) D chain ft fs J hD
  refine ⟨H.1, fun σ hσ => ⟨(h σ hσ).1, (h σ hσ).2.1⟩, fun hB σ hσ => ?_, H.2.2.1, H.2.2.2⟩
  obtain ⟨hf, he, -⟩ := h σ hσ
  exact ⟨_, _, good_of_fields hf he
    (freshAtLots_of_spenders Op φ (witAt I g rd A.Z) (lotNo OnBytes.secondHashFunction A.Z) D hD hσ Bk ord hB)⟩

/-- **The premise at a job whose sender lends nothing**: where no address spends a coin of it. -/
theorem clear_of_idle {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place}
    {a : Addr} (h0 : ∀ p, Bk.spentBy a p = []) : SpendersClearAny P ride Bk ord a :=
  fun p hp => absurd (h0 p) hp

/-- **The premise at a job of whose sender no entry of the book spends a coin.** -/
theorem clear_of_no_entry {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place}
    {a : Addr} (h : ∀ e ∈ Bk.ahead, e.once = true → e.owner ≠ a) :
    SpendersClearAny P ride Bk ord a :=
  clear_of_idle (spentBy_nil_of_no_spending h)

/-- **The premise at ONE job, from the public test at that job's own sender.** The test accepts
there exactly if BookClearAny holds at that sender (lotsOkB_at, ownerOkB_iff); SpendersClearAny, in
which this theorem ends, is the weaker of the two. -/
theorem clear_of_ok_at {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {Zp : Pub}
    {G : Ground} {Bk : ProverCoinCounts} {ord : List Place} {J : SendJob (PlaceIn Inst) Unit}
    (hJ : J ∈ k1Jobs o S O Zp G) (h : lotsOkB Zp G Bk ord ⟨J.P.place, 0⟩ = true) :
    SpendersClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ := by
  obtain ⟨D, hD⟩ := job_mem hJ
  exact spendersClearAny_of_bookClearAny (clear_at_jobs (lotNo o Zp) D h J hD rfl)

/-- **The premise at all 52 jobs at once, from the one public test over the book's owners.** -/
theorem clear_of_lotsOk {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {Zp : Pub}
    {G : Ground} {Bk : ProverCoinCounts} {ord : List Place}
    (hBook : ∀ e ∈ Bk.ahead, e.once = true → lotsMine Zp G e.owner = true →
      lotsOkB Zp G Bk ord e.owner = true) :
    ∀ J ∈ k1Jobs o S O Zp G, SpendersClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ := by
  intro J hJ
  obtain ⟨D, hD⟩ := job_mem hJ
  exact spendersClear_all (lotNo o Zp) D hBook J hD

/-- **THERE ARE 52 ROWS, AT 52 PLACES.** -/
theorem rows_52 {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (rowsOfLots A.Z A.G [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O]).length = 52 ∧
      ((rowsOfLots A.Z A.G [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O]).map
        (·.place)).Nodup := by
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  rw [← hG]
  have e : (rowsOfLots A.Z Bs.G₀ [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O]).map
      (·.place) =
      (lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z Bs.G₀ ++
        wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z Bs.G₀).map (·.P.place) := by
    have p := congrArg (List.map fun x : K1.Par × Nat × (Nat → Option Ride) => x.1.place)
      (jobs_public (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) (K13.wDataAt O.pile) A.Z
        Bs.G₀)
    simp only [List.map_append, List.map_map] at p
    have p2 := List.append_inj p (by
      rw [List.length_map, List.length_map, lotJobs_length, lotJobs_length])
    rw [rows_eq, k1Jobs, List.map_map, List.map_append, List.map_append]
    exact congrArg₂ _ rfl p2.2.symm
  refine ⟨?_, ?_⟩
  · have l := congrArg List.length e
    rw [List.length_map, List.length_map] at l
    rw [l]
    exact jobs_52_in_scope hS hR Op _ _
  · rw [e]
    exact jobPlaces_nodup _ _ _ _

/-- **No row of ours ever stops**: the sender has neither a first nor a second stop. -/
theorem rows_never_stop {V W X Xi Pb : Type} (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) :
    ∀ x ∈ (jobRow (V := V) (Pb := Pb) wit J).row,
      (∀ a b, x.1.bad a b = none) ∧ ∀ a b c, x.1.hid a b c = none := by
  intro x hx
  obtain rfl := List.mem_singleton.1 hx
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## 4 The premises inside the clauses can be met -/

/-- **A list of challenges is due at the returned description**: the clause on bud speaks of
something. -/
theorem due_at_return {Z : VerifierAndGoals.PublicFiles} (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (Draws.ofDecl A.F).due A.F = true :=
  due_of_live hL (K5.parts_of_atPure hA).1.desc

/-- **The rounds of the side that is seated at a job are K1's own two at the job's numbers.** -/
theorem rounds_at_job {V W X Xi Pb : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription Inst} {Zp : Pub} {Bs : PureBase} {base : List (Block First.S Cl)}
    {c : Chain First.S Cl} {S₂ : SharedSeat} {S₃ : SecondSeat}
    (Op : IM.Open o pol lay KL F Zp Bs base c S₂ S₃) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Zp Bs.G₀ ++ wJobs no D Zp Bs.G₀) {fs : List (Fall F.S₁)}
    {σ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (jobRow (V := V) (Pb := Pb) wit J).place
      (jobRow (V := V) (Pb := Pb) wit J).row fs = some σ) :
    σ.block.rounds = K1.rounds J.P := by
  have e := Op.desc
  subst e
  obtain ⟨hm, hp⟩ := of_find (find_of_seated hσ)
  rcases List.mem_append.1 hJ with hJ | hJ
  · obtain ⟨b₀, hown, hpl, hr, -⟩ := own_of_job no D Zp Bs.G₀ hJ
    exact (member_of_own Op hown hm (hp.trans hpl.symm)).1.trans hr
  · obtain ⟨msg, hmsg, rfl⟩ := w_of_job no D Zp Bs.G₀ hJ
    obtain ⟨h1, -, -⟩ := w_member (X := X) Zp.first (wGp Zp) 4 (no ⟨1, none, 4, .K1⟩) msg
      (D Zp Bs.G₀) _ (K13.whereOf Zp) hmsg
      (show K1.wAt Zp.first (wGp Zp) 4 = some _ from wBlock_of_msg hmsg)
    obtain ⟨x, hF, hA⟩ := k13_m4_alone Op (wBlock_of_msg hmsg) hm hp
    obtain ⟨-, -, hr, -, -⟩ := alone_gives _ x _ _ _ _ hF hA
    exact hr.trans h1

/-- **Every one of the 52 rows has a side at the returned description**; that side is Seated at the
row's job, and ITS OWN rounds can draw a list of challenges. -/
theorem side_at_return {Z : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {P : OnlineProverParts W₀' Rc' Cells Unit Unit}
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (fs : List (Fall A.F.S₁)) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G,
      ∃ σ : Side A.F.S₁ A.F.Cl (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst,
        Side.seated A.F.first.blocksInOrder (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                     (witAt I g rd A.Z) J).place (jobRow (witAt I g rd A.Z) J).row fs = some σ ∧
          Seated σ (jobOver J (witAt I g rd A.Z)) ∧
          ∃ ds, drawsFit σ.block.rounds ds = true := by
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  rw [← hG]
  intro J hJ
  obtain ⟨D, hD⟩ := job_mem hJ
  obtain ⟨m, hm, hp⟩ := stands_at_job Op (lotNo OnBytes.secondHashFunction A.Z) D hD
  cases hf : A.F.first.blocksInOrder.find? fun b => b.place == J.P.place with
  | none => exact absurd (beq_iff_eq.2 hp) (List.find?_eq_none.1 hf m hm)
  | some b =>
    have hσ : Side.seated A.F.first.blocksInOrder (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                 (witAt I g rd A.Z) J).place (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                 (witAt I g rd A.Z) J).row fs =
        some { block := b
               row := (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                 (witAt I g rd A.Z) J).row
               fall := fallOf fs J.P.place } := by
      unfold Side.seated
      exact congrArg (Option.map _) hf
    refine ⟨_, hσ, seatedAt_job Op (witAt I g rd A.Z) (lotNo OnBytes.secondHashFunction A.Z) D hD hσ, ?_⟩
    rw [rounds_at_job Op (witAt I g rd A.Z) (lotNo OnBytes.secondHashFunction A.Z) D hD hσ]
    exact draws_some J.P

end ProofFile.Honest.K1.Sim

#print axioms ProofFile.Honest.K1.Sim.half_thru
#print axioms ProofFile.Honest.K1.Sim.lotS_toHLot
#print axioms ProofFile.Honest.K1.Sim.wS_toHLot
#print axioms ProofFile.Honest.K1.Sim.lots_split
#print axioms ProofFile.Honest.K1.Sim.others_not_k1_base
#print axioms ProofFile.Honest.K1.Sim.others_not_k1
#print axioms ProofFile.Honest.K1.Sim.lotS_toHLot_base
#print axioms ProofFile.Honest.K1.Sim.wS_toHLot_base
#print axioms ProofFile.Honest.K1.Sim.lots_split_base
#print axioms ProofFile.Honest.K1.Sim.rows_only
#print axioms ProofFile.Honest.K1.Sim.k1_rows_only
#print axioms ProofFile.Honest.K1.Sim.k1_rows_only_base
#print axioms ProofFile.Honest.K1.Sim.open_at
#print axioms ProofFile.Honest.K1.Sim.rows_eq
#print axioms ProofFile.Honest.K1.Sim.row_mem
#print axioms ProofFile.Honest.K1.Sim.job_mem
#print axioms ProofFile.Honest.K1.Sim.clear_of_idle
#print axioms ProofFile.Honest.K1.Sim.clear_of_no_entry
#print axioms ProofFile.Honest.K1.Sim.clear_of_ok_at
#print axioms ProofFile.Honest.K1.Sim.clear_of_lotsOk
#print axioms ProofFile.Honest.K1.Sim.handIn_at_return
#print axioms ProofFile.Honest.K1.Sim.rows_52
#print axioms ProofFile.Honest.K1.Sim.rows_never_stop
#print axioms ProofFile.Honest.K1.Sim.due_at_return
#print axioms ProofFile.Honest.K1.Sim.rounds_at_job
#print axioms ProofFile.Honest.K1.Sim.side_at_return
