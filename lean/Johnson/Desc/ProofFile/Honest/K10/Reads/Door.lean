-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Reads/Door.lean: the closing of a segment (K10): what the honest prover's parts at the
kind's places read of the prover's input. A fact on texts, stated as equations between the values of functions at two
inputs. Twenty-one theorems; no definition. The form is that of Honest/K2/Law/SwitchPartsEntry.lean, for the kind K2.

Terms (Honest/Frame.lean). A lot's honest side (`HLot`) lists halves; a half (`Placed`) is a list of parts at one place;
a part has one move for each of its rounds, and two stops. A move has two fields. `say` yields the round's message or a
refusal (`Except String Sending`), from the coins, what was shown, and the state. `hand` yields what is passed on, from
the state. The state holds the input, the challenges heard, and what the parts pass on. "Says and hands the same at two
inputs" means: at all coins, all that was shown, all that was heard and all that was passed on, both fields return the
same at the two states that differ in the input alone; for `say` the equation is between the two results as wholes, so
a refusal and its words are covered. The input (`Local`) has four fields: w₀, rc, x (the public instance), trace.

The two lots. `seatLotC readers rows stAt` (Honest/K10/SeatLotC.lean) lays the closings alone; `seatLotT`
(SeatLotT.lean) lays K9's own halves in front of them. The three parameters are arbitrary here: readers (from the input
to the record `Readers`, Honest/RowData.lean), rows (the main rows' data, a function of the instance), stAt (the
statement in front of the round "BAT", a function of the instance).

How the input reaches a move. A half of `seatLotC` has one part: the round "BAT", then the fold's part, lifted
(`seatFold`, Honest/K10/Seat.lean). A lifted move is handed the input through one function, which yields a small record
(`CloseIn`: readers, data, st); at the lot that function is `closeIn readers rows stAt`. The small record holds the
readers whole, so it is not the same record at two inputs whose readers differ. Hence two steps.
  Step 1 (`seatClosings_of_fold`, `seatClosings_of_in`): the moves depend on the input through the small record alone,
  whatever the fold's part is.
  Step 2 (`foldAtT_of_own`): the moves of the lot's fold return the same at two small records that have the same data,
  the same st, and the same function `ownBy data readers` (Honest/K2/AtPlan.lean), whatever else the readers hold.
At `closeIn`, data and st are functions of x. `ownBy` is the same at two readers at which the data's field `entry` is
the same (`ownBy_of_entry`, SwitchPartsEntry.lean). The two steps joined: `seatLotC_of_entry`.

A job (`CloseJob`, Honest/K10/Job.lean) at two inputs
  `closeAsk_of_job`, `closeAskAt_of_job`, `askOr_of_job`   where a job's fields `stAt` and `rows` each return the same
                    function at two inputs, the three functions that make the fold's data return the same there
  `foldShellT_of_job`   so each move of the part at that job (`foldShellT`, Honest/K10/Sim.lean) says and hands the same
The lot's job (`jobAt`, Honest/K10/SeatLot.lean) at two small records
  `jobRows_of_own`    `jobRows` (Honest/K10/SegmentClosing.lean): where its parameter `own` is the same at two inputs, so is
                    its field `rows`
  `jobAt_of_own`      at two small records with the same data, the same statement and the same `ownBy data readers`,
                    the lot's job has the same `stAt` and the same `rows`
  `foldAtT_of_own`    step 2
The lifted part; the function to the small record and the fold's part are arbitrary
  `closePart_of_fold`   laying the round "BAT" in front keeps "says and hands the same"
  `seatFold_of_fold`    where the fold's moves say the same at the two small records, the lifted moves say and hand the
                    same at the two inputs
  `seatClosings_of_fold`   so at each move of each part of each half
  `seatClosings_of_in`   where the small record is the same at the two inputs, the premise is met by every fold's part
The lot with the closings alone
  `seatLotC_of_own`   at two inputs with the same x at whose readers `ownBy` at the data is the same
  `seatLotC_of_entry` at two inputs with the same x at whose readers the data's `entry` is the same
The two stops. The first stop (`bad`) is handed challenges alone; the second (`hid`) is handed the input too
  `stopBoth_of_none`, `closePart_stops_none`, `seatClosings_stops_none`   two stops that always return `none`, joined by
                    `stopBoth` (Frame.lean), always return `none`; so with "BAT" in front; so at each part of each half
  `seatLotC_stops_none`   at each part of each half of the lot both stops return `none` at every argument; no premise
The lot with K9's own halves in front
  `batHalves_idle`, `batHalves_stops_none`   each move of K9's own halves (`K9.batHalves`, Honest/K9/Part.lean) says and
                    hands the same at any two inputs; both stops always return `none`
  `seatLotT_of_entry`, `seatLotT_stops_none`   `seatLotC_of_entry` and `seatLotC_stops_none` at `seatLotT`

By: `ownBy_of_entry` (Honest/K2/Law/SwitchPartsEntry.lean); `seatLotT_is` (Honest/K10/SeatLotC.lean).

Limits. Equations on what functions return: nothing on any run or on what a view holds. The three equations at the lots
are at two inputs with the same x; of these lots' closings at two inputs with different x nothing is said. Which fields
of the readers a filling's `entry` reads is not said here: Honest/K10/Reads/Cells.lean says it of one filling. The
part's coins (its own, the spent, the carried) are no part of the input: they are a move's first argument, which is the
same variable on both sides. What was shown (`Seen`), what was heard and what was passed on are likewise the same
variables on both sides. What was shown is the rounds, which the parts in front write, and, where they are handed, the
columns opened so far, of these parts' tables and of the stored tables. The fold's moves read the rounds and are handed
the columns (`closeCut`, Honest/K10/Job.lean). That two runs at two inputs show the same in front of a move is not said
here: it would need the like of every part in front, and, for the columns, the like of the stored tables and of the
positions that the challenges open. Of the input `stAt` is handed x alone, by type. The `Seen` that it is handed too
holds, where they are handed, opened columns: that no filler reads these is by the fillers' text: the weaker ground.
What the term that is laid for it closes over no type says. The fillers: `stAtFirst` (Honest/K10/StAt.lean), `stAtZero`
(Honest/K10/StAtZero.lean). The part's other five fields (takes, spends, carries, badShare, hidShare) are no functions
of an input, by type. That a prover's filling lays one of these lots is not said here. Of the lot with the older caller
(`seatLotR`, Honest/K10/SeatLot.lean) nothing. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SeatLotC
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchPartsEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

variable {V W X W₀ Rc Xi Tr : Type}

/-! ## A job at two inputs -/

/-- Where a job's `stAt` and `rows` are each the same at two inputs, `closeAsk` is the same function there. -/
theorem closeAsk_of_job (J : CloseJob W) {w w' : W} (hs : J.stAt w = J.stAt w')
    (hr : J.rows w = J.rows w') : closeAsk J w = closeAsk J w' := by
  funext seen front x u ca
  unfold closeAsk
  rw [hs, hr]

/-- So `closeAskAt` returns the same at two states that have heard the same and at whose inputs the two fields are the
same. -/
theorem closeAskAt_of_job (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t t' : State W X)
    (hh : t.heard = t'.heard) (hs : J.stAt t.input = J.stAt t'.input)
    (hr : J.rows t.input = J.rows t'.input) : closeAskAt J n c s t = closeAskAt J n c s t' := by
  have hc : closeCut n s t = closeCut n s t' := by
    unfold closeCut
    rw [hh]
  have hl : t.lately n = t'.lately n := by
    unfold State.lately
    rw [hh]
  unfold closeAskAt
  dsimp only
  rw [hc, hl, hh, closeAsk_of_job J hs hr]

/-- So does `askOr`, at both values of tot. -/
theorem askOr_of_job (tot : Bool) (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t t' : State W X)
    (hh : t.heard = t'.heard) (hs : J.stAt t.input = J.stAt t'.input)
    (hr : J.rows t.input = J.rows t'.input) : askOr tot J n c s t = askOr tot J n c s t' := by
  unfold askOr
  rw [closeAskAt_of_job J n c s t t' hh hs hr]

/-- Each move of the part at a job says and hands the same at two inputs at which the job's `stAt` and `rows` are each
the same. -/
theorem foldShellT_of_job (tot : Bool) (J : CloseJob W) (F : FoldWords) {w w' : W}
    (hs : J.stAt w = J.stAt w') (hr : J.rows w = J.rows w') :
    ∀ mv ∈ (foldShellT (V := V) (X := X) tot J F).moves, ∀ (heard : List Fmt.Drawn) (own : X),
      (∀ c s, mv.say c s ⟨w, heard, own⟩ = mv.say c s ⟨w', heard, own⟩) ∧
        mv.hand ⟨w, heard, own⟩ = mv.hand ⟨w', heard, own⟩ := by
  intro mv hmv heard own
  rcases List.mem_cons.1 hmv with rfl | hmv
  · refine ⟨fun c s => ?_, rfl⟩
    have e := askOr_of_job (X := X) tot J 0 c s ⟨w, heard, own⟩ ⟨w', heard, own⟩ rfl hs hr
    exact (congrArg (Except.map _) e :)
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hmv
    refine ⟨fun c s => ?_, rfl⟩
    have e := askOr_of_job (X := X) tot J (j + 1) c s ⟨w, heard, own⟩ ⟨w', heard, own⟩ rfl hs hr
    exact (congrArg (Except.map _) e :)

/-! ## The lot's job at two small records -/

/-- Where the parameter `own` is the same at two inputs, the field `rows` of `jobRows` is the same there. -/
theorem jobRows_of_own (pub : ClosePub) (table : ProofFile.Honest.K2.FreshTable)
    (segs : List ProofFile.Honest.K2.SegmentPub)
    (stAt : W → Seen → List Fmt.Drawn → Except String (OnBytes.Statement × Nat))
    (own : W → List Fmt.Drawn → Nat → Nat → Nat → Nat → Cb.Gl.E) {w w' : W} (h : own w = own w') :
    (jobRows pub table segs stAt own).rows w = (jobRows pub table segs stAt own).rows w' := by
  funext front ca
  unfold jobRows
  dsimp only
  rw [h]

/-- At two small records with the same data, the same statement and the same `ownBy data readers`, the lot's job has the
same `stAt` and the same `rows`. -/
theorem jobAt_of_own (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr)
    (segs : List ProofFile.Honest.K2.SegmentPub)
    (stAt : CloseIn → Seen → List Fmt.Drawn → Except String (OnBytes.Statement × Nat)) (pub : ClosePub)
    {I I' : CloseIn} (hd : I.data = I'.data) (hst : stAt I = stAt I')
    (ho : ProofFile.Honest.K2.ownBy I.data I.readers = ProofFile.Honest.K2.ownBy I'.data I'.readers) :
    (jobAt lay addrs segs stAt pub).stAt I = (jobAt lay addrs segs stAt pub).stAt I' ∧
      (jobAt lay addrs segs stAt pub).rows I = (jobAt lay addrs segs stAt pub).rows I' := by
  refine ⟨hst, ?_⟩
  have hb : (jobBare addrs segs stAt pub).rows I = (jobBare addrs segs stAt pub).rows I' := by
    unfold jobBare
    refine jobRows_of_own _ _ _ _ _ ?_
    show (fun heard => ProofFile.Honest.K2.ownBy I.data I.readers addrs _ heard) =
      fun heard => ProofFile.Honest.K2.ownBy I'.data I'.readers addrs _ heard
    rw [ho]
  funext front ca
  show (ProofFile.Honest.K2.ownReady I.data lay (askPlace addrs) segs front).bind _ =
    (ProofFile.Honest.K2.ownReady I'.data lay (askPlace addrs) segs front).bind _
  rw [hd, hb]

/-- **Step 2: the readers count through `ownBy` alone**: each move of the lot's fold says and hands the same at two
small records with the same data, the same st and the same `ownBy data readers`. -/
theorem foldAtT_of_own (Z : Pub) (G : Ground) (pub : ClosePub) {I I' : CloseIn} (hd : I.data = I'.data)
    (hst : I.st = I'.st)
    (ho : ProofFile.Honest.K2.ownBy I.data I.readers = ProofFile.Honest.K2.ownBy I'.data I'.readers) :
    ∀ mv ∈ (foldAtT (V := V) (X := X) Z G pub).moves, ∀ (heard : List Fmt.Drawn) (own : X),
      (∀ c s, mv.say c s ⟨I, heard, own⟩ = mv.say c s ⟨I', heard, own⟩) ∧
        mv.hand ⟨I, heard, own⟩ = mv.hand ⟨I', heard, own⟩ := by
  have h := jobAt_of_own G.first.layout (addrsAt Z G)
    ((ProofFile.Honest.K2.segmentsOf Z G).take (pub.par.link + 1)) (fun i : CloseIn => i.st pub.par) pub hd
    (congrArg (fun f : StAt => f pub.par) hst :) ho
  unfold foldAtT
  exact foldShellT_of_job true _ foldWords h.1 h.2

/-! ## The lifted part: the function to the small record and the fold's part are arbitrary -/

/-- Where each move of a part says and hands the same at two inputs, so does each move of that part with the round "BAT"
in front. -/
theorem closePart_of_fold (fold : Part V W X) {w w' : W}
    (h : ∀ mv ∈ fold.moves, ∀ (heard : List Fmt.Drawn) (own : X),
      (∀ c s, mv.say c s ⟨w, heard, own⟩ = mv.say c s ⟨w', heard, own⟩) ∧
        mv.hand ⟨w, heard, own⟩ = mv.hand ⟨w', heard, own⟩) :
    ∀ mv ∈ (closePart fold).moves, ∀ (heard : List Fmt.Drawn) (own : X),
      (∀ c s, mv.say c s ⟨w, heard, own⟩ = mv.say c s ⟨w', heard, own⟩) ∧
        mv.hand ⟨w, heard, own⟩ = mv.hand ⟨w', heard, own⟩ := by
  intro mv hmv heard own
  rcases List.mem_append.1 (show mv ∈ (closeBatPart (V := V) (W := W) (X := X)).moves.map _ ++
      fold.moves.map _ from hmv) with hm | hm
  · obtain ⟨m0, h0, rfl⟩ := List.mem_map.1 hm
    obtain rfl : m0 = _ := List.mem_singleton.1 h0
    exact ⟨fun _ _ => rfl, rfl⟩
  · obtain ⟨m0, h0, rfl⟩ := List.mem_map.1 hm
    exact ⟨fun _ s => (h m0 h0 heard own).1 _ s, (h m0 h0 heard own).2⟩

/-- Where the fold's moves say the same at the small records of two inputs, the lifted moves say and hand the same at
these inputs. -/
theorem seatFold_of_fold (inOf : Local W₀ Rc Xi Tr → CloseIn) (fold : ClosePub → Part Unit CloseIn Unit)
    (pub : ClosePub) {i i' : Local W₀ Rc Xi Tr}
    (h : ∀ m0 ∈ (fold pub).moves, ∀ (heard : List Fmt.Drawn) c s,
      m0.say c s ⟨inOf i, heard, ()⟩ = m0.say c s ⟨inOf i', heard, ()⟩) :
    ∀ mv ∈ (seatFold (X := X) inOf fold pub).moves, ∀ (heard : List Fmt.Drawn) (own : X),
      (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
        mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ := by
  intro mv hmv heard own
  obtain ⟨m0, h0, rfl⟩ := List.mem_map.1 hmv
  exact ⟨fun c s => h m0 h0 heard c s, rfl⟩

/-- **Step 1**: where the fold's moves say the same at the small records of two inputs, each move of each part of each
half says and hands the same at these inputs. -/
theorem seatClosings_of_fold (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (borne : Pub → VerifiableInference.Desc.First.Close.Par → List Borne)
    (fold : ClosePub → Part Unit CloseIn Unit) (Z : Pub) (G : Ground) {i i' : Local W₀ Rc Xi Tr}
    (h : ∀ pub, ∀ m0 ∈ (fold pub).moves, ∀ (heard : List Fmt.Drawn) c s,
      m0.say c s ⟨inOf i, heard, ()⟩ = m0.say c s ⟨inOf i', heard, ()⟩) :
    ∀ g ∈ seatClosings (X := X) inOf borne fold Z G, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ := by
  intro g hg
  obtain ⟨P, -, rfl⟩ := List.mem_map.1 (show g ∈ (closePars Z).map
    (fun P => closeHalf (seatFold (X := X) inOf fold) ⟨P, borne Z P⟩) from hg)
  intro q hq
  obtain rfl : q = _ := List.mem_singleton.1 hq
  exact closePart_of_fold (seatFold (X := X) inOf fold ⟨P, borne Z P⟩)
    (seatFold_of_fold inOf fold ⟨P, borne Z P⟩ (h ⟨P, borne Z P⟩))

/-- **Step 1, in short**: where the small record is the same at two inputs, each move of each part of each half says and
hands the same there, whatever the fold's part is. -/
theorem seatClosings_of_in (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (borne : Pub → VerifiableInference.Desc.First.Close.Par → List Borne)
    (fold : ClosePub → Part Unit CloseIn Unit) (Z : Pub) (G : Ground) {i i' : Local W₀ Rc Xi Tr}
    (hw : inOf i = inOf i') :
    ∀ g ∈ seatClosings (X := X) inOf borne fold Z G, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ :=
  seatClosings_of_fold inOf borne fold Z G fun _ _ _ _ _ _ => by rw [hw]

/-! ## The lot with the closings alone -/

/-- Each move of each part of each of the lot's halves says and hands the same at two inputs with the same x at whose
readers `ownBy` at the data is the same. -/
theorem seatLotC_of_own (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : Pub) (G : Ground) {i i' : Local W₀ Rc Xi Tr} (hx : i.x = i'.x)
    (ho : ProofFile.Honest.K2.ownBy (rows i'.x) (readers i) = ProofFile.Honest.K2.ownBy (rows i'.x) (readers i')) :
    ∀ g ∈ (seatLotC (X := X) readers rows stAt).halves Z G, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ := by
  have ho' : ProofFile.Honest.K2.ownBy (closeIn readers rows stAt i).data (closeIn readers rows stAt i).readers =
      ProofFile.Honest.K2.ownBy (closeIn readers rows stAt i').data (closeIn readers rows stAt i').readers := by
    show ProofFile.Honest.K2.ownBy (rows i.x) (readers i) = ProofFile.Honest.K2.ownBy (rows i'.x) (readers i')
    rw [hx]
    exact ho
  refine seatClosings_of_fold (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G
    fun pub m0 h0 heard c s => ?_
  exact ((foldAtT_of_own Z G pub (I := closeIn readers rows stAt i) (I' := closeIn readers rows stAt i')
    (congrArg rows hx :) (congrArg stAt hx :) ho') m0 h0 heard ()).1 c s

/-- **Each move of each part of each of the lot's halves says and hands the same** at two inputs with the same x at
whose readers the data's `entry` is the same; readers, rows and stAt are arbitrary. -/
theorem seatLotC_of_entry (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : Pub) (G : Ground) {i i' : Local W₀ Rc Xi Tr} (hx : i.x = i'.x)
    (hD : (rows i'.x).entry (readers i) = (rows i'.x).entry (readers i')) :
    ∀ g ∈ (seatLotC (X := X) readers rows stAt).halves Z G, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ :=
  seatLotC_of_own readers rows stAt Z G hx (funext fun addrs => funext fun shapes => funext fun heard =>
    ProofFile.Honest.K2.Law.ownBy_of_entry (rows i'.x) hD addrs shapes heard)

/-! ## The two stops -/

/-- Two stops that always return `none`, joined by `stopBoth`, always return `none`. -/
theorem stopBoth_of_none (n m : Nat) (f g : List Fmt.Drawn → List Fmt.Drawn → Option String)
    (hf : ∀ a b, f a b = none) (hg : ∀ a b, g a b = none) (front own : List Fmt.Drawn) :
    stopBoth n m f g front own = none := by
  unfold stopBoth
  rw [hf, hg]
  split <;> split <;> rfl

/-- Where both stops of a part always return `none`, so do both stops of that part with the round "BAT" in front. -/
theorem closePart_stops_none (fold : Part V W X) (hb : ∀ a b, fold.bad a b = none)
    (hh : ∀ v a b, fold.hid v a b = none) :
    (∀ v a b, (closePart fold).hid v a b = none) ∧ ∀ a b, (closePart fold).bad a b = none := by
  refine ⟨fun v a b => ?_, fun a b => ?_⟩
  · show stopBoth _ _ ((closeBatPart (V := V) (W := W) (X := X)).hid v) (fold.hid v) a b = none
    exact stopBoth_of_none _ _ _ _ (fun _ _ => rfl) (hh v) a b
  · show stopBoth _ _ (closeBatPart (V := V) (W := W) (X := X)).bad fold.bad a b = none
    exact stopBoth_of_none _ _ _ _ (fun _ _ => rfl) hb a b

/-- Where both stops of the fold's part always return `none`, so do both stops of each part of each half. -/
theorem seatClosings_stops_none (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (borne : Pub → VerifiableInference.Desc.First.Close.Par → List Borne)
    (fold : ClosePub → Part Unit CloseIn Unit) (Z : Pub) (G : Ground)
    (hb : ∀ pub a b, (fold pub).bad a b = none) (hh : ∀ pub v a b, (fold pub).hid v a b = none) :
    ∀ g ∈ seatClosings (X := X) inOf borne fold Z G, ∀ q ∈ g.parts,
      (∀ v a b, q.hid v a b = none) ∧ ∀ a b, q.bad a b = none := by
  intro g hg
  obtain ⟨P, -, rfl⟩ := List.mem_map.1 (show g ∈ (closePars Z).map
    (fun P => closeHalf (seatFold (X := X) inOf fold) ⟨P, borne Z P⟩) from hg)
  intro q hq
  obtain rfl : q = _ := List.mem_singleton.1 hq
  exact closePart_stops_none (seatFold (X := X) inOf fold ⟨P, borne Z P⟩)
    (fun a b => hb ⟨P, borne Z P⟩ a b) (fun _ a b => hh ⟨P, borne Z P⟩ () a b)

/-- **At each part of each of the lot's halves both stops return `none` at every argument**; readers, rows and stAt are
arbitrary; no premise. -/
theorem seatLotC_stops_none (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : Pub) (G : Ground) :
    ∀ g ∈ (seatLotC (X := X) readers rows stAt).halves Z G, ∀ q ∈ g.parts,
      (∀ v a b, q.hid v a b = none) ∧ ∀ a b, q.bad a b = none :=
  seatClosings_stops_none (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G (fun _ _ _ => rfl)
    fun _ _ _ _ => rfl

/-! ## The lot with K9's own halves in front -/

/-- Each move of each part of K9's own halves says and hands the same at any two inputs. -/
theorem batHalves_idle (Z : Pub) :
    ∀ g ∈ ProofFile.Honest.K9.batHalves (V := V) (W := W) (X := X) Z, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (w w' : W) (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨w, heard, own⟩ = mv.say c s ⟨w', heard, own⟩) ∧
          mv.hand ⟨w, heard, own⟩ = mv.hand ⟨w', heard, own⟩ := by
  intro g hg
  obtain ⟨l, -, hf⟩ := List.mem_filterMap.1 hg
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 hf
  intro q hq
  obtain rfl : q = _ := List.mem_singleton.1 hq
  intro mv hmv
  obtain rfl : mv = _ := List.mem_singleton.1 hmv
  exact fun _ _ _ _ => ⟨fun _ _ => rfl, rfl⟩

/-- Both stops of each part of K9's own halves always return `none`. -/
theorem batHalves_stops_none (Z : Pub) :
    ∀ g ∈ ProofFile.Honest.K9.batHalves (V := V) (W := W) (X := X) Z, ∀ q ∈ g.parts,
      (∀ v a b, q.hid v a b = none) ∧ ∀ a b, q.bad a b = none := by
  intro g hg
  obtain ⟨l, -, hf⟩ := List.mem_filterMap.1 hg
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 hf
  intro q hq
  obtain rfl : q = _ := List.mem_singleton.1 hq
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- `seatLotC_of_entry` at the lot with K9's own halves in front. -/
theorem seatLotT_of_entry (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : Pub) (G : Ground) {i i' : Local W₀ Rc Xi Tr} (hx : i.x = i'.x)
    (hD : (rows i'.x).entry (readers i) = (rows i'.x).entry (readers i')) :
    ∀ g ∈ (seatLotT (X := X) readers rows stAt).halves Z G, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ := by
  intro g hg
  rw [seatLotT_is] at hg
  rcases List.mem_append.1 hg with h | h
  · exact fun q hq mv hmv heard own => batHalves_idle Z g h q hq mv hmv i i' heard own
  · exact seatLotC_of_entry readers rows stAt Z G hx hD g h

/-- `seatLotC_stops_none` at the lot with K9's own halves in front. -/
theorem seatLotT_stops_none (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : Pub) (G : Ground) :
    ∀ g ∈ (seatLotT (X := X) readers rows stAt).halves Z G, ∀ q ∈ g.parts,
      (∀ v a b, q.hid v a b = none) ∧ ∀ a b, q.bad a b = none := by
  intro g hg
  rw [seatLotT_is] at hg
  rcases List.mem_append.1 hg with h | h
  · exact batHalves_stops_none Z g h
  · exact seatLotC_stops_none readers rows stAt Z G g h

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closeAsk_of_job
#print axioms ProofFile.Honest.K10.closeAskAt_of_job
#print axioms ProofFile.Honest.K10.askOr_of_job
#print axioms ProofFile.Honest.K10.foldShellT_of_job
#print axioms ProofFile.Honest.K10.jobRows_of_own
#print axioms ProofFile.Honest.K10.jobAt_of_own
#print axioms ProofFile.Honest.K10.foldAtT_of_own
#print axioms ProofFile.Honest.K10.closePart_of_fold
#print axioms ProofFile.Honest.K10.seatFold_of_fold
#print axioms ProofFile.Honest.K10.seatClosings_of_fold
#print axioms ProofFile.Honest.K10.seatClosings_of_in
#print axioms ProofFile.Honest.K10.seatLotC_of_own
#print axioms ProofFile.Honest.K10.seatLotC_of_entry
#print axioms ProofFile.Honest.K10.stopBoth_of_none
#print axioms ProofFile.Honest.K10.closePart_stops_none
#print axioms ProofFile.Honest.K10.seatClosings_stops_none
#print axioms ProofFile.Honest.K10.seatLotC_stops_none
#print axioms ProofFile.Honest.K10.batHalves_idle
#print axioms ProofFile.Honest.K10.batHalves_stops_none
#print axioms ProofFile.Honest.K10.seatLotT_of_entry
#print axioms ProofFile.Honest.K10.seatLotT_stops_none
