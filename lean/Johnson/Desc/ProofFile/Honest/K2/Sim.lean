-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Sim.lean: the kind "the code switch" (K2): THE PART's SIMULATOR, in
the frame's form (`Sim`, Honest/Frame.lean), and the row in which it stands beside the part
(`Side`, Honest/Side.lean). Definitions with code; one statement with its proof, on the row's form.

WHAT IT IS HANDED, BY TYPE: the public instance; what stands in front (not read); the challenges;
the positions; coins of its own: no input, no witness, no coin of a run's. BESIDE THESE IT HAS FOUR
LETTERS, which whoever lays the row fills: the sender `Sd`; the place's data `p`; a test `ok` on the
public instance; the rounds. THEY ARE MEANT TO BE PUBLIC DATA OF THE PLAN; NOTHING IN THIS FILE
HOLDS THEM FREE OF THE INDEX: that is to be held where they are filled. At the kind's lot of rows
(`switchSLot`, Honest/K2/Rows.lean) it is held BY TYPE: all four are terms of the plan's public
part (`Pub`), the segments' public data (`Ground`) and the filling's letter (`RowDataOf`) alone:
none takes an input or a reader. That these three are public is the frame's matter.

WHAT IT IS. THE TWO MOVES OF THE PART's OWN MAKER (`switchPart`, Honest/K2/Part.lean), PLAYED BY THE
FRAME's OWN `play`, AT AN INPUT THAT IS MADE OF ZEROS: what the fold in front leaves: zeros; the
next segment's own messages' main rows: zeros. The part is that maker at the runs that the book lets
it carry; the simulator plays the same maker at no carried run: two instances of one text, which
reads the carried runs through its input alone. There is no second text of the sending. It takes as
many coins as the part, which spends no run. It reads: the public instance, through one test; the
challenges of the part's two rounds; the positions that will be read; its coins. It does not read
what the parts in front show. The maker's two stops never stop.
WHERE THE ZEROS STAND: at the entries of the main rows that are no pad's of THIS sending: the
carrying message's, the kept copies', the next segment's own. What the carrying message holds of
OLDER sendings' coins (old mask rows, old tails, the kept members' old pads) is data of this
sending: zeros here. AT EVERY COIN's PLACE OF THIS SENDING (each row's tail; each sampled message's
pad; the mask rows' entries; the fresh mask's coefficients) STANDS THE SIMULATOR's OWN COIN, laid by
the same sender that lays the part's: `Sd`, a letter here; at the kind's lot it is `coreSender`,
whose `messageRows` (Honest/K2/Sending.lean) asks first whether a coin stands at a place.

  `zeroLeft`        what a fold leaves, at zeros
  `shapeZeros`, `shapeZerosAll`   FOR A TEST ON SHAPES ALONE: zeros of the type of coins, at a
                    count; at a list of named counts. `closingOk` alone calls them. NEVER TO BE
                    HANDED TO A PART OR A SIMULATOR IN THE STEAD OF COINS
  `simAsk`          the input of zeros, behind one public verdict
  `switchSim`       THE SIMULATOR. ok: a test on the public instance. rounds: the part's two rounds,
                    each with its oracle messages
  `switchRow`       the row: the kind's part (as Honest/K2/Half.lean lays it) with its simulator
  `publicOk`        a test with code on the filling at the public instance: `ownLaid`
                    (Honest/K2/AtPlan.lean) returns: what the lot's closing asks of the instance
  `closingOk`       a test with code on the place's public data alone: the closing returns AT ZEROS:
                    at main rows, challenges and carried coins that are zeros or lack. segs: the
                    segments in front of the switch, from the first on, as the lot hands them to
                    its closing
  `switchRow_fits`  a side that is seated with this row at a block of two rounds, each with a list
                    of oracle messages, passes the frame's test on a row's form (`Side.fits`)

Limits. NOTHING IS SHOWN HERE OF WHAT THE SIMULATOR YIELDS AGAINST WHAT THE PART SHOWS. The part's
closing refuses at public data that does not fit; the simulator does not run the closing: so the two
can be held against each other only where `closingOk` says yes, and that the closing then returns at
all values just where `publicOk` says yes is not shown here: it is `returnsLaw`
(Honest/K2/Law/SegmentAlike.lean). `ok` and `rounds` are letters: nothing holds them against a lot
or a block. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Oracle)
open VerifiableInference.Desc.K2.Honest (Left zeroG)

variable {W₀ Rc Xi Tr X S Cl : Type}

/-- What a fold leaves, at zeros. -/
def zeroLeft : Left :=
  ⟨fun _ => zeroG, fun _ => zeroG, fun _ _ => zeroG, fun _ _ => zeroG,
    fun _ => ⟨fun _ _ => zeroG, fun _ _ => zeroG⟩⟩

/-- FOR A TEST ON SHAPES ALONE: zeros of the type of coins. Never to be handed to a part or a
simulator in the stead of coins. -/
def shapeZeros (d : Due) : Cs d := ⟨fun _ => OnBytes.Slice.toF 0, fun _ => zeroG⟩

/-- The like at a list of named counts. -/
def shapeZerosAll : (ds : List (String × Due)) → CsAll ds
  | [] => ()
  | d :: ds => (shapeZeros d.2, shapeZerosAll ds)

/-- The input of zeros, behind one public verdict. -/
def simAsk (ok : Bool) : SwitchAsk :=
  ⟨fun _ _ => if ok then .ok zeroLeft else .error "the filling does not fit the place",
    fun _ _ _ => zeroG⟩

/-- **THE SIMULATOR.** -/
def switchSim (Sd : Sender) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) : Sim Xi :=
  { addr := ⟨p.place, 0⟩
    takes := (switchPart Sd p.sizes p.others p.foldVars []).takes
    tell := fun x _ ds asks c =>
      (play ((switchPart Sd p.sizes p.others p.foldVars []).steps "" ⟨p.place, 0⟩ rounds none
        (c, (), ())) ds [] (Mid.bare ⟨simAsk (ok x), [], ()⟩ [] [])).toOption.map fun y =>
          shownOf y.1 asks }

/-- **The row**: the kind's part with its simulator. -/
def switchRow (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi) :=
  (switchHalf Sd D readers closing p).parts.map fun P => (P, switchSim Sd p ok rounds)

/-- A test on the filling at the public instance. -/
def publicOk (D : RowDataOf Xi) (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace)
    (segs : List SegmentPub) (x : Xi) : Bool :=
  match ownLaid (D x) lay p segs with
  | .ok _ => true
  | .error _ => false

/-- A test on the place's public data: the closing returns at zeros. -/
def closingOk (table : FreshTable) (segs : List SegmentPub) (p : SwitchPlace) : Bool :=
  match closingFor table segs p.sizes.kept (fun _ _ _ _ => zeroG) []
      (Stretch.carried p.carries (shapeZerosAll p.carries)) with
  | .ok _ => true
  | .error _ => false

/-- **The row's form.** -/
theorem switchRow_fits (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (h : Side.seated bs p.place (switchRow Sd D readers closing p ok rounds) fs = some σ)
    (hr : σ.block.rounds.length = 2) (ho : σ.block.oracles.length = 2) : σ.fits = true := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp : b.place = p.place := by
    have := List.find?_some hb
    simpa using this
  have hr' : b.rounds.length = 2 := hr
  have ho' : b.oracles.length = 2 := ho
  simp [Side.fits, Side.half, Placed.rounds, switchRow, switchHalf, switchSim, switchPart,
    Part.lift, hp, hr', ho']

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.zeroLeft
#print axioms ProofFile.Honest.K2.shapeZeros
#print axioms ProofFile.Honest.K2.shapeZerosAll
#print axioms ProofFile.Honest.K2.simAsk
#print axioms ProofFile.Honest.K2.switchSim
#print axioms ProofFile.Honest.K2.switchRow
#print axioms ProofFile.Honest.K2.publicOk
#print axioms ProofFile.Honest.K2.closingOk
#print axioms ProofFile.Honest.K2.switchRow_fits
