-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Toy.lean: A TOY FOR K9's HONEST PART AND FOR ITS SHARE OF THE FALL:
the part played by the frame's own player, against K9's OWN VERIFIER TEXT at the real type of states of the
first chain (`First.S`, `K9.atS`), in a made-up segment laid by `Link.blocksInOrder`. Definitions,
`#guard` lines and a print as a pure definition (`printLines`; nothing is run or printed while the
file is compiled); no theorem. The file does not compile if one of the lines is false.

The segment. One oracle message with one mask row of two free entries; two slots, both filled; a
member that hears nothing and states two claims on the held values x0, x1:
    claim 0:  x0 - x1 - 3 = 0        claim 1:  x1 - 4 = 0        (true at x0 = 7, x1 = 4)
The held value under slot j is shown_j - factor * mask_j; shown_j := x_j + factor * mask_j.
The flat list: laid · the hearing member · THE BATCHING (`K9.batch atS`: the draw and the adding) ·
the frame's member "behind the batching", whose test is `K9.freeSlot` · the one equation
(`K9.oneEquation atS`) · cleared.
Behind the adding at chi: the coefficients are 1 on slot 0 and chi - 1 on slot 1; the constant is
- 3 - 4 chi. SO AT chi = 1 SLOT 1 HAS THE COEFFICIENT 0: the verifier refuses: a fall.

What is held.
  (0) the row is cut as the book's rule cuts the member's rounds; the frame's `chainSteps` lays it
  (1) the part plays: one round, nothing sent; at every chi that is tried, the falling one too
  (2) the batching's STEP (with the format's test on the rounds) says yes on the played round
  (3) K9's decision tests no equation: THE TEST IS THE CLAIM THAT THE BLOCK LEAVES: the one sum, on
      the ledger that the text leaves and on the masks, is 0: at two challenges; and it is not 0
      where a held value, a mask entry or a shown scalar is turned by one
  (4) the numbers: the coefficients and the constant at chi = 5, written out
  (5) the member behind the batching and the one equation's member say yes at chi = 5; the equation
      that goes to the chain holds on the masks
  (6) THE FALL: at chi = 1 the member behind the batching refuses under "K9.free-slot", and the
      fall's test says so; over 24 values of chi the fall's test says "none" just where that member
      says yes; at chi = 1 the claim that is left is 0 at another x1 too; at the merge's slot the
      test asks the other way round
  (7) another kind's shares: the one in front of the member is asked first; the one behind the
      adding behind K9's; where the batching itself refuses, what stands behind it is silent
  (8) the side: the row fits the member; the simulator's one round has the played round's items

Limits. A toy: made-up numbers; no array, no run, no smallness test; the counts of a segment's sort
are not in it. The masks are numbers of the toy, not coins of a book: K9's part is handed none.
"NO FALL JUST WHERE THAT MEMBER SAYS YES" IS THE TOY's TRUTH: its link's test is `K9.freeSlot` alone; at
the proof file's description that member asks more, and "a fall, so a refusal" alone is due.
NO LINE RUNS `batHalves`, `batLot`'s halves, `batFallAt` OR `batFallShareAt`: they want a public part
(`Pub`), which is made of the public files; none is at hand here. Some lines are controls on the
frame's and the format's own functions and stay green whatever K9's terms are: they are marked.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Fall
import Johnson.Desc.ProofFile.Honest.K9.Side
import Johnson.Desc.ProofFile.Honest.BookOf
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9.Toy
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape ReqLink ReqMessage)
open VerifiableInference.Desc (Block Link Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where)

def e (x : UInt64) : E := E.ofTriple (x, 0, 0)
def dE (x : UInt64) : Fmt.Drawn := ⟨[(x, 0, 0)], [], [], none⟩

/-! ## The written state in front of the draw -/

def osh : OracleShape := { mainRows := 0, maskRows := 1, answers := 0 }
def msg : ReqMessage := { shape := osh, leafClass := 0, moment := 0, life := 0 }
def lnk : ReqLink := { plain := 0, messages := [msg] }
def shape : ReqShape := { (default : ReqShape) with link := [lnk] }
def frame : ReqFrame :=
  { shape := shape, groups := #[], next := .laterOrClose, link := 0, group := 0, own := #[0] }
def check : ChainCheck := { frame := frame, rows := ⟨⟨[[]]⟩⟩, inLink := true, moments := 1 }
def LD : LinkCtx := { check := check, list := { link := true, planned := true }, moments := 1 }
def led : Ledger := { next := 0, left := 2, rows := 1, logRows := 0 }
def orc : OnBytes.Oracle := { shape := osh, groups := [0], ledger := some led }
def grp : Group := { code := 0, members := #[0], kept := #[false] }
/-- The mask rows' code: messages of two entries. -/
def stD : Statement :=
  { codes := { mask := #[{ logN := 2, ell := 2, r := 1 }] }, oracles := #[orc], groups := #[grp] }
def tlD : HTailF2 := { slotB := 2, eqFirst := #[0] }

/-- The factor of the two mask entries. -/
def beta : E := e 6

/-- What the toy's prover holds: the two held values, the two mask entries. -/
structure Held where
  x0 : E
  x1 : E
  m0 : E
  m1 : E

def held : Held := ⟨e 7, e 4, e 100, e 200⟩

def Held.mask (h : Held) (j : Nat) : E := if j == 0 then h.m0 else h.m1

/-- The ledger in front of the draw: both slots filled with what was shown. -/
def FD (h : Held) : Fork :=
  { planClaimsF := 2, ns := 2, next := 2, LS := #[zeroE, zeroE]
    vp := #[addE h.x0 (mulE beta h.m0), addE h.x1 (mulE beta h.m1)], mf := #[beta, beta]
    gotF := #[true, true] }

/-- A state in front of the first segment that bears no mark. -/
def base : S := S.start default { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ }

def sD (h : Held) : S := { base.enterLay LD (FD h) tlD with st := stD }

/-! ## The segment -/

def cl0 : Claim := { form := Aff.slot 0 - Aff.slot 1 - Aff.ofConst (e 3) }
def cl1 : Claim := { form := Aff.slot 1 - Aff.ofConst (e 4) }

def hearB : Block S Claim :=
  { name := "the toy's hearing member", place := ⟨1, some 0, 1, .K4⟩, planOk := true, rounds := []
    oracles := [], before := [], decide := fun s _ _ => .ok s
    claims := [("own", fun _ s => .ok ([cl0, cl1], s))], after := [] }

def pw : Where := { chain := 1, link := 0, piece := 2, pieceEq := 4, rows := 2, sent := 1 }

def lk : Link S Claim :=
  { name := "the toy's segment", chain := 1, number := 0, lay := .ok, hear := [hearB]
    order := [(0, "own")], each := fun _ _ _ => .ok (), orderAfter := []
    batch := fun g => VerifiableInference.Desc.K9.batch atS pw g
    tests := fun s => do
      let a ← VerifiableInference.Desc.K9.there "K9.in-a-segment"
        (VerifiableInference.Desc.K9.tAtS.get? s)
      VerifiableInference.Desc.K9.freeSlot 2 a.merge a.F
    close := [VerifiableInference.Desc.K9.oneEquation atS pw], clear := .ok }

def bs : List (Block S Claim) := lk.blocksInOrder

/-- A member that refuses all: what `at_` answers beyond the list. -/
def noB : Block S Claim :=
  { hearB with name := "no member", decide := fun _ _ _ => .error "no member", claims := [] }

def at_ (i : Nat) : Block S Claim := bs.getD i noB

-- the list's places: the half stands at the batching's
-- (a control: on the made-up segment's flat list; green whatever K9's honest terms are)
#guard bs.map (·.place.piece) == [0, 1, 2, 3, 4, 5]
#guard (at_ 2).place == (batHalf pw : Placed Unit Unit Unit).place
-- (a control: on the flat list's rounds; green whatever K9's honest terms are)
#guard (at_ 2).rounds.length == 1 && (at_ 3).rounds.isEmpty && (at_ 4).rounds.isEmpty
-- (a control: on the flat list's plan tests; green whatever K9's honest terms are)
#guard bs.all (·.planOk)

/-! ## The part played -/

abbrev Bk : ProverCoinCounts := { first := [], shared := [], second := [], ahead := [], cuts := [] }

def half : Placed Unit Unit Unit := batHalf pw

/-- A row played by the frame's player, at the description's own member's rounds; both stops are
asked (the second is handed `some ()`). own: what is handed on to the row. The rounds, and what the
row hands on. The start state is `Mid.bare`: no column is handed to the row here, and the toy says
nothing of a player that hands columns. -/
def playedBy (hf : Placed Unit Unit Nat) (own : Nat) (front ds : List Fmt.Drawn) :
    Option (List Fmt.RoundView × Nat) :=
  let c : Coins Bk := ⟨(), (), ()⟩
  (lendRow Bk (Bk.rowsOf 0) (c.look 0) hf.place hf.parts 0).toOption.bind fun h =>
    (play (hf.steps (at_ 2) (some ()) h) ds [] (Mid.bare ⟨(), front, own⟩ front [])).toOption.map fun y =>
      (roundsOf y.1, y.2.st.own)

def played (front ds : List Fmt.Drawn) : Option (List Fmt.RoundView) :=
  (playedBy (batHalf pw) 7 front ds).map (·.1)

/-- The half with a stop laid in: for two controls. -/
def stopping (first : Bool) : Placed Unit Unit Nat :=
  ⟨(batHalf pw : Placed Unit Unit Nat).place,
   [if first then { (batPart : Part Unit Unit Nat) with bad := fun _ _ => some "a stop" }
    else { (batPart : Part Unit Unit Nat) with hid := fun _ _ _ => some "a stop" }]⟩

/-- A book that has the cut for the batching's place: one part of one round. -/
abbrev BkC : ProverCoinCounts :=
  { first := [], shared := [], second := [], ahead := [], cuts := [(⟨1, some 0, 2, .K9⟩, [1])] }

/-- The whole flat list's rounds, as the frame lays them at a book: how many; or its refusal. -/
def laid (B : ProverCoinCounts) (c : Coins B) : Except String Nat :=
  (chainSteps B (B.rowsOf 0) (c.look 0) (some ()) bs [half]).map (·.length)

-- the row is cut as the book's rule cuts the member's own rounds; the frame lays the list at a book
-- with that cut, and (a control on the frame) refuses at a book without it
#guard cutOfNames .K9 ((at_ 2).rounds.map (·.entry.name)) == half.parts.map (·.moves.length)
#guard (laid BkC ⟨(), (), ()⟩).toOption == some 1
#guard (laid Bk ⟨(), (), ()⟩).toOption == none
#guard strays bs [half] == []
#guard strays bs [(batHalf { pw with piece := 7 } : Placed Unit Unit Unit)] != []
-- the halves off a list of places, as the lot reads it: of K9's three places a segment the one with
-- steps alone gets a half (a half reads of the place's numbers chain, segment and piece alone); a place
-- of another kind gets none; a K9 place with steps whose stretch of rounds is empty gets none; two K9
-- places with steps at one segment: the lot's own reading lists the segment twice: two halves at the
-- first one's place
def spots : List (Spot × List Fmt.DeclaredRound × Nat) :=
  [(⟨"hears", ⟨1, some 0, 1, .K4⟩, [⟨"G0", "a", 1, "K4", 0⟩]⟩, [], 1),
   (⟨"the batching", ⟨1, some 0, 2, .K9⟩, [⟨"G0", "b", 2, "K9", 1⟩]⟩, (at_ 2).rounds, 1),
   (⟨"the one equation", ⟨1, some 0, 4, .K9⟩, []⟩, [], 1)]
#guard (batHalvesAt spots : List (Placed Unit Unit Unit)).map (·.place) == [half.place]
#guard (batHalvesAt spots : List (Placed Unit Unit Unit)).map (·.rounds) == [1]
#guard (batHalvesAt (spots.take 1) : List (Placed Unit Unit Unit)).isEmpty
#guard strays bs (batHalvesAt spots : List (Placed Unit Unit Unit)) == []
def spotNoRounds : Spot × List Fmt.DeclaredRound × Nat :=
  (⟨"the batching", ⟨1, some 0, 2, .K9⟩, [⟨"G0", "b", 2, "K9", 1⟩]⟩, [], 1)
#guard (batHalvesAt [spotNoRounds] : List (Placed Unit Unit Unit)).isEmpty
def spotTwice : Spot × List Fmt.DeclaredRound × Nat :=
  (⟨"a second one", ⟨1, some 0, 6, .K9⟩, [⟨"G0", "c", 6, "K9", 1⟩]⟩, (at_ 2).rounds, 1)
#guard (batHalvesAt (spots ++ [spotTwice]) : List (Placed Unit Unit Unit)).map (·.place)
  == [half.place, half.place]

def why {α : Type} : Except String α → String
  | .ok _ => "yes"
  | .error x => x

/-- The state behind the batching's STEP on the played round. -/
def behind (h : Held) (chi : UInt64) : Except String S :=
  match played [dE 9] [dE chi] with
  | some rs => ((at_ 2).step 0 (sD h) rs []).map (·.1)
  | none => .error "the part did not play"

/-- The ledger behind the adding. -/
def ledger (h : Held) (chi : UInt64) : Option Fork := (behind h chi).toOption.bind (·.fork?)

/-- THE CLAIM THAT IS LEFT: the constant and, for each slot, its coefficient times the held value
under it, at the masks m. -/
def left (F : Fork) (m : Nat → E) : E :=
  (List.range F.ns).foldl (fun a j => addE a (mulE (F.LS.getD j zeroE)
    (subE (F.vp.getD j zeroE) (mulE (F.mf.getD j zeroE) (m j))))) F.c0

-- (1) one round, nothing sent; the falling chi too; a list of two challenges is refused
#guard (played [dE 9] [dE 5]).map (·.map fun r => (r.vals, r.drawn)) == some [([], dE 5)]
#guard (played [] [dE 1]).map (·.length) == some 1
-- (a control: on the frame's player; green whatever K9's honest terms are)
#guard (played [dE 9] [dE 5, dE 6]).isNone
-- it hands on what it was handed
#guard (playedBy (batHalf pw) 7 [dE 9] [dE 5]).map (·.2) == some 7
-- neither stop stops: with a stop of either sort laid in, this player does not go through
#guard (playedBy (stopping true) 7 [dE 9] [dE 5]).isNone
#guard (playedBy (stopping false) 7 [dE 9] [dE 5]).isNone
-- (2) the batching's step says yes; (two controls on the format's test) on a round that holds an
-- item, and on no round, it says no
#guard why (behind held 5) == "yes"
#guard why ((at_ 2).step 0 (sD held) [⟨[.e (1, 0, 0)], dE 5⟩] []) == "the rounds"
#guard why ((at_ 2).step 0 (sD held) [] []) == "the rounds"
-- (3) the claim that is left is 0, at two challenges
#guard (ledger held 5).map (fun F => left F held.mask) == some zeroE
#guard (ledger held 12345).map (fun F => left F held.mask) == some zeroE
-- a held value turned by one (a false input): not 0
#guard (ledger { held with x0 := e 8 } 5).map (fun F => left F held.mask == zeroE) == some false
#guard (ledger { held with x1 := e 5 } 5).map (fun F => left F held.mask == zeroE) == some false
-- a mask entry turned by one behind the showing: not 0
#guard (ledger held 5).map (fun F => left F { held with m0 := e 101 }.mask == zeroE) == some false
#guard (ledger held 5).map (fun F => left F { held with m1 := e 201 }.mask == zeroE) == some false
-- a shown scalar turned by one: not 0
#guard (ledger held 5).map (fun F =>
  left { F with vp := F.vp.modify 1 (addE · oneE) } held.mask == zeroE) == some false
-- (4) the numbers at chi = 5: 1 and 5 - 1 on the slots; - 3 - 4 * 5 as the constant; two claims
#guard (ledger held 5).map (·.LS) == some #[e 1, e 4]
#guard (ledger held 5).map (·.c0) == some (subE zeroE (e 23))
#guard (ledger held 5).map (·.nClaim) == some 2
#guard (ledger held 5).map (·.vp) == some #[e 607, e 1204]
#guard (ledger held 12345).map (·.LS) == some #[e 1, e 12344]
-- (5) the two members behind say yes at chi = 5
def behind2 (h : Held) (chi : UInt64) : Except String S :=
  (behind h chi).bind fun s => (at_ 3).decide s [] []
def behind3 (h : Held) (chi : UInt64) : Except String S :=
  (behind2 h chi).bind fun s => (at_ 4).decide s [] []
#guard why (behind2 held 5) == "yes"
#guard why (behind3 held 5) == "yes"
-- one row more lies on the segment's group, and both mask entries are taken
#guard (behind3 held 5).toOption.map (fun s => (s.st.groups.map (·.rows.size), s.st.oracles.map
  fun o => o.ledger.map (·.left))) == some (#[1], #[some 0])
-- the equation that goes to the chain: < on the masks, the masks > + the constant = 0
#guard ((ledger held 5).bind fun F =>
  (VerifiableInference.Desc.K9.equation { LD with handed := true } F).toOption.map fun x =>
    addE x.1.constant (addE (mulE (x.1.onMasks.getD 0 zeroE) held.m0)
      (mulE (x.1.onMasks.getD 1 zeroE) held.m1))) == some zeroE
-- (6) THE FALL. At chi = 1 the batching says yes, the coefficient on slot 1 is 0, the member behind
-- refuses, and the fall's test says so; the claim that is left is 0 there too
def fall (h : Held) (chi : UInt64) : Option String :=
  batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => none) (sD h) [dE chi]
#guard why (behind held 1) == "yes"
#guard (ledger held 1).map (·.LS) == some #[e 1, zeroE]
#guard (ledger held 1).map (fun F => left F held.mask) == some zeroE
#guard why (behind2 held 1) == "the tests behind the adding: K9.free-slot"
#guard fall held 1 == some "K9.free-slot"
#guard fall held 5 == none
-- at chi = 1, where slot 1 stands under the coefficient 0, the claim that is left is 0 at x1 = 5
-- too (7 - 5 - 3 + 1 * (5 - 4) = 0); at chi = 5 it is not (above). The verifier's text on the test:
-- Johnson/Desc/First/Door/Sums.lean, "What kind of tests these are"
#guard (ledger { held with x1 := e 5 } 1).map (fun F => left F held.mask) == some zeroE
-- a challenge with a sealed digest: the member is shown none, as `Block.step` shows it none: a
-- made-up member that refuses a round with a digest goes through
def shy : Block S Claim :=
  { at_ 2 with decide := fun s rs gs =>
      if rs.any (·.drawn.digest.isSome) then .error "a digest is shown" else (at_ 2).decide s rs gs }
def dD (x : UInt64) : Fmt.Drawn := ⟨[(x, 0, 0)], [], [], some ByteArray.empty⟩
-- (a control: on the toy's own shy member; green whatever K9's honest terms are)
#guard why (shy.decide (sD held) [⟨[], dD 5⟩] []) == "a digest is shown"
#guard (behindBat shy (sD held) [dD 5]).isSome
-- (a control: on Block.step, which hides the digest; green whatever K9's honest terms are)
#guard why (shy.step 0 (sD held) [⟨[], dD 5⟩] []) == "yes"
#guard batFallTest shy 2 (fun _ _ => none) (fun _ => none) (sD held) [dD 1] == some "K9.free-slot"
-- over 24 values: "no fall" just where the member behind the batching says yes; one of them falls
#guard (List.range 24).all fun c =>
  (fall held c.toUInt64).isNone == (behind2 held c.toUInt64).toOption.isSome
#guard ((List.range 24).filter fun c => (fall held c.toUInt64).isSome) == [1]
-- at other x and m: the same answers
#guard (List.range 24).all fun c =>
  fall ⟨e 1, e 2, e 3, e 4⟩ c.toUInt64 == fall held c.toUInt64
-- THE MEMBER AS THE DESCRIPTION's MAKERS WRAP IT: with a refusal where the decision leaves a mark
-- (`guardMark`, Johnson/Desc/ProofFile/Frames1.lean): the toy's state bears no mark: the same answers;
-- at a marked state that member refuses, under the mark's own words, at each of the six chi tried, the
-- falling one among them, and what stands behind it is silent
#guard (sD held).failed == none
#guard batFallTest (guardMark (at_ 2)) 2 (fun _ _ => none) (fun _ => none) (sD held) [dE 1]
  == some "K9.free-slot"
#guard batFallTest (guardMark (at_ 2)) 2 (fun _ _ => none) (fun _ => none) (sD held) [dE 5] == none
#guard (behindBat (guardMark (at_ 2)) (sD held) [dE 5]).isSome
#guard (behindBat (guardMark (at_ 2)) ((sD held).mark "a mark") [dE 5]).isNone
#guard (List.range 6).all fun c =>
  why ((guardMark (at_ 2)).decide ((sD held).mark "a mark") [⟨[], dE c.toUInt64⟩] []) == "marked: a mark"
#guard batFallTest (guardMark (at_ 2)) 2 (fun _ _ => none) (fun _ => none) ((sD held).mark "a mark")
  [dE 1] == none
#guard (behindBat (at_ 2) ((sD held).mark "a mark") [dE 5]).isSome
-- a chi with all three coordinates: the claim that is left is 0; no fall
def dE3 (x y z : UInt64) : Fmt.Drawn := ⟨[(x, y, z)], [], [], none⟩
#guard ((behindBat (at_ 2) (sD held) [dE3 5 7 11]).bind (·.fork?)).map (fun F => left F held.mask)
  == some zeroE
#guard ((behindBat (at_ 2) (sD { held with x1 := e 5 }) [dE3 5 7 11]).bind (·.fork?)).map
  (fun F => left F held.mask == zeroE) == some false
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => none) (sD held) [dE3 5 7 11] == none
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => none) (sD held) [dE3 1 0 1] == none
-- (7) another kind's share is asked behind K9's own, of the state behind the adding
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => some "another's") (sD held) [dE 5] == some "another's"
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => some "another's") (sD held) [dE 1] == some "K9.free-slot"
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun s => if (s.fork?.map (·.nClaim)) == some 2 then none else some "x")
  (sD held) [dE 5] == none
-- a share in front of the member is asked first, of the state in front and the challenges
#guard batFallTest (at_ 2) 2 (fun _ ds => if ds == [dE 1] then some "in front" else none)
  (fun _ => none) (sD held) [dE 1] == some "in front"
#guard batFallTest (at_ 2) 2 (fun s _ => if (s.fork?.map (·.nClaim)) == some 0 then none else some "x")
  (fun _ => none) (sD held) [dE 5] == none
-- where the batching itself refuses (drawn twice) what stands behind it is silent; in front: not
#guard why ((behind held 5).bind fun s => (at_ 2).decide s [⟨[], dE 5⟩] []) == "K9.nothing-owed"
#guard ((behind held 5).toOption.bind fun s =>
  batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => some "another's") s [dE 5]) == none
#guard ((behind held 5).toOption.bind fun s =>
  batFallTest (at_ 2) 2 (fun _ _ => some "in front") (fun _ => none) s [dE 5]) == some "in front"
-- three slots under test where two are filled: the third has no coefficient: a fall at every chi
#guard batFallTest (at_ 2) 3 (fun _ _ => none) (fun _ => none) (sD held) [dE 5] == some "K9.free-slot"
-- the stated shares
#guard statedShares [half] == (⟨0, 1⟩, ⟨0, 1⟩)
#guard batFallShare 2 3 97 == ⟨6, 97⟩
#guard sizeOfE == 18446744069414584321 ^ 3

/-! ## The merge's slot; no open segment -/

/-- A state with the merge's end value under slot j. -/
def withMerge (j : Nat) (s : S) : S :=
  match s.here with
  | .lay a =>
    { s with here := .lay { a with own := some { VerifiableInference.Desc.First.blankOwn with
        wo := { VerifiableInference.Desc.First.blankOwn.wo with sFv := j } } } }
  | _ => s

-- the toy's states have no merge; with the merge's end value under slot 1 the test asks that slot
-- 1's coefficient IS 0: so chi = 1 passes and chi = 5 falls
#guard (behind held 5).toOption.map (fun s => VerifiableInference.Desc.K9.mergeOf s) == some none
#guard (behind held 5).toOption.map (fun s => VerifiableInference.Desc.K9.mergeOf (withMerge 1 s))
  == some (some 1)
#guard (behind held 1).toOption.map (fun s => slotsFree 2 (withMerge 1 s)) == some true
#guard (behind held 5).toOption.map (fun s => slotsFree 2 (withMerge 1 s)) == some false
#guard (behind held 5).toOption.map (fun s => freeSlotShare 2 (withMerge 1 s))
  == some (some "K9.free-slot")
-- and the link's own test says the same at these states
#guard (behind held 1).toOption.map (fun s => why (lk.tests (withMerge 1 s))) == some "yes"
#guard (behind held 5).toOption.map (fun s => why (lk.tests (withMerge 1 s)))
  == some "K9.free-slot"
-- the whole test from a state IN FRONT of the draw that has the merge under slot 1
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => none) (withMerge 1 (sD held)) [dE 1] == none
#guard batFallTest (at_ 2) 2 (fun _ _ => none) (fun _ => none) (withMerge 1 (sD held)) [dE 5]
  == some "K9.free-slot"
-- where no segment is open K9's share is silent: that refusal is no test on values
#guard slotsFree 2 S.blank == true
-- (a control: on the verifier's test outside a segment; green whatever K9's honest terms are)
#guard why (lk.tests S.blank) == "K9.in-a-segment"

/-! ## The side -/

def side : Option (Side S Claim Unit Unit Nat Unit) := batSide bs pw

#guard (side.map (·.fits)) == some true
#guard (side.map (·.block.name)) == some (at_ 2).name
#guard ((batSide bs { pw with piece := 7 } : Option (Side S Claim Unit Unit Nat Unit)).isNone)
-- the simulator's one round has the played round's items: none; no column
#guard ((batSim pw : Sim Unit).tell () ⟨[], []⟩ [dE 5] [[]] Cs.empty).map (·.map (·.vals))
  == (played [dE 9] [dE 5]).map (·.map (·.vals))
#guard ((batSim pw : Sim Unit).tell () ⟨[], []⟩ [dE 5] [[]] Cs.empty).map (·.map (·.cols))
  == some [[]]

/-- A line of the print: one challenge. -/
def line (chi : UInt64) : String :=
  s!"chi = {chi}: played {(played [dE 9] [dE chi]).map (·.length)} round(s) · the batching: " ++
  s!"{why (behind held chi)} · behind the batching: {why (behind2 held chi)} · the one equation: " ++
  s!"{why (behind3 held chi)} · the claim left is 0: " ++
  s!"{(ledger held chi).map fun F => left F held.mask == zeroE} · the fall's test: {fall held chi}"

/-- **THE PRINT**, as a pure definition: five lines. -/
def printLines : List String := [0, 1, 2, 5, 12345].map line

#guard printLines[1]? == some ("chi = 1: played (some 1) round(s) · the batching: yes · behind the " ++
  "batching: the tests behind the adding: K9.free-slot · the one equation: the tests behind the " ++
  "adding: K9.free-slot · the claim left is 0: (some true) · the fall's test: (some K9.free-slot)")
#guard printLines[3]? == some ("chi = 5: played (some 1) round(s) · the batching: yes · behind the " ++
  "batching: yes · the one equation: yes · the claim left is 0: (some true) · the fall's test: none")

end ProofFile.Honest.K9.Toy

#print axioms ProofFile.Honest.K9.Toy.e
#print axioms ProofFile.Honest.K9.Toy.dE
#print axioms ProofFile.Honest.K9.Toy.osh
#print axioms ProofFile.Honest.K9.Toy.msg
#print axioms ProofFile.Honest.K9.Toy.lnk
#print axioms ProofFile.Honest.K9.Toy.shape
#print axioms ProofFile.Honest.K9.Toy.frame
#print axioms ProofFile.Honest.K9.Toy.check
#print axioms ProofFile.Honest.K9.Toy.LD
#print axioms ProofFile.Honest.K9.Toy.led
#print axioms ProofFile.Honest.K9.Toy.orc
#print axioms ProofFile.Honest.K9.Toy.grp
#print axioms ProofFile.Honest.K9.Toy.stD
#print axioms ProofFile.Honest.K9.Toy.tlD
#print axioms ProofFile.Honest.K9.Toy.beta
#print axioms ProofFile.Honest.K9.Toy.Held
#print axioms ProofFile.Honest.K9.Toy.held
#print axioms ProofFile.Honest.K9.Toy.Held.mask
#print axioms ProofFile.Honest.K9.Toy.FD
#print axioms ProofFile.Honest.K9.Toy.base
#print axioms ProofFile.Honest.K9.Toy.sD
#print axioms ProofFile.Honest.K9.Toy.cl0
#print axioms ProofFile.Honest.K9.Toy.cl1
#print axioms ProofFile.Honest.K9.Toy.hearB
#print axioms ProofFile.Honest.K9.Toy.pw
#print axioms ProofFile.Honest.K9.Toy.lk
#print axioms ProofFile.Honest.K9.Toy.bs
#print axioms ProofFile.Honest.K9.Toy.noB
#print axioms ProofFile.Honest.K9.Toy.at_
#print axioms ProofFile.Honest.K9.Toy.Bk
#print axioms ProofFile.Honest.K9.Toy.half
#print axioms ProofFile.Honest.K9.Toy.playedBy
#print axioms ProofFile.Honest.K9.Toy.played
#print axioms ProofFile.Honest.K9.Toy.stopping
#print axioms ProofFile.Honest.K9.Toy.BkC
#print axioms ProofFile.Honest.K9.Toy.laid
#print axioms ProofFile.Honest.K9.Toy.spots
#print axioms ProofFile.Honest.K9.Toy.spotNoRounds
#print axioms ProofFile.Honest.K9.Toy.spotTwice
#print axioms ProofFile.Honest.K9.Toy.why
#print axioms ProofFile.Honest.K9.Toy.behind
#print axioms ProofFile.Honest.K9.Toy.ledger
#print axioms ProofFile.Honest.K9.Toy.left
#print axioms ProofFile.Honest.K9.Toy.behind2
#print axioms ProofFile.Honest.K9.Toy.behind3
#print axioms ProofFile.Honest.K9.Toy.fall
#print axioms ProofFile.Honest.K9.Toy.shy
#print axioms ProofFile.Honest.K9.Toy.dD
#print axioms ProofFile.Honest.K9.Toy.dE3
#print axioms ProofFile.Honest.K9.Toy.withMerge
#print axioms ProofFile.Honest.K9.Toy.side
#print axioms ProofFile.Honest.K9.Toy.line
#print axioms ProofFile.Honest.K9.Toy.printLines
