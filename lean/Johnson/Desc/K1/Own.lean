-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Own.lean: the kind K1, sending an encoding with an out-of-domain sample: the kind's
own decision. The rounds, the cube's numbers and the tests on the plan are
Johnson/Desc/K1/Send.lean's; here the pad, the front factor, the sample row and the seeds' cut are
written out.

This file holds definitions only; no theorem is stated.

This file and the rounds of Johnson/Desc/K1/Send.lean call none of the program's Send.cube,
Send.pad, Send.front, Send.form and Send.seedsOf (OnBytes/Iop/Send.lean), after which they are
written. Beneath them admitP (Johnson/Desc/First/Base/Ground.lean) has the pad's places from the
description's own Own.padMade (Johnson/Desc/Own/Send.lean).

What is called by name:
  the field's arithmetic (E, mulE, subE, oneE, zeroE, thetaE, E.ofTriple);
  three small tests in the description's own text: treesCan (Johnson/Desc/Own/Trees.lean), allZero
  (Johnson/Desc/Own/Rows.lean) and rising (Johnson/Desc/Own/Rising.lean);
  how a linear row is held as data: Tensor.eq, Tensor.entry, Row.addUnit, Row.add;
  the effects on the statement (Johnson/Desc/First/Base/Ground.lean): recvP, admitP, joinP;
  the segment's frame: the walk's and the frame's records and tests, and a commitment's frame
  around it (Johnson/Top/H0/L3/Frame.lean).

decide stands behind Block.step. The clauses on what a round holds or draws stand under ROUNDS, as
data, and are asked once, by roundsFit, out of ROUNDS: round 1 shows no item; it draws
seeds * (v + 1) elements, no position, no matrix entry; round 2 shows just the answers, one for each
sampled message and seed, and nothing else; it draws nothing. decide does not ask them again. A law
of this kind is to be stated of "roundsFit and decide". Whoever calls decide by itself has no such
asker.

Every refusal bears its test's name. One test asks more than the program, which has one copy of the
codes: that the record's codes are the plan's. "a seed's factor is 0" compares words with 0: it
speaks of the field's zero only where every word is below the prime (viewWordsBelowPrime,
Johnson/Desc/Block.lean).

Main names: Msg.e, Msg.pad, Msg.padFits, Msg.front, sampleRow, cutSeeds, layRows, decideSend;
planOkOwn; sendOwn (a sending by itself); laterOwn, commitOwn (a segment's later moment).

What is not claimed. That a row made here is the program's: no theorem ties them. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Send
import Johnson.Desc.Own.Rows
import Johnson.Desc.Own.Rising

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP reLoc)

/-! ## The pad and the sample row of an oracle message (its cube: K1/Send.lean) -/

/-- e_o: the pad's entries for one answer. -/
def Msg.e (m : Msg) : Nat := if m.Kzk != 0 || m.overE then 1 else 3

/-- The pad of answer i: the index of each of its entries, with the power of θ that it goes with. It
lies at the end of the final mask row, or of the final main row if there is no mask row; an entry in
row r at position j has the index r + j · 2 ^ (the row's bits). -/
def Msg.pad (m : Msg) (i : Nat) : List (Nat × Nat) :=
  let (rows, len) := if m.Kzk != 0 then (m.Kzk, 2 ^ m.logEllZk) else (m.K, 2 ^ m.logEll)
  (List.range m.e).map fun t =>
    ((rows - 1) + (len - m.e * m.answers + m.e * i + t) * 2 ^ clog rows, t)

/-- The pads fit their row. ON THE PLAN ALONE. -/
def Msg.padFits (m : Msg) : Bool :=
  decide (m.e * m.answers ≤ (if m.Kzk != 0 then 2 ^ m.logEllZk else 2 ^ m.logEll))

/-- With both tables: the factor that fixes the cube's coordinates above a table's own bits: 0
between, and the last 0 for main, 1 for mask. -/
def Msg.front (m : Msg) (z : List E) (tableBits : Nat) (mask : Bool) : E :=
  if !(m.K != 0 && m.Kzk != 0) then oneE else
  let top := z.getD (m.v - 1) zeroE
  ((z.take (m.v - 1)).drop tableBits).foldl (fun f x => mulE f (subE oneE x))
    (if mask then top else subE oneE top)

/-- **The sample row of message number o for answer i**: ĝ_o(z) + β · ⟨θ, the pad of i⟩ = y, where
g_o holds every entry outside the pads at its index. Coordinate t of z goes with bit t of the index,
the lowest first (Tensor.eq). At a pad's entry the coefficient under z is taken off again. -/
def sampleRow (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) : OnBytes.Row :=
  let part : Part := if m.Kzk != 0 then .mask else .main
  let onMain := Tensor.eq (z.take m.mainBits) (m.front z m.mainBits false)
  let onMask := Tensor.eq (z.take m.maskBits) (m.front z m.maskBits true)
  let under := fun j => (if m.Kzk != 0 then onMask else onMain).entry j
  let pads := (List.range m.answers).flatMap fun k => (m.pad k).map fun x => (k, x)
  let r₀ : OnBytes.Row := pads.foldl (fun r x =>
    r.addUnit o part x.2.1 (subE (if x.1 == i then mulE β (thetaE x.2.2) else zeroE) (under x.2.1)))
    { kind := .sample }
  let r₁ := if m.K != 0 then r₀.add o .main onMain else r₀
  { (if m.Kzk != 0 then r₁.add o .mask onMask else r₁) with target := y }

/-! ## DECIDES -/

/-- n seeds, each v coordinates and a factor, off the elements drawn. -/
def cutSeeds (v : Nat) : Nat → List E → List (List E × E)
  | 0, _ => []
  | n + 1, l => (l.take v, (l.drop v).headD zeroE) :: cutSeeds v n (l.drop (v + 1))

/-- Message by message, in the order of sending: a sampled one takes its next answers, its sample
rows are laid and it is admitted; a word without a sample is passed by. -/
def layRows {L : Type} (codes : Codes) (seeds : List (List E × E)) :
    List (Nat × OracleShape) → List E → DState L → Except String (DState L)
  | [], ys, d =>
    -- no answer is left over
    if ys.isEmpty then .ok d else .error "K1: an answer is left over"
  | (o, s) :: l, ys, d =>
    if s.answers == 0 then layRows codes seeds l ys d else
    -- a seed is there for each answer; and an answer for each row
    if decide (seeds.length < s.answers) then .error "K1: a seed lacks for an answer" else
    if decide (ys.length < s.answers) then .error "K1: an answer lacks for a row" else
    let m := Msg.of codes s
    let rows := ((seeds.take s.answers).zip (ys.take s.answers)).zipIdx.map fun x =>
      sampleRow m o x.1.1.1 x.1.1.2 x.2 x.1.2
    (named "K1: the statement does not admit the sample" (Ground.admitP d o rows.toArray)).bind
      (layRows codes seeds l (ys.drop s.answers))

/-- **The sending's decision**, behind roundsFit. Returns the new messages' numbers. -/
def decideSend {L : Type} (P : Par) (owed : Option Nat) (d : DState L) :
    List Fmt.RoundView → Except String (Array Nat × DState L)
  | [r₁, r₂] => do
    -- on the carried record alone
    need "K1: rows are owed" owed.isNone
    -- more than the program asks, which has one copy: the record's codes are the plan's: the cube
    -- and the pad here are counted by the plan's codes; recvP and admitP read the record's
    need "K1: the record's codes are not the plan's" (d.st.codes == P.codes)
    -- on the plan, once more, under its own name (Par.trees and oracles say nothing where it fails)
    need "K1: the trees cannot be laid" (Own.treesCan P.codes P.sent)
    -- on what is drawn
    let seeds := cutSeeds P.coordinates P.seeds (r₁.drawn.elems.map E.ofTriple)
    need "K1: a seed's factor is 0" (seeds.all fun s => !Own.allZero s.2)
    let ys := r₂.vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none
    let x ← named "K1: the statement does not receive the messages"
      (Ground.recvP P.gp.firstTree d P.sent)
    let all := x.1.toList.zip (P.sent.toList.map (·.shape))
    let todo := (all.filter fun y => y.2.answers != 0).map (·.1)
    -- the sampled messages' numbers rise
    need "K1: the numbers do not rise" (Own.rising todo)
    -- none was sampled before
    need "K1: a message was sampled before"
      (todo.all fun o => ((x.2.st.oracles[o]?).map (!·.sampled)).getD false)
    let d' ← layRows P.codes seeds all ys x.2
    pure (x.1, d')
  | _ => .error "K1: not two rounds"

/-- TESTS ON THE PLAN ALONE: K1/Send.lean's, and every sampled message's pads fit their row. -/
def planOkOwn (P : Par) : Bool := planOk P && P.tuple.all fun s => (Msg.of P.codes s).padFits

variable {Cl : Type}

/-- **A sending by itself.** -/
def sendOwn (P : Par) : Block (Owing (DState (Array Nat))) Cl :=
  { name := "K1: a sending", place := P.place, planOk := planOkOwn P, rounds := rounds P
    oracles := oracles P, before := before, claims := [], after := []
    decide := fun s rs _ => (decideSend P s.owed s.held rs).map fun x =>
      { owed := none, held := { x.2 with loc := x.1 } } }

/-- A segment's later moment around the sending: the walk's and the frame's own tests and writes. -/
def laterOwn (P : Par) (owed : Option Nat) : L3.Send (DState Unit) := fun c w rs =>
  let f := c.frame
  if !(c.inLink && decide (c.moments < c.momentsDue)) then .error "no moment is due" else
  match f.shape.link[f.link]? with
  | none => .error "the segment is not in the shape"
  | some Lk =>
    if !(f.next == .laterOrClose && decide (f.moment < reqMoments Lk)) then
      .error "the frame awaits no later moment" else
    match decideSend P owed w rs with
    | .error e => .error e
    | .ok x =>
      match joinOwnP groundG P.gp x.2 { f with moment := f.moment + 1 } (f.atMoment f.moment)
          x.1 with
      | none => .error "the joining refuses"
      | some y => .ok ({ c with frame := y.1, sent := x.1, moments := c.moments + 1 }, y.2)

/-- **A segment's later moment**, where the sub-proof commits to arrays. -/
def commitOwn (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Block (Owing (L3.St (DState Unit))) Cl :=
  { name := "K1: a commitment", place := P.place, planOk := planOkOwn P && arrays.isSome
    rounds := rounds P, oracles := oracles P, before := before, claims := [], after := []
    decide := fun s rs _ =>
      let f := s.held.L.check.frame
      -- on the carried record alone: it stands at this place, and announces what ROUNDS says
      if f.link == link && f.moment == moment &&
          ReqFrame.notices (f.atMoment f.moment) == P.sent then
        match arrays with
        | none => .error "K1: the plan names no arrays"
        | some ts => (L3.commitStep (laterOwn P s.owed) ts s.held rs).map fun x =>
          { owed := none, held := x }
      else .error "K1: the record does not stand at this place, or announces other messages" }

end VerifiableInference.Desc.K1
