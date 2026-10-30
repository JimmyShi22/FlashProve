-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyFall.lean: a second small toy example, at a toy description of
its own: eight parts in the second chain, with a stop, two owners of one spender, a part that spends
and sends a table, and a fall that depends on a coin: two sub-protocols, one with a round and a
part, one without a round, each of which rejects at a state which depends on a coin of the run's.
Definitions and `#guard` lines, as in Honest/Law/ToyRow.lean. No theorem is stated here.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

The second chain, sub-protocol by sub-protocol (the first chain is its front and the sealing round;
the shared chain has no round; every sub-protocol but "weigh" and "tests" accepts at every list that
its rounds can draw):
  `vbA`   "own a"   `vPA`: coins t, a. It says ans + t + a. The verifier's state takes that word as
     a number
  `vbB`   "own b"   `vPB`: coins t', b. It says a(0) + t' + b
  `vbS`   "spend"   `vPS`: no coin of its own; it spends a and b, of two owners, and sends a table:
     at p: a(p) + a + b. Its round draws an element; it stops where that is 13
  `vbD`   "draw"   `vPD`: it sends nothing. Its round draws an element, which the state takes
  `vbM`   "mid"   `vPM`: coin r. It says ans + r; its round draws the position at which the
     spender's table is read. A part between the draw and the rejection
  `vbW`   "weigh"   `vPW`: coin ρ. It says a(2) + ρ. It rejects where the two numbers add up to 1
     modulo 5: a sub-protocol with a round and a part that can reject
  `vbT`   "tests"   no round, no part: it rejects where the two numbers add up to a multiple of 5
  `vbL`   "late"   `vPL`: coin r'; it carries t. It says a(1) + r' + t, which the state takes. A
     part after the rejection
  `vbE`   "echo"   `vPE`: no coin; it carries t and r'. It says the word of "late" again; its
     simulator reads that word from `front`, under a condition at its entry (`onEcho`). The verifier
     compares the two words

  1  the sub-protocols, `Fv`
  2  the parts, `Bv`, `coinsV`, the prover, `ρv`
  3  the simulators, the sides, their members
  4  `fallQ`, `fallW`: the tests of "tests" and of "weigh" on the weight
  5  the `#guard` lines

What the lines check. The description passes its tests on the plan, and the book passes its eleven
tests. The run goes through at every coin and list that is tried, also where the description
rejects. The description accepts or rejects over five coins and five challenges: at each of the five
challenges two of the five coins fall, one of them at "weigh", and at each coin two challenges.
The stop: at the element 13 `silentAt` (Honest/Rule.lean) returns a stop, and the spender shows
`none`, as its simulator does. The spender's table is read at one position, at each of the 8 that
"mid" can draw. Which entries `Good.fresh` reads. The echo's condition at its entry, as a test, at
the run's own `front`. Evaluations at fixed coins: no distribution.

Limits.
  * A toy example.
  * `run` (Honest/Frame.lean) plays every part on after a rejection; a function that produces
    substitutes there is not in the files that this one imports: so "never called" is checked of no
    part here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription need roundlessBlock)
open VerifiableInference.Desc.BlockToy (St tree₃ drawD orc sealB frontQ endQ drawn)
open OnBytes.Slice (toF toE ofF ofE)

/-! ## 1 The sub-protocols and the description -/

def vpA : Place := ⟨3, none, 0, .K4⟩
def vpB : Place := ⟨3, none, 1, .K5⟩
def vpS : Place := ⟨3, none, 2, .K6⟩
def vpD : Place := ⟨3, none, 3, .K9⟩
def vpM : Place := ⟨3, none, 4, .K12⟩
def vpL : Place := ⟨3, none, 6, .K10⟩
def vpW : Place := ⟨3, none, 7, .K13⟩
def vpE : Place := ⟨3, none, 10, .K11⟩

/-- The first word of the one element of a stretch of one round; nothing at another shape. -/
def firstWord : List Fmt.RoundView → Option UInt64
  | [⟨[.e x], _⟩] => some x.1
  | _ => none

/-- One group of one column of one word. -/
def oneCol : List (List (Nat × List UInt64)) → Bool
  | [[(_, [_])]] => true
  | _ => false

/-- A round that sends one element and draws nothing. -/
def sayR : Fmt.DeclaredRound := { entry := { name := "CS", msg := 24 } }

/-- One element is sent; the state takes its first word as a number. -/
def vbA : Block St Nat :=
  { name := "own a", place := vpA, planOk := true, rounds := [sayR], oracles := [[]], before := []
    decide := fun s rs _ =>
      match firstWord rs with
      | some x => .ok { s with total := x.toNat }
      | none => .error "own a.one-element"
    claims := [], after := [] }

/-- One element is sent. -/
def vbB : Block St Nat :=
  { name := "own b", place := vpB, planOk := true, rounds := [sayR], oracles := [[]], before := []
    decide := fun s rs _ => (need "own b.one-element" (firstWord rs).isSome).map fun _ => s
    claims := [], after := [] }

/-- A root is sent; an element is drawn. -/
def vbS : Block St Nat :=
  { name := "spend", place := vpS, planOk := true
    rounds := [{ entry := { name := "CS", msg := 32, roots := 1, drawE := 1 } }]
    oracles := [[orc (2, 1)]], before := []
    decide := fun s _ _ => .ok s
    claims := [], after := [] }

/-- Nothing is sent; an element is drawn; the state takes its first word. -/
def vbD : Block St Nat :=
  { name := "draw", place := vpD, planOk := true, rounds := [{ entry := drawD }], oracles := [[]]
    before := []
    decide := fun s rs _ => .ok { s with claimed := (drawn rs).headD 0 }
    claims := [], after := [] }

/-- One element is sent; a position below 8 is drawn, and the chain's own tree is opened there. -/
def vbM : Block St Nat :=
  { name := "mid", place := vpM, planOk := true
    rounds := [{ entry := { name := "CS", msg := 24, poss := 1, logN := 3 }
                 opens := [(tree₃, .own 0)] }]
    oracles := [[]], before := [(3, 0)]
    decide := fun s rs gs =>
      (need "mid.one-element-one-column" ((firstWord rs).isSome && oneCol gs)).map fun _ => s
    claims := [], after := [] }

/-- A test of the verifier's inside a sub-protocol that has a round, on the state before it. -/
def weighOk (s : St) : Bool := (s.total + s.claimed) % 5 != 1

/-- One element is sent; it rejects where the two numbers add up to 1 modulo 5. -/
def vbW : Block St Nat :=
  { name := "weigh", place := vpW, planOk := true, rounds := [sayR], oracles := [[]], before := []
    decide := fun s rs _ =>
      (need "weigh.one-element" (firstWord rs).isSome).bind fun _ =>
        (need "weigh.a-weight-is-1" (weighOk s)).map fun _ => s
    claims := [], after := [] }

/-- The verifier's later test, on a state. -/
def weightOk (s : St) : Bool := (s.total + s.claimed) % 5 != 0

/-- No round: it rejects where the test fails. -/
def vbT : Block St Nat :=
  roundlessBlock "tests" 3 none 5 fun s => if weightOk s then .ok s else .error "a weight is 0"

/-- One element is sent; the state's third number takes its first word. -/
def vbL : Block St Nat :=
  { name := "late", place := vpL, planOk := true, rounds := [sayR], oracles := [[]], before := []
    decide := fun s rs _ =>
      match firstWord rs with
      | some x => .ok { s with claimed := x.toNat }
      | none => .error "late.one-element"
    claims := [], after := [] }

/-- One element is sent; it is compared with the word that the state took at "late": a test on a
value. -/
def vbE : Block St Nat :=
  { name := "echo", place := vpE, planOk := true, rounds := [sayR], oracles := [[]], before := []
    decide := fun s rs _ =>
      match firstWord rs with
      | some x => (need "echo.the-word" (x.toNat == s.claimed)).map fun _ => s
      | none => .error "echo.one-element"
    claims := [], after := [] }

/-- The second chain's sub-protocols between its front and its end. -/
def vBlocks : List (Block St Nat) := [vbA, vbB, vbS, vbD, vbM, vbW, vbT, vbL, vbE]

/-- The example's description. -/
def Fv : FileDescription Nat where
  S₁ := St
  S₂ := St
  S₃ := St
  Cl := Nat
  plans := (sealB.rounds, [], vBlocks.flatMap (·.rounds))
  tableDepth := 3
  wanted := []
  owed := []
  fileOk := true
  okStart := fun _ => true
  XiPub := Unit
  pub := fun _ => ()
  start₁ := fun _ => ⟨0, none, 0⟩
  start₂ := fun _ => ⟨0, none, 0⟩
  start₃ := fun _ _ _ => .ok ⟨0, none, 0⟩
  first := ⟨frontQ 1, [], [], [], sealB⟩
  shared := ⟨frontQ 2, [], [], [], roundlessBlock "end 2" 2 none 9 .ok⟩
  second := ⟨frontQ 3, vBlocks, [], [], endQ⟩
  fin := fun _ _ _ _ => true

/-! ## 2 The parts, the book, the prover -/

def vaA : Addr := ⟨vpA, 0⟩
def vaB : Addr := ⟨vpB, 0⟩
def vaS : Addr := ⟨vpS, 0⟩
def vaD : Addr := ⟨vpD, 0⟩
def vaM : Addr := ⟨vpM, 0⟩
def vaL : Addr := ⟨vpL, 0⟩
def vaW : Addr := ⟨vpW, 0⟩
def vaE : Addr := ⟨vpE, 0⟩

/-- The first owner. Two coins: t and a. It says the index's answer plus t plus a. -/
def vPA : Part L L Nat :=
  { takes := ⟨2, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).bind fun t => (c.1.fAt 1).map fun a =>
        ⟨[.e ⟨toF s.input.w₀.ans + t + a, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- The second owner. Two coins: t' and b. It says the index's word at 0 plus t' plus b. -/
def vPB : Part L L Nat :=
  { takes := ⟨2, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).bind fun t => (c.1.fAt 1).map fun b =>
        ⟨[.e ⟨toF (s.input.w₀.a 0) + t + b, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- The spender, which sends. No coin of its own; it spends a, of the first owner, and b, of the
second. Its table's word at every position is the index's plus a plus b. It stops where its own
challenge is the element 13: one of the p cubed elements of the extension field, p the prime: the
stated share. -/
def vPS : Part L L Nat :=
  { takes := ⟨0, 0⟩, spends := [("a to the spender", ⟨1, 0⟩), ("b to the spender", ⟨1, 0⟩)]
    carries := []
    bad := fun _ own => if own.head? == some (dE 13) then some "the challenge is 13" else none
    hid := fun _ _ _ => none
    badShare := ⟨1, 6277101731002175853884774869567645561244584131361410908161⟩
    hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.2.1.1.fAt 0).bind fun a => (c.2.1.2.1.fAt 0).map fun b =>
        ⟨[], [⟨2, 1, fun p _ => toF (s.input.w₀.a p) + a + b⟩]⟩,
      fun s => s.own⟩] }

/-- At the sub-protocol that draws. No coin; it sends nothing. -/
def vPD : Part L L Nat :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, fun s => s.own⟩] }

/-- Between the draw and the rejection. One coin, r. It says the index's answer plus r. -/
def vPM : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).map fun r =>
        ⟨[.e ⟨toF s.input.w₀.ans + r, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- At the sub-protocol with a round that can reject. One coin, ρ. It says the index's word at 2
plus ρ. -/
def vPW : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).map fun r =>
        ⟨[.e ⟨toF (s.input.w₀.a 2) + r, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- After the rejection. One coin, r'; it carries t. It says the index's word at 1 plus r' plus t.
-/
def vPL : Part L L Nat :=
  { takes := ⟨1, 0⟩, spends := [], carries := [("t to the late part", ⟨1, 0⟩)]
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.1.fAt 0).bind fun r => (c.2.2.1.fAt 0).map fun t =>
        ⟨[.e ⟨toF (s.input.w₀.a 1) + r + t, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- After "late": it says the word of "late" again. No coin of its own; it carries t and r'. It says
the index's word at 1 plus r' plus t. -/
def vPE : Part L L Nat :=
  { takes := ⟨0, 0⟩, spends := []
    carries := [("t to the echo", ⟨1, 0⟩), ("r' to the echo", ⟨1, 0⟩)]
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ s => (c.2.2.1.fAt 0).bind fun t => (c.2.2.2.1.fAt 0).map fun r =>
        ⟨[.e ⟨toF (s.input.w₀.a 1) + r + t, toF 0, toF 0⟩], []⟩,
      fun s => s.own⟩] }

/-- The example's book. -/
abbrev Bv : ProverCoinCounts :=
  { first := [], shared := []
    second := [(vaA, ⟨2, 0⟩), (vaB, ⟨2, 0⟩), (vaM, ⟨1, 0⟩), (vaW, ⟨1, 0⟩), (vaL, ⟨1, 0⟩)]
    ahead := [⟨"a to the spender", vaA, ⟨1, 0⟩, ⟨1, 0⟩, vaS, true⟩,
      ⟨"b to the spender", vaB, ⟨1, 0⟩, ⟨1, 0⟩, vaS, true⟩,
      ⟨"t to the late part", vaA, ⟨0, 0⟩, ⟨1, 0⟩, vaL, false⟩,
      ⟨"t to the echo", vaA, ⟨0, 0⟩, ⟨1, 0⟩, vaE, false⟩,
      ⟨"r' to the echo", vaL, ⟨0, 0⟩, ⟨1, 0⟩, vaE, false⟩]
    cuts := [(vpA, [1]), (vpB, [1]), (vpS, [1]), (vpD, [1]), (vpM, [1]), (vpW, [1]), (vpL, [1]),
      (vpE, [1])] }

/-- A run's coins: t, a · t', b · r · ρ · r'. -/
def coinsV (t a t' b r ρ' r' : UInt64) : Coins Bv :=
  ⟨(), (), (coin₂ t a, coin₂ t' b, coin₁ r, coin₁ ρ', coin₁ r', ())⟩

def Pv : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat :=
  { P with first := [], shared := []
           second := [⟨vpA, [vPA]⟩, ⟨vpB, [vPB]⟩, ⟨vpS, [vPS]⟩, ⟨vpD, [vPD]⟩, ⟨vpM, [vPM]⟩,
             ⟨vpW, [vPW]⟩, ⟨vpL, [vPL]⟩, ⟨vpE, [vPE]⟩] }

/-- The challenges at which "spend" draws e, "draw" draws χ and "mid" draws the position q. -/
def ρv (e χ : UInt64) (q : Nat) : Draws :=
  ⟨[d0], [], [d0, d0, dE e, dE χ, dP q, d0, d0, d0]⟩

def runV (c : Coins Bv) (ρ' : Draws) : Option Run := (run Fv Bv Pv w₀ 7 5 c ρ' none).toOption

/-! ## 3 The simulators, the sides, their members -/

/-- A simulator that says one coin of its own as an element, and reads nothing. -/
def eSim (a : Addr) : Sim Nat :=
  { addr := a, takes := ⟨1, 0⟩
    tell := fun _ _ _ _ c => some [⟨[.e (ofF (c.f ⟨0, by decide⟩), 0, 0)], []⟩] }

/-- Beside the spender: one coin of its own at each position that is asked; `none` where the part's
stop stops it, which it reads from the part's own challenges. -/
def vTs : Sim Nat :=
  { addr := vaS, takes := ⟨1, 0⟩
    tell := fun _ _ ds asks c =>
      if ds.head? == some (dE 13) then none else
      some [⟨[], (asks.headD []).map fun ps => ps.map fun p => (p, [ofF (c.f ⟨0, by decide⟩)])⟩] }

/-- Beside the part that sends nothing. -/
def vTd : Sim Nat := { addr := vaD, takes := ⟨0, 0⟩, tell := fun _ _ _ _ _ => some [⟨[], []⟩] }

/-- The items in the clear of the last round that `front` lists. -/
def lastVals (front : Before) : Option (List Fmt.ItemValue) := front.rounds.getLast?.map (·.2.1.vals)

/-- Beside the echo: no coin. It reads `front`: it says again what the last round there shows in the
clear. `none` where `front` lists no round. -/
def vTe : Sim Nat :=
  { addr := vaE, takes := ⟨0, 0⟩
    tell := fun _ front _ _ _ => (lastVals front).map fun v => [⟨v, []⟩] }

/-- **The last round that `front` lists shows the one element (y, 0, 0)**: an executable test. -/
def onEchoB (y : Cb.Gl.F) (front : Before) : Bool := lastVals front == some [.e (ofF y, 0, 0)]

/-- The first coins of the first two blocks of a list of blocks; 0 where there are fewer. -/
def twoCoins : (l : List (String × Due)) → CsAll l → Cb.Gl.F × Cb.Gl.F
  | _ :: _ :: _, c => ((c.1.fAt 0).toOption.getD (toF 0), (c.2.1.fAt 0).toOption.getD (toF 0))
  | _, _ => (toF 0, toF 0)

/-- The echo's condition at its entry: the last round before shows the index's word at 1 plus the
two carried coins: the word of "late", from the blocks that the echo carries. -/
def onEcho : (u : Member L L Nat Nat) → CsAll u.part.carries → Mid L Nat → Before → Prop :=
  fun u ca m front =>
    onEchoB (toF (m.st.input.w₀.a 1) + (twoCoins u.part.carries ca).2 +
      (twoCoins u.part.carries ca).1) front = true

def vSideA : Side St Nat L L Nat Nat := { block := vbA, row := [(vPA, eSim vaA)] }
def vSideB : Side St Nat L L Nat Nat := { block := vbB, row := [(vPB, eSim vaB)] }
def vSideS : Side St Nat L L Nat Nat := { block := vbS, row := [(vPS, vTs)] }
def vSideD : Side St Nat L L Nat Nat := { block := vbD, row := [(vPD, vTd)] }
def vSideM : Side St Nat L L Nat Nat := { block := vbM, row := [(vPM, eSim vaM)] }
def vSideW : Side St Nat L L Nat Nat := { block := vbW, row := [(vPW, eSim vaW)] }
def vSideL : Side St Nat L L Nat Nat := { block := vbL, row := [(vPL, eSim vaL)] }

def vSideE : Side St Nat L L Nat Nat := { block := vbE, row := [(vPE, vTe)] }

def vUA : Member L L Nat Nat := ⟨0, vbA.rounds.zip vbA.oracles, vPA, eSim vaA⟩
def vUB : Member L L Nat Nat := ⟨0, vbB.rounds.zip vbB.oracles, vPB, eSim vaB⟩
def vUS : Member L L Nat Nat := ⟨0, vbS.rounds.zip vbS.oracles, vPS, vTs⟩
def vUD : Member L L Nat Nat := ⟨0, vbD.rounds.zip vbD.oracles, vPD, vTd⟩
def vUM : Member L L Nat Nat := ⟨0, vbM.rounds.zip vbM.oracles, vPM, eSim vaM⟩
def vUW : Member L L Nat Nat := ⟨0, vbW.rounds.zip vbW.oracles, vPW, eSim vaW⟩
def vUL : Member L L Nat Nat := ⟨0, vbL.rounds.zip vbL.oracles, vPL, eSim vaL⟩

def vUE : Member L L Nat Nat := ⟨0, vbE.rounds.zip vbE.oracles, vPE, vTe⟩

/-! ## 4 The two tests on the weight, each on the state before its sub-protocol -/

/-- **The own test of "tests", on the state before it**: it returns something where that
sub-protocol will reject. It is given no coin and no input. -/
def fallQ (s : St) (_ : List Fmt.Drawn) : Option String :=
  if weightOk s then none else some "a weight is 0"

/-- **The own test of "weigh", on the state before it**: it returns something where that
sub-protocol will reject because of the weight. It is given no coin and no input. -/
def fallW (s : St) (_ : List Fmt.Drawn) : Option String :=
  if weighOk s then none else some "a weight is 1"

/-! ## 5 The `#guard` lines -/

def five : List UInt64 := [0, 1, 2, 3, 4]

-- the description's tests on the plan; the book's eleven; the places
#guard Fv.planOk
#guard Bv.word Fv == none
#guard Fv.placesOk
#guard Fv.lastChainFirstTreeNumber == 1
-- the sides fit
#guard vSideA.fits && vSideB.fits && vSideS.fits && vSideD.fits && vSideM.fits && vSideW.fits &&
  vSideL.fits && vSideE.fits
-- what the eight show: 9 + 1 + 2 · 0 + 3 + 4 · 0 + 2 + 4 at the position 2 · nothing · 9 + 5 ·
-- 0 + 8 · 0 + 6 + 1 · that word again
#guard (runV (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6)).map (fun r =>
    (r.shownAt vaA, r.shownAt vaB, r.shownAt vaS, r.shownAt vaD, r.shownAt vaM, r.shownAt vaW,
      r.shownAt vaL, r.shownAt vaE)) ==
  some ([⟨[.e (12, 0, 0)], []⟩], [⟨[.e (7, 0, 0)], []⟩], [⟨[], [[(2, [6])]]⟩], [⟨[], []⟩],
    [⟨[.e (14, 0, 0)], []⟩], [⟨[.e (8, 0, 0)], []⟩], [⟨[.e (7, 0, 0)], []⟩],
    [⟨[.e (7, 0, 0)], []⟩])
-- the description: 12 + 1: accepts; 12 + 3: "tests" rejects; 12 + 4: "weigh" rejects
#guard say Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6) none == "yes"
#guard say Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 3 6) none ==
  "no: the second chain: refused at tests: a weight is 0"
#guard say Fv Bv Pv w₀ 7 5 (coinsV 1 2 3 4 5 8 6) (ρv 0 4 6) none ==
  "no: the second chain: refused at weigh: weigh.a-weight-is-1"
-- the run goes through there all the same, and the part after the rejection is played
#guard (runV (coinsV 1 2 3 4 5 8 6) (ρv 0 3 6)).map (·.shownAt vaL) == some [⟨[.e (7, 0, 0)], []⟩]
-- at each challenge two coins of the five fall, one of them at "weigh"; at each coin two challenges
#guard five.all fun χ => (five.filter fun t =>
  say Fv Bv Pv w₀ 7 5 (coinsV t 2 3 4 5 8 6) (ρv 0 χ 6) none != "yes").length == 2
#guard five.all fun t => (five.filter fun χ =>
  say Fv Bv Pv w₀ 7 5 (coinsV t 2 3 4 5 8 6) (ρv 0 χ 6) none != "yes").length == 2
#guard five.all fun χ => (five.filter fun t =>
  say Fv Bv Pv w₀ 7 5 (coinsV t 2 3 4 5 8 6) (ρv 0 χ 6) none ==
    "no: the second chain: refused at weigh: weigh.a-weight-is-1").length == 1
-- no stop fires at a fall
#guard silentAt Fv Pv w₀ 7 5 (ρv 0 3 6) == none && silentAt Fv Pv w₀ 7 5 (ρv 0 4 6) == none
-- the stop: at the element 13: the silent set says so; the run returns an error; the spender,
-- played alone, shows `none`, and so does its simulator
#guard silentAt Fv Pv w₀ 7 5 (ρv 13 1 6) == some .bad
-- and that list is one that the rounds can draw: the silent set meets the due lists
#guard (ρv 13 1 6).due Fv
#guard (runV (coinsV 1 2 3 4 5 8 6) (ρv 13 1 6)).isNone
#guard vSideS.shows .own vUS (Cs.empty, (coin₁ 2, coin₁ 4, ()), ()) midY [dE 13] [[[2]]] == none
#guard vUS.tells .own (coin₁ 6) (wAt 5) none₀ [dE 13] [[[2]]] == none
-- elsewhere both show one column
#guard vSideS.shows .own vUS (Cs.empty, (coin₁ 2, coin₁ 4, ()), ()) midY [dE 0] [[[2]]] ==
  some [⟨[], [[(2, [6])]]⟩]
#guard vUS.tells .own (coin₁ 6) (wAt 5) none₀ [dE 0] [[[2]]] == some [⟨[], [[(2, [6])]]⟩]
-- the spender's table is read at one position, at each of the 8 that "mid" can draw; every such
-- list is one that the rounds can draw
#guard (List.range 8).all fun q => (ρv 0 1 q).due Fv &&
  (runV (coinsV 1 2 3 4 5 8 6) (ρv 0 1 q)).map (fun r => onePos (r.askedAt vaS)) == some true
#guard !(ρv 0 1 8).due Fv
-- which entries `Good.fresh` reads: of each owner for the spender one block; nothing else is given
-- to it or before it; t is given to the late part and to the echo, both after the spender
#guard (Bv.spentBy vaA vaS).map (·.name) == ["a to the spender"]
#guard (Bv.spentBy vaB vaS).map (·.name) == ["b to the spender"]
#guard (Bv.knownBy (orderOf Fv) vaA vaS).map (·.name) == []
#guard (Bv.knownBy (orderOf Fv) vaB vaS).map (·.name) == []
#guard (Bv.knownBy (orderOf Fv) vaA vaL).map (·.name) == ["a to the spender", "t to the late part"]
-- the echo: its condition at the entry, as a test, at the run's own `front`: true at the word of
-- "late" of the run's coins, false at another; its simulator says that word from `front`
#guard (runV (coinsV 1 2 3 4 5 8 6) (ρv 0 1 6)).map (fun r =>
    (onEchoB (toF 0 + toF 6 + toF 1) (r.beforeAt [] vaE), onEchoB (toF 8) (r.beforeAt [] vaE),
      vUE.tells .own Cs.empty (wAt 5) (r.beforeAt [] vaE) [d0] [[]])) ==
  some (true, false, some [⟨[.e (7, 0, 0)], []⟩])
#guard (Bv.knownBy (orderOf Fv) vaL vaE).map (·.name) == ["r' to the echo"]
-- at the coins (1, 2) and (2, 1) the first owner says the same word (by the body of `vPA` its word
-- changes with t + a alone; no line of this file evaluates more than this pair)
#guard vSideA.shows .own vUA (coin₂ 1 2, (), ()) midY [d0] [[]] ==
  vSideA.shows .own vUA (coin₂ 2 1, (), ()) midY [d0] [[]]

end ProofFile.Honest.Toy
