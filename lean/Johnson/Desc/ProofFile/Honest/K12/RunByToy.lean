-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByToy.lean: tests (`#guard`) that evaluate `runBy` (RunBy.lean)
and `testAll` (Test.lean) at two small made-up examples and compare them. Example 1 is Toy.lean's:
two members in one tree, the fresh table sent before the test. Example 2 is ToyOwn.lean's: the first
fold sends its own fresh table, and the first opening has two trees. That the two definitions agree
is a theorem (`runBy_eq`, RunByEq.lean). The tests add what no theorem covers: whether the block
(`verdict`) accepts the output, and the warnings in `RunOut.no`. The last section tests `denseAt`
alone, at a made-up row.

By what. `same` compares the rounds (what is sent and what each round sampled), the trees at
positions 0 to 39, and the opened columns. The comment above each `#guard` says what it checks. Most
warnings and all tests with a changed random value run at example 1 alone.

Limits.
- Three stages of tiny sizes, (k, h) = (3, 0), (1, 1), (0, 0), at both examples. The first stage's
  mask table and its tails are all 0.
- `RunIn.ofTest` (RunOf.lean) makes the input of `runBy` from the job's `rec₀`, `rows₀` and
  `trees₀`, which `testAll` reads too. An error in these three is not found.
- No test reaches the warning that the last stage's claim cannot be written out.
- A row with a written-out factor inside a run: RunByToyForm.lean. Other shapes of a first stage:
  RunManyToy.lean.
- `#guard` runs compiled code outside Lean's kernel and leaves no theorem. That the block accepts an
  output is a test at one example. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyOwn
import Johnson.Desc.ProofFile.Honest.K12.RunOf
import Johnson.Desc.ProofFile.Honest.K12.RunBy
import Johnson.Desc.ProofFile.Honest.K12.Halve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.ByToy
open ProofFile.Honest.K12.Toy (csOf restList list₁ list₂ sorts upVal)
open Johnson.Prover.Link (BOut)

def at' (ds : List Fmt.Drawn) (r : ℕ) : Fmt.Drawn := ds.getD r ⟨[], [], [], none⟩

/-- The random values of example 1, in the order of Toy.lean's `whole`. upS: one of the sender's 23
made one larger (the oracle messages' tails and pads; the fresh table's coefficients and tails). up:
one of the second part's. -/
def coins₁ (up : Option ℕ) (upS : Option ℕ := none) : TestCoins :=
  let S := stretchOf (csOf 23 ProofFile.Honest.K12.Toy.senderList upS)
  ⟨fun i => S.e (14 + i), fun _ q => S.e (21 + q),
    fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩, (stretchOf (csOf 125 restList up)).e⟩

/-- The random values of example 2. The first part has nine of its own (`ownList`). -/
def coins₂ (up : Option ℕ) : TestCoins :=
  let S := stretchOf (csOf 14 ProofFile.Honest.K12.ToyOwn.senderList none)
  let O := stretchOf (csOf 9 ProofFile.Honest.K12.ToyOwn.ownList none)
  ⟨O.e, fun _ q => O.e (7 + q), fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩,
    (stretchOf (csOf 125 restList up)).e⟩

def term₁ (ds : List Fmt.Drawn) : BOut :=
  testAll ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none) (at' ds)
def term₂ (ds : List Fmt.Drawn) : BOut :=
  testAll ProofFile.Honest.K12.ToyOwn.J 0 ProofFile.Honest.K12.ToyOwn.fr (coins₂ none) (at' ds)

def by₁ (S : Seams) (up : Option ℕ) (ds : List Fmt.Drawn) : RunOut :=
  runBy S (RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ up)) (at' ds)
def by₂ (S : Seams) (up : Option ℕ) (ds : List Fmt.Drawn) : RunOut :=
  runBy S (RunIn.ofTest ProofFile.Honest.K12.ToyOwn.J 0 ProofFile.Honest.K12.ToyOwn.fr (coins₂ up)) (at' ds)

/-- The same rounds: what is sent, item for item, and what each round sampled. -/
def sameR (a : RunOut) (b : BOut) : Bool :=
  a.rs.map (·.vals) == b.rs.map (·.vals) && a.rs.map (·.drawn) == b.rs.map (·.drawn)

/-- The same items sent. What a round sampled is not compared. -/
def sameSent (a : RunOut) (b : BOut) : Bool := a.rs.map (·.vals) == b.rs.map (·.vals)

/-- The same tree at each round, at forty positions. -/
def sameTrees (a : RunOut) (b : BOut) : Bool :=
  a.tr.length == b.tr.length &&
    (List.range a.tr.length).all fun i => (List.range 40).all fun x =>
      (a.tr.getD i fun _ => []) x == (b.tr.getD i fun _ => []) x

/-- The same rounds, trees and opened columns. -/
def same (a : RunOut) (b : BOut) : Bool := sameR a b && sameTrees a b && a.gs == b.gs

/-- The last element that round i sampled, replaced by b. -/
def factorAt (i : ℕ) (b : UInt64 × UInt64 × UInt64) (ds : List Fmt.Drawn) : List Fmt.Drawn :=
  ds.modify i fun d => { d with elems := d.elems.dropLast ++ [b] }

/-- w raised by the prime, where the sum fits 64 bits. -/
def lift (w : UInt64) : UInt64 := if w < 4294967295 then w + 18446744069414584321 else w

/-- List 1 with `lift` applied to each word of each element. -/
def list₃ : List Fmt.Drawn :=
  list₁.map fun d => { d with elems := d.elems.map fun x => (lift x.1, lift x.2.1, lift x.2.2) }

/-- Three words that decode to 0 and are not all 0. -/
def zero' : UInt64 × UInt64 × UInt64 := (18446744069414584321, 0, 18446744069414584321)

-- both examples' stages pass the hypothesis of runBy_eq
#guard StagesOk ProofFile.Honest.K12.Toy.J.p.nums.stages && StagesOk ProofFile.Honest.K12.ToyOwn.J.p.nums.stages
-- thirteen rounds; "SEND seed" is round 5 and round 9, and samples more than one element
#guard (by₁ .lib none list₁).rs.length == 13 && (by₂ .lib none list₁).rs.length == 13
#guard [5, 9].all fun i => decide (1 < (at' list₁ i).elems.length)
-- example 1
#guard same (by₁ .lib none list₁) (term₁ list₁) && same (by₁ .lib none list₂) (term₁ list₂)
#guard ProofFile.Honest.K12.Toy.verdict (by₁ .lib none list₁).rs (by₁ .lib none list₁).gs == "ok"
#guard ProofFile.Honest.K12.Toy.verdict (by₁ .lib none list₂).rs (by₁ .lib none list₂).gs == "ok"
-- example 2
#guard same (by₂ .lib none list₁) (term₂ list₁) && same (by₂ .lib none list₂) (term₂ list₂)
#guard ProofFile.Honest.K12.ToyOwn.verdict (by₂ .lib none list₁).rs (by₂ .lib none list₁).gs == "ok"
#guard ProofFile.Honest.K12.ToyOwn.verdict (by₂ .lib none list₂).rs (by₂ .lib none list₂).gs == "ok"
-- words raised by the prime: another list, the same values sent
#guard list₃ != list₁
#guard same (by₁ .lib none list₃) (term₁ list₃) && same (by₂ .lib none list₃) (term₂ list₃)
#guard sameSent (by₁ .lib none list₃) (term₁ list₁)
-- a sampled factor 0, at each switch, in two encodings, at both examples
#guard [5, 9].all fun i => [(0, 0, 0), zero'].all fun b =>
  same (by₁ .lib none (factorAt i b list₁)) (term₁ (factorAt i b list₁)) &&
    same (by₂ .lib none (factorAt i b list₁)) (term₂ (factorAt i b list₁))
-- what is sent there differs from list 1's, and the block rejects
#guard [5, 9].all fun i =>
  !sameSent (by₁ .lib none (factorAt i (0, 0, 0) list₁)) (term₁ list₁) &&
    ProofFile.Honest.K12.Toy.verdict (by₁ .lib none (factorAt i (0, 0, 0) list₁)).rs
      (by₁ .lib none (factorAt i (0, 0, 0) list₁)).gs != "ok"
-- the warnings: none at the three lists; then each case with its own warning
#guard [list₁, list₂, list₃].all fun ds =>
  (by₁ .lib none ds).no == [] && (by₂ .lib none ds).no == []
#guard [(5, 0), (9, 1)].all fun i => [(0, 0, 0), zero'].all fun b =>
  (by₁ .lib none (factorAt i.1 b list₁)).no.contains
      s!"the switch after stage {i.2}: the sampled factor is 0 or missing" &&
    (by₂ .lib none (factorAt i.1 b list₁)).no.contains
      s!"the switch after stage {i.2}: the sampled factor is 0 or missing"
#guard (runBy .lib
  { RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none) with
    door := ProofFile.Honest.K12.Toy.noRec } (at' list₁)).no.contains
      "stage 0: the verifier's state holds no claim; an empty row is used"
#guard (runBy .lib
  { RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none) with own := true }
  (at' list₁)).no.contains ("the input and the test's parameters disagree on whether the first " ++
    "fold sends its own fresh table")
#guard (let I := RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none)
  (runBy .lib { I with first := { I.first with M := I.first.M.map (·.dropLast) } }
    (at' list₁)).no.contains ("the input's first-stage rows or tails do not have the sizes that " ++
      "the stage states"))
-- list 1 cut after round 4: the two agree, and there are warnings
#guard same (by₁ .lib none (list₁.take 5)) (term₁ (list₁.take 5)) &&
  (by₁ .lib none (list₁.take 5)).no != []
-- one stage alone; no stage
#guard (let I := RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none)
  (runBy .lib { I with p := { I.p with nums := { I.p.nums with
    stages := I.p.nums.stages.take 1 } } } (at' list₁)).no.contains
      "the list of stages fails StagesOk")
#guard (let I := RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none)
  (runBy .lib { I with p := { I.p with nums := { I.p.nums with stages := [] } } }
    (at' list₁)).no == ["the list of stages fails StagesOk"])
-- stages that fail StagesOk, with the last stage's main message half as long as the row that the
-- switch leaves: the masking word is shorter than the row, the warning says so, and the output is
-- not testAll's
def shortStages : List Fmt.M1.Stage :=
  ProofFile.Honest.K12.Toy.J.p.nums.stages.modify 2 fun s => { s with C := { s.C with l := s.C.l / 2 } }
def shortJ : TestJob ℕ Unit :=
  { ProofFile.Honest.K12.Toy.J with
    p := { ProofFile.Honest.K12.Toy.J.p with
      nums := { ProofFile.Honest.K12.Toy.J.p.nums with stages := shortStages } } }
def shortBy : RunOut :=
  runBy .lib (RunIn.ofTest shortJ 0 ProofFile.Honest.K12.Toy.fr (coins₁ none)) (at' list₁)
#guard !StagesOk shortJ.p.nums.stages
#guard shortBy.no.contains ("the last stage: a list of the masking word is shorter than what it " ++
  "masks; the rest is sent unmasked")
#guard !same shortBy (testAll shortJ 0 ProofFile.Honest.K12.Toy.fr (coins₁ none) (at' list₁))
-- with Seams.halving
#guard same (by₁ .halving none list₁) (term₁ list₁) && same (by₂ .halving none list₂) (term₂ list₂)
-- negative tests: one random value for each of 16 uses made one larger: rounds or trees differ
#guard sorts.all fun i =>
  !(sameR (by₁ .lib (some i) list₁) (term₁ list₁) &&
    sameTrees (by₁ .lib (some i) list₁) (term₁ list₁))
-- each of the sender's 23 made one larger: rounds, trees or opened columns differ from testAll's
-- at the unchanged values, and equal testAll's at the changed ones
#guard (List.range 23).all fun i =>
  let R := runBy .lib
    (RunIn.ofTest ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none (some i))) (at' list₁)
  !same R (term₁ list₁) &&
    same R (testAll ProofFile.Honest.K12.Toy.J 0 ProofFile.Honest.K12.Toy.fr (coins₁ none (some i)) (at' list₁))
-- the first sent element one larger: rejected
#guard ProofFile.Honest.K12.Toy.verdict (upVal 1 0 (by₁ .lib none list₁).rs)
  (by₁ .lib none list₁).gs != "ok"
#guard ProofFile.Honest.K12.ToyOwn.verdict (upVal 1 0 (by₂ .lib none list₁).rs)
  (by₂ .lib none list₁).gs != "ok"

/-! ## `denseAt` -/

def e3 (n : ℕ) : OnBytes.E := OnBytes.E.ofTriple (Fmt.M1.FoldOwn.mk .two n)

/-- A tensor on v variables; dv: those of the written-out factor. -/
def tens (v s : ℕ) (dv : List ℕ) : OnBytes.Tensor :=
  { scalar := e3 s
    pairs := (List.range v).map fun i =>
      if dv.contains i then (OnBytes.oneE, OnBytes.oneE)
      else (e3 (s + 2 * i + 1), e3 (s + 2 * i + 2))
    denseVars := dv, values := ((List.range 9).map fun i => e3 (s + 40 + i)).toArray, first := 2 }

/-- Four rows of four entries; two mask rows of four. -/
def stW : Fmt.M1.Stage := ⟨⟨5, 4, 2⟩, ⟨5, 4, 2⟩, 2, 1, 2⟩

def rowW (more : List OnBytes.Tensor) : OnBytes.GroupRow :=
  { c := { tensors := [tens 4 1 [], tens 4 20 [1, 3], tens 4 30 [0]] ++ more
           entries := [(5, e3 77), (5, e3 78), (11, e3 79)] }
    d := ((List.range 3).map e3).toArray, target := e3 9 }

/-- x with each word reduced modulo the prime. -/
def norm (x : Fmt.M1.E) : Fmt.M1.E := Fmt.Fld.two.addE x Fmt.Fld.zeroE

def readsAs (c : Array Fmt.M1.E) (f : OnBytes.Form) : Bool :=
  (List.range 16).all fun i => norm (c.getD i Fmt.Fld.zeroE) == norm (f.entry i).triple

#guard (denseAt (rowW []) stW).c.size == 16 && (denseAt (rowW []) stW).d.size == 8
#guard readsAs (denseAt (rowW []) stW).c (rowW []).c
#guard (denseAt (rowW []) stW).d.toList ==
  (List.range 3).map (fun i => (e3 i).triple) ++ List.replicate 5 Fmt.Fld.zeroE
#guard (denseAt (rowW []) stW).t == (e3 9).triple
-- a vector on the mask table that is too long: cut
#guard (denseAt { rowW [] with d := ((List.range 11).map e3).toArray } stW).d.toList ==
  (List.range 8).map fun i => (e3 i).triple
-- without the two tensors that have a written-out factor the entries differ
#guard !readsAs (denseAt (rowW []) stW).c { (rowW []).c with tensors := [tens 4 1 []] }
-- a tensor of fewer variables
#guard (denseAt (rowW [tens 3 50 []]) stW).c.size == 16
#guard readsAs (denseAt (rowW [tens 3 50 []]) stW).c (rowW [tens 3 50 []]).c
-- there Form.writeOut (through dense) differs from Form.entry: hence denseAt's second branch
#guard !readsAs (VerifiableInference.Desc.K12.dense (rowW [tens 3 50 []]).c 4)
  (rowW [tens 3 50 []]).c

end ProofFile.Honest.K12.Light.ByToy

#print axioms ProofFile.Honest.K12.Light.ByToy.at'
#print axioms ProofFile.Honest.K12.Light.ByToy.coins₁
#print axioms ProofFile.Honest.K12.Light.ByToy.coins₂
#print axioms ProofFile.Honest.K12.Light.ByToy.term₁
#print axioms ProofFile.Honest.K12.Light.ByToy.term₂
#print axioms ProofFile.Honest.K12.Light.ByToy.by₁
#print axioms ProofFile.Honest.K12.Light.ByToy.by₂
#print axioms ProofFile.Honest.K12.Light.ByToy.sameR
#print axioms ProofFile.Honest.K12.Light.ByToy.sameSent
#print axioms ProofFile.Honest.K12.Light.ByToy.sameTrees
#print axioms ProofFile.Honest.K12.Light.ByToy.same
#print axioms ProofFile.Honest.K12.Light.ByToy.factorAt
#print axioms ProofFile.Honest.K12.Light.ByToy.lift
#print axioms ProofFile.Honest.K12.Light.ByToy.list₃
#print axioms ProofFile.Honest.K12.Light.ByToy.zero'
#print axioms ProofFile.Honest.K12.Light.ByToy.shortStages
#print axioms ProofFile.Honest.K12.Light.ByToy.shortJ
#print axioms ProofFile.Honest.K12.Light.ByToy.shortBy
#print axioms ProofFile.Honest.K12.Light.ByToy.e3
#print axioms ProofFile.Honest.K12.Light.ByToy.tens
#print axioms ProofFile.Honest.K12.Light.ByToy.stW
#print axioms ProofFile.Honest.K12.Light.ByToy.rowW
#print axioms ProofFile.Honest.K12.Light.ByToy.norm
#print axioms ProofFile.Honest.K12.Light.ByToy.readsAs
