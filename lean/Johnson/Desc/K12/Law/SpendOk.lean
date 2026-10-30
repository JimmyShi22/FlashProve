-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SpendOk.lean: a test, with code, of what a bound over the chain of a proximity
test (the kind K12) asks of a place's rounds and sizes beside `Chain.Pub`.

Definitions with code alone; no theorem; no Mathlib beneath. The library's three laws that take a
chain's blocks off (`foldSem_of`, `csSem_of`, `baseSem_of`, OnBytes/Slice/ChainSem.lean) ask of the
written rounds and the sizes: `FoldRounds dE dT` (the fold's first round sends one element and draws
one; the repeated round sends two and draws one), `SendsDraws` of the base case's first round (it
draws one element), and `Sg.Sized` (C.a ≤ 32, Z.a ≤ C.a, C.r + C.l ≤ 2 ^ C.a, Z.r + Z.l ≤ 2 ^ Z.a).
`Chain.Pub` holds none of these.
Main names:
  `sdB w ns ne np a`: the written round sends ns elements, draws ne elements and np positions below
    2 ^ a, and nothing else: the premises of the library's `sendsDraws_of` as a Boolean.
  `spendL`, `spendOk`, `spendNo`: the named clauses over the place's declared rounds, cut as `pubOk`
    cuts them.
  `spendSpoiled`, `spendLines`: controls, and the lines that a run prints.
Limits: What the three laws ask beside (radii below the distance; facts on codes) is no matter of
the place's rounds and is not here. `sdB` asks «logN = a» also at a round that draws no position,
which is more than `SendsDraws` needs there: it can only refuse an honest place. A root in a message
is no element, so a first fold that sends its own mask (a root beside the element) is not refused.
Evaluated at the four proximity tests of the two stored example proofs, the full-size one and the
smaller one: true at each [the prints are not in this library].

-/
import Johnson.Desc.K12.Law.PubOk

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)

/-- The elements among a message's items (the library's nS, RoundsOf.lean:49, typed again so that no
Mathlib stands beneath; tied by nSB_eq in Johnson/Desc/K12/Law/ChainSpend.lean). -/
def nSB : List Fmt.Item → Nat
  | [] => 0
  | .e :: l => nSB l + 1
  | .answer :: l => nSB l + 1
  | _ :: l => nSB l

def sdB (w : WR) (ns ne np a : Nat) : Bool :=
  decide (w.entry.trits = 0) && decide (w.kind ≠ .sealed) && decide (w.kind ≠ .seeds) &&
    decide (w.entry.drawNZ ≤ w.entry.drawE) && decide (w.entry.logN ≤ 64) &&
    decide (nSB w.items = ns) && decide (w.entry.drawE = ne) && decide (w.entry.poss = np) &&
    decide (w.entry.logN = a)

def sizedL (a : Fmt.M1.Stage) : Clauses :=
  [("sized.small", decide (a.C.a ≤ 32)), ("sized.short", decide (a.Z.a ≤ a.C.a)),
   ("sized.roomC", decide (a.C.r + a.C.l ≤ 2 ^ a.C.a)),
       ("sized.roomZ", decide (a.Z.r + a.Z.l ≤ 2 ^ a.Z.a))]

def spendL : Nat → Fmt.M1.Stage → List Fmt.M1.Stage → List WR → Clauses
  | j, a, [], l =>
    match l with
    | [dL, _] => tag j (("lambda", sdB dL 1 1 0 0) :: sizedL a)
    | _ => [(toString j ++ ":cut at the last stage", false)]
  | j, a, b :: rest, l =>
    match l with
    | dE :: dT :: l' =>
      match (dT :: l').drop (kk a) with
      | _ :: _ :: l'' =>
        tag j (("eps", sdB dE 1 1 0 0) :: ("two", sdB dT 2 1 0 0) :: sizedL a) ++ spendL (j + 1) b
            rest l''
      | _ => [(toString j ++ ":cut: no two rounds behind the fold's", false)]
    | _ => [(toString j ++ ":cut: no two rounds of a fold", false)]

def spendAll (p : P12) : Clauses :=
  match p.nums.stages, writtenOf p.nums with
  | a :: rest, some (_ :: l) => spendL 0 a rest l
  | _, _ => [("no stage, or the declared rounds cannot be written", false)]

/-- The test: every clause says yes. -/
def spendOk (p : P12) : Bool := ok (spendAll p)

def spendNo (p : P12) : List String := ((spendAll p).filter (!·.2)).map (·.1)

/-- Controls: each must say false. -/
def spendSpoiled (p : P12) : List (String × P12) :=
  let st (f : List Fmt.M1.Stage → List Fmt.M1.Stage) : P12 :=
      { p with nums := { p.nums with stages := f p.nums.stages } }
  let at0 (l : List Fmt.M1.Stage) (i : Nat) (f : Fmt.M1.Stage → Fmt.M1.Stage) : List Fmt.M1.Stage :=
    l.zipIdx.map fun x => if x.2 == i then f x.1 else x.1
  [("stage 0: C.a := 33", st (at0 · 0 fun s => { s with C := { s.C with a := 33 } })),
   ("stage 1: the mask code longer than the main", st
       (at0 · 1 fun s => { s with Z := { s.Z with a := s.C.a + 1 } })),
   ("stage 0: the main tail fills the word", st
       (at0 · 0 fun s => { s with C := { s.C with r := 2 ^ s.C.a } })),
   ("stage 1: the mask tail fills the word", st
       (at0 · 1 fun s => { s with Z := { s.Z with r := 2 ^ s.Z.a } })),
   ("one stage alone", st (·.take 1))]

def spendLines (tagS : String) (p : P12) : List String :=
  s!"{tagS}.SPEND\tspendOk {spendOk p}\tclauses {(spendAll p).length}\trefusing: {spendNo p}" ::
    (spendSpoiled p).map fun x =>
      s!"{tagS}.SPEND.control\t{x.1}\tspendOk {spendOk x.2}\trefusing {(spendNo x.2).length}: \
          {(spendNo x.2).take 3}"

end H2K.Pub
