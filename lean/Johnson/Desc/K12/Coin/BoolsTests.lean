-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BoolsTests.lean: THE PUBLIC PREMISES OF THE PROXIMITY TEST's LAW IN THE PLAIN
FORM, BOTH ARMS, AND THE PROMISES `FirstOpens` | `FirstOpensOwn`, AS TESTS WITH CODE. DEFINITIONS
WITH CODE ALONE; NO THEOREM. Cut by a program out of Bools.lean and BoolsOwn.lean, to the letter, so
that a run can evaluate them without the law's proofs beneath: it stands over the block's text and
the tests on the plan, not over Sheet.lean.

  `likeB`, `likeAllB`, `likeOk` · `wantsB` · `treesWalk`, `treesOk` · `firstOpensB` · `PlaceB`: the
    first arm (the first fold's mask came earlier).
  `treesOwnWalk`, `treesOwnOk` · `firstOpensOwnB` · `PlaceOwnB`: the second arm (the first fold
    sends its own mask).
What each test's yes gives: Bools.lean (`like_of_ok`, `wants_of_B`, `trees_of_ok`,
`firstOpens_of_B`, `atPlace_of`) and BoolsOwn.lean (`treesOwn_of_ok`, `firstOpensOwn_of_B`,
`atPlaceOwn_of`).
Limits: evaluated is not proved; a test's no does not refute its proposition. Nothing has been
evaluated. No soundness is claimed.

-/
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.Law.SpendOk
import Johnson.Desc.K12.Law.DealOk
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (writtenOf WR spendOk kk)
open H2K.First (gpOf Plain)

/-! ## The first arm -/

def likeB (d : RDT) (w : WR) : Bool :=
  decide (d.entry = w.entry) && decide (d.kind = w.kind) && decide (d.items = w.items) &&
    decide (d.trees = w.tree.toList) && d.stored.isEmpty

def likeAllB : List RDT → List WR → Bool
  | [], [] => true
  | d :: ds, w :: ws => likeB d w && likeAllB ds ws
  | _, _ => false

def likeOk (π : P12) (ds : List RDT) : Bool :=
  match writtenOf π.nums with
  | some (w0 :: l) => likeAllB ds (w0 :: l)
  | _ => false

def wantsB (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ) : List RDT → List Fmt.DeclaredRound → Bool
  | [], [] => true
  | d :: ds, r :: rs =>
    d.stored.isEmpty && r.stored.isEmpty && decide (d.opens = r.opens.map fun o => num o.2) &&
      (r.opens.all fun o => dep (num o.2) == some o.1.a) && wantsB dep num ds rs
  | _, _ => false

def treesWalk : List Fmt.M1.Stage → Fmt.M1.Stage → List WR → Bool
  | [], _, _ => true
  | b :: rest, a, l =>
    match l with
    | dE :: dT :: l' =>
      dE.tree.isNone && dT.tree.isNone &&
        match (dT :: l').drop (kk a) with
        | dS :: dC :: l'' => dS.tree.isSome && dC.tree.isNone && treesWalk rest b l''
        | _ => false
    | _ => false

def treesOk (π : P12) : Bool :=
  match π.nums.stages, writtenOf π.nums with
  | a :: rest, some (_ :: l) => treesWalk rest a l
  | _, _ => false

def firstOpensB (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12) : Bool :=
  match π.nums.stages, t.st.groups[t.g]?, t.st.layout t.g with
  | a :: _, some G0, some Ly =>
    match gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly with
    | some D =>
      decide (D.opens.map (fun o => num o.2) = D.ts.map no) &&
        D.ts.all fun z => decide (no z < base)
    | none => true
  | _, _, _ => true

/-- The tests on a place and its stretch's data, together. -/
def PlaceB (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) :
    Bool :=
  π.early && decide (π.answers = 1) && (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk && spendOk π &&
    H2K.First.dealOk π && likeOk π (dB :: dt) && dB.trees.isEmpty &&
    decide (H2K.First.ownN π = 0) &&
    wantsB (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth num (dB :: dt)
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds && treesOk π

/-! ## The second arm -/

def treesOwnWalk : List Fmt.M1.Stage → Fmt.M1.Stage → List WR → Bool
  | [], _, _ => false
  | b :: rest, a, l =>
    match l with
    | dE :: dT :: l' =>
      dE.tree.isSome && dT.tree.isNone &&
        match (dT :: l').drop (kk a) with
        | dS :: dC :: l'' => dS.tree.isSome && dC.tree.isNone && treesWalk rest b l''
        | _ => false
    | _ => false

def treesOwnOk (π : P12) : Bool :=
  match π.nums.stages, writtenOf π.nums with
  | a :: rest, some (_ :: l) => treesOwnWalk rest a l
  | _, _ => false

def firstOpensOwnB (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12) : Bool :=
  match π.nums.stages, t.st.groups[t.g]?, t.st.layout t.g with
  | a :: _, some G0, some Ly =>
    match gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly with
    | some D =>
      decide (D.opens.map (fun o => num o.2) = D.ts.map no) &&
        (D.mems.all fun s => decide (no s.t < base)) && decide (no D.fresh.t = base)
    | none => true
  | _, _, _ => true

/-- The tests on a place whose first fold sends its own mask, and on its stretch's data. -/
def PlaceOwnB (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) : Bool :=
  π.early && decide (π.answers = 1) && (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk && spendOk π &&
    H2K.First.dealOk π && likeOk π (dB :: dt) && dB.trees.isEmpty &&
    decide (H2K.First.ownN π = 1) &&
    wantsB (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth num (dB :: dt)
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds && treesOwnOk π

end VerifiableInference.Desc.K12.Coin
