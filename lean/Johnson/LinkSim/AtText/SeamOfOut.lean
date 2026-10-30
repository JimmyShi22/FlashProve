-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamOfOut.lean: two outputs that agree where the verifier looks give two
runs of the link's protocol that disclose the same.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

The link's prover is defined twice in Johnson/Prover/Link/. linkAll
(Johnson/Prover/Link/LinkAll.lean) gives all rounds, trees and groups at a whole family of
challenges; its output is a BOut. linkNext gives each round's message as a function of the
challenges so far; linkNext_at (Johnson/Prover/Link/LinkCausal.lean) proves that it agrees with
linkAll. An algorithm that is given all challenges at once, such as the simulator's, has only the
first form. This file brings both forms under one statement.

What this file proves. Both statements hold for all parameters.
  Spec.sameOfOut, sameOfOut    suppose the message function next reads the output O and next'
               reads O' (ReadsOut), and O and O' satisfy SameAt. Then next and next' satisfy
               SameItems and SameCols (SeamShows.lean): round by round their items give the same
               plain part (the items in the protocol's type), and at every position of a tree
               of the prover that the challenges ask for they give the same symbol.
  Spec.showsOfOut, showsOfOut    hence, by Spec.showsOfNext (SeamShows.lean), the two runs of the
               strategies made of next and next' against a verifier message ρ disclose the same
               (Shows, Johnson/LinkSim/SpecForm.lean).

How it fits. nextOfOut, with valsAt and colAt, is part of the definition of the simulator: simLink
(Johnson/LinkSim/AtText/SpecExact.lean) plays the strategy made of nextOfOut of simAll, and
homeSim Z (Johnson/LinkSim/AtHome/SpecHome.lean) is simLink at constants of the library and at Z's
decision function (Spec.lean, "the guard on what a simulator may read"). So these three definitions
occur in the statement of the main theorem, homeExactAt (Johnson/LinkSim/AtHome/HomeExactAll.lean).
SeamGroups.lean uses showsOfOut for the prover's strategy (linkNext) and the simulator's. These
lemmas are used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean), through
SeamGroups.lean and Exact.lean.

The other names (namespace OnBytes.LinkSim.Seam; the lemmas that join the algorithms to the
protocol's types).
  valsAt, colAt    round i's items of an output (the values that the round sends in the clear), and
               the column of the tree that round i sends.
  nextOfOut O      the function that gives round i's items and tree of O, whatever challenges it
               is given. An output holds one tree a round, so nextOfOut ignores the tree's number
               within the round. A strategy made of it has looked at all challenges from its first
               message on (see SpecExact.lean's limits).
  ReadsOut next O Ds    at each round, at the challenges so far, next gives round i's items and
               tree of O.
  readsOut_nextOfOut, readsOut_linkNext    both forms satisfy it (the second: linkNext_at,
               Johnson/Prover/Link/LinkCausal.lean).
  orcT_congr       two families of columns that agree at (tree k, position x) give the same symbol
               of the protocol's type at that position.
  SameAt ds O O' Ds    the two outputs have the same items in every round, and the same column at
               every (tree of the prover, position) that the challenges ask for, read at the round
               that sends the tree (seatOf gives, for a tree's number, that round and the tree's
               number within it).
  sameAt_refl      every output satisfies SameAt with itself, by reflexivity; this shows only that
               the premise can hold.

Notes. SameAt is about the trees' columns (BOut.tr), not the groups (BOut.gs). That linkAll's
groups are its trees' columns at the lists of sampled positions is proved in SeamGroups.lean, not
here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamShows
import Johnson.Prover.Link.LinkCausal

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes.LinkSim
open OnBytes.Flat (linkProtocolOfRoundData)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK PlainOf View XO)
open TypedOracleCompiler.Run.PQ (RD SOf uL drawnSL posAtS posAtT PosT wanted)

/-- Round i's items of an output. -/
def valsAt (O : BOut) (i : ℕ) : List Fmt.ItemValue := ((O.rs[i]?).map (·.vals)).getD []

/-- The column of the tree that round i of an output sends. -/
def colAt (O : BOut) (i : ℕ) : ℕ → List UInt64 := (O.tr[i]?).getD fun _ => []

/-- The function that gives round i's items and tree of O, whatever challenges it is given. -/
def nextOfOut (O : BOut) : ℕ → List Fmt.Drawn → MsgV := fun i _ => ⟨valsAt O i, fun _ => colAt O i⟩

/-- At each round, at the challenges so far, next gives round i's items and tree of O. -/
def ReadsOut (next : ℕ → List Fmt.Drawn → MsgV) (O : BOut) (Ds : List Fmt.Drawn) : Prop :=
  ∀ i, (next i (Ds.take i)).vals = valsAt O i ∧ (next i (Ds.take i)).col = fun _ => colAt O i

/-- nextOfOut O reads O. -/
theorem readsOut_nextOfOut (O : BOut) (Ds : List Fmt.Drawn) : ReadsOut (nextOfOut O) O Ds :=
  fun _ => ⟨rfl, rfl⟩

/-- linkNext reads linkAll at the same data and coins, at the challenges Ds continued by empty
challenges. -/
theorem readsOut_linkNext (P : _root_.Desc.K15.P15) (S : OnBytes.Slice.Sz) (t : ℕ) (X : LIn S)
    (C : LCoins) (Ds : List Fmt.Drawn) :
    ReadsOut (linkNext P S t X C) (linkAll P S t X C fun j => Ds.getD j ⟨[], [], [], none⟩) Ds :=
  fun i => linkNext_at P S t X C Ds i

/-- Two families of columns that agree at (tree k, position x) give the same symbol of the
protocol's type there. -/
theorem orcT_congr : ∀ (ts : List Fmt.Shape) (f f' : ℕ → ℕ → List UInt64) (k x : ℕ) (q : PosT ts),
    posAtT ts k x = some q → f k x = f' k x → orcT ts f q = orcT ts f' q
  | [], _, _, _, _, _, hq, _ => by cases hq
  | s :: ts, f, f', 0, x, q, hq, h => by
      unfold posAtT at hq
      split at hq
      · cases hq
        show (fun k : Fin s.W => (f 0 x).getD k.val 0) = fun k : Fin s.W => (f' 0 x).getD k.val 0
        rw [h]
      · cases hq
  | s :: ts, f, f', k + 1, x, q, hq, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.1 hq
      exact orcT_congr ts (fun n => f (n + 1)) (fun n => f' (n + 1)) k x q' hq' h

/-- The two outputs have the same items in every round, and the same column at every (tree of the
prover, position) that the challenges ask for. -/
def SameAt (ds : List RD) (O O' : BOut) (Ds : List Fmt.Drawn) : Prop :=
  (∀ i, i < ds.length → valsAt O i = valsAt O' i) ∧
    ∀ nx ∈ wanted ds Ds, ∀ j k, seatOf ds nx.1 = some (j, k) → colAt O j nx.2 = colAt O' j nx.2

/-- Statement only; proved as sameOfOut below. ReadsOut twice and SameAt give SameItems and
SameCols. -/
def Spec.sameOfOut : Prop :=
  ∀ (ds : List RD) (next next' : ℕ → List Fmt.Drawn → MsgV) (O O' : BOut) (Ds : List Fmt.Drawn),
    ReadsOut next O Ds → ReadsOut next' O' Ds → SameAt ds O O' Ds →
    SameItems ds next next' Ds ∧ SameCols ds next next' Ds

/-- Proof of Spec.sameOfOut. -/
theorem sameOfOut : Spec.sameOfOut := by
  intro ds next next' O O' Ds h h' hS
  refine ⟨fun j d hd => ?_, fun nx hnx j k d q hs _ hq => ?_⟩
  · have hj : j < ds.length := (List.getElem?_eq_some_iff.1 hd).1
    rw [(h j).1, (h' j).1, hS.1 j hj]
  · refine orcT_congr d.trees _ _ k nx.2 q hq ?_
    rw [(h j).2, (h' j).2]
    exact hS.2 nx hnx j k hs

/-- Statement only; proved as showsOfOut below. The same, down to the two runs: they disclose the
same (Shows). -/
def Spec.showsOfOut : Prop :=
  ∀ (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (X : Type) (dec : X → View → Bool) (x : X)
    (next next' : ℕ → List Fmt.Drawn → MsgV) (O O' : BOut)
    (ρ : Rho (_root_.Run.Twin.up (SOf C ds))),
    ReadsOut next O (drawnSL C ds ρ.2) → ReadsOut next' O' (drawnSL C ds ρ.2) →
    SameAt ds O O' (drawnSL C ds ρ.2) →
    Shows (linkProtocolOfRoundData C ds a xs dec) x ((stratOf C ds next).run ρ).1 ((stratOf C ds next').run ρ).1

/-- Proof of Spec.showsOfOut. -/
theorem showsOfOut : Spec.showsOfOut := fun C ds a xs X dec x next next' O O' ρ h h' hS =>
  showsOfNext C ds a xs X dec x next next' ρ (sameOfOut ds next next' O O' _ h h' hS).1
    (sameOfOut ds next next' O O' _ h h' hS).2

/-- SameAt of an output with itself, by reflexivity; it shows only that the premise can hold. -/
theorem sameAt_refl (ds : List RD) (O : BOut) (Ds : List Fmt.Drawn) : SameAt ds O O Ds :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.sameOfOut
#print axioms OnBytes.LinkSim.Seam.showsOfOut
#print axioms OnBytes.LinkSim.Seam.readsOut_linkNext
