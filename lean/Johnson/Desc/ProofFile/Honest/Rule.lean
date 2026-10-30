-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Rule.lean: definitions that fix where a statement on all honest sides
of one description is made. `silentAt` is the one set of lists of challenges outside which such a
statement speaks. `Sides` holds the lists of parts of one description, each with its parameters of
`Good` (Honest/Side.lean). `Lettered.goodAt` and `Lettered.owedAt` say what has to be proved of each
list. The one definition of all hypotheses, `Owed`, is in Honest/Owed.lean, after the function that
it names (Honest/Walk.lean). Definitions only: no theorem is stated, and no rule that joins sides.

Why this is defined before any rule. `Good` has free parameters. Two of them, On and `bud`, read a
run: what comes before a part, its challenges, its positions. A parameter that reads challenges can
be false at some lists, and there the condition says nothing. So it has to be fixed where On and
`bud` have to be proved, before sides are written against them: at one description, one book and one
prover, whose prover's sides are the sides' own; at every input of a relation, all coins, and every
list of challenges that the rounds can draw, outside the one named set; of one run's own five
values, each computed by a function of Honest/Frame.lean, Honest/Side.lean or Honest/MidW.lean. On
and `bud` are conclusions there, not hypotheses on the given list.

  1  `chainStopAt`, `silentAt`   the one silent set: whether, and by which stop, the honest side
     stops at a list of challenges; computed from the parts' stops alone, with no coin among its
     arguments
  2  `Lettered`, `Lettered.side`, `Sides`, `Sides.prover`, `Sides.seated`   a list of parts at a
     place with its parameters; its side, at the description's own sub-protocol there; the lists of
     a description's three chains; the prover whose sides are theirs; that every list is at a place
  3  `preOf`, `Lettered.goodAt`, `Lettered.owedAt`   what has to be proved of a list

Limits.
  * Definitions alone: nothing here shows that a list of parts of the protocol meets them.
  * A and B have to be proved nowhere here: nothing ties A to a chain's start, or one place's B to
    the next place's A. With A := False at every side `plays` and `acc` hold vacuously.
  * `earlier` in `goodAt` is on the caller's word: nothing here compares it with a description. At a
    wrong list the hypothesis of `Good.exact` on `opened` can be false at a run's own values, and
    `exact` says nothing there. `Owed` lays `earlierOf F`.
  * A side's sub-protocol is the description's own sub-protocol at the place, as the functions that
    build the description have wrapped it (guarded, joined, retyped), not the kind's or the lot's
    definition. What ties the two has to be proved by whoever proves `Good` of a side.
  * The silent set is named, not measured: nothing here compares the shares that parts state
    (`Part.badShare`, `Part.hidShare`) with it.
  * One request: a batch of several is not modelled.
  * `Owed` (Honest/Owed.lean) computes the stored tables' opened columns from the run's own index
    and the stored tables' pads and encoding randomness (w₀, rc). What a simulator of the whole
    protocol, which is given neither, would supply there is not stated.
  * A fall (`Fall`, Honest/Side.lean) at a place at which no list is defined is read by nothing
    here. Nothing compares a fall's stated share with its test.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The one silent set -/

section
variable {S Cl V W Y : Type}

/-- Whether a chain's prover's sides stop, sub-protocol by sub-protocol of the description's own
flat list, as `play` asks their stops. `loc`: the challenges before the list that the stops are
given. No coin is among its arguments. -/
def chainStopAt (v : Option V) : List (Block S Cl) → List (Placed V W Y) → List Fmt.Drawn →
    List Fmt.Drawn → Option Why
  | [], _, _, _ => none
  | b :: bs, hs, loc, ds =>
    let own := ds.take b.rounds.length
    ((hs.find? fun h => h.place == b.place).bind fun h => rowStopAt v h.parts loc own).or
      (chainStopAt v bs hs (loc ++ own) (ds.drop b.rounds.length))

end

/-- **The one silent set**: whether the honest side stops at a list of challenges, and by which
stop: the first that fires, in the order in which `run` and `runC` (Honest/Walk.lean) play the
chains. Both stops are in it. It is computed from the stops alone: no coin is among its arguments,
and no fault can take a stop's place. `none` if the request has no trace. -/
def silentAt (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (ρ : Draws) : Option Why :=
  (H.trace w₀ x).bind fun tr =>
    let w : Local W₀ Rc Xi Tr := ⟨w₀, rc, x, tr⟩
    let w' : Common W₀ Rc Ky := ⟨w₀, rc, H.key x⟩
    (chainStopAt (Face.own.sees w) F.first.blocksInOrder H.first [] ρ.first).or
      ((chainStopAt (Face.shared.sees w') F.shared.blocksInOrder H.shared [] ρ.shared).or
        (chainStopAt (Face.own.sees w) F.second.blocksInOrder H.second ρ.first ρ.second))

/-! ## 2 The sides of one description -/

/-- **A list of parts at a place, with the parameters of `Good`**, at a book. It holds no
sub-protocol: that is taken from the description's own list, by the place (`Lettered.side`). -/
structure Lettered (Bk : ProverCoinCounts) (S Cl V W Y Pb : Type) where
  place : Place
  /-- each part paired with a term of type `Sim` -/
  row : List (Part V W Y × Sim Pb)
  A : Coins Bk → S → Mid W Y → Env → Prop
  B : Coins Bk → S → Mid W Y → Env → Prop
  On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop
  bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop

/-- **Its side**: the list with the sub-protocol of a description's list that is at its place, as
the functions that build the description have wrapped it; `none` if there is none. `fs`: the chain's
falls. -/
def Lettered.side {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (L : Lettered Bk S Cl V W Y Pb)
    (bs : List (Block S Cl)) (fs : List (Fall S) := []) : Option (Side S Cl V W Y Pb) :=
  Side.seated bs L.place L.row fs

/-- **The lists of one description's three chains**, typed at that description's own states, claims
and instance; and each chain's falls (`Fall`, Honest/Side.lean): most descriptions' chains have
none. A fall is at the place of the sub-protocol whose own step it excuses; if a list is defined
there, `Lettered.side` puts it into that list's side. The second chain's start, which is no
sub-protocol and has no place, has no field for a fall: none is known there. -/
structure Sides (F : FileDescription Xi) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type) where
  first : List (Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  shared : List (Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  second : List (Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  falls₁ : List (Fall F.S₁) := []
  falls₂ : List (Fall F.S₂) := []
  falls₃ : List (Fall F.S₃) := []

/-- **The prover whose sides are these lists**: H's other fields stay. -/
def Sides.prover {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prover W₀ Rc Xi Ky Tr X₀ X :=
  { H with
    first := G.first.map fun L => ⟨L.place, L.row.map (·.1)⟩
    shared := G.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩
    second := G.second.map fun L => ⟨L.place, L.row.map (·.1)⟩ }

/-- **Every list is at a place of its chain**: an executable test. -/
def Sides.seated {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Bool :=
  G.first.all (fun L => (L.side F.first.blocksInOrder).isSome) &&
    G.shared.all (fun L => (L.side F.shared.blocksInOrder).isSome) &&
    G.second.all fun L => (L.side F.second.blocksInOrder).isSome

/-! ## 3 What has to be proved of a list -/

section
variable {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type}

/-- **The declared rounds whose reads are handed to the parts at a place**, as `readsBefore`
(Side.lean) takes them: those of the earlier chains, which the caller lays, and then the rounds of
the sub-protocols of the chain's own list `bs` before the place `a` (the same list as
`roundsBefore`, Field.lean; all the list's rounds if no sub-protocol is at `a`). -/
def preOf (chain firstTree : Nat) (earlier : List (Nat × Nat × List Fmt.DeclaredRound))
    (bs : List (Block S Cl)) (a : Place) : List (Nat × Nat × List Fmt.DeclaredRound) :=
  earlier ++ [(chain, firstTree, (bs.takeWhile fun b => b.place != a).flatMap (·.rounds))]

/-- The list's side meets `Good`, at the list's own parameters. `bs`: its chain's list in the
description. `fs`: its chain's falls: `acc` is asked outside the one at the list's place. It holds
vacuously if no sub-protocol of `bs` is at the list's place: `Owed.seats` excludes that. `earlier`:
the earlier chains' declared rounds. The parameter `pre` of `Good` is made here, from `earlier` and
`bs` (`preOf`). -/
def Lettered.goodAt (L : Lettered Bk S Cl V W Y Pb)
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) (bs : List (Block S Cl))
    (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S) := []) : Prop :=
  ∀ σ, L.side bs fs = some σ →
    Good (preOf chain firstTree earlier bs L.place) φ σ Bk ord chain firstTree L.A L.B L.On L.bud

/-- **On and `bud` hold at one run's values**, for each part u of the list, at its address a. It
says: the book lends u its carried blocks `ca`, from the coins `k`; the function `mid` returns m at
a; `On u ca m` holds at `r.beforeAt st a`; and `bud` holds at r's challenges at a and at the
positions that r reads of u's tables. `k`, `chain`, `mid`, `r` and `st` are arguments here: `Owed`
supplies all of them from one run, with `mid` := `orRefused` (Owed.lean) of `midAtW` or
`midSharedAtW` (MidW.lean) at that run's arguments and `st` := the stored tables' columns that it
reads. `called`: which parts the run has called. Its default counts every part as called. Of a part
that was not called `bud` alone is asked: it reads the part's own challenges and the positions read
of its tables, and a round that was not played is listed under its part's address all the same. It
holds vacuously if no sub-protocol of `bs` is at the list's place: `Owed.seats` excludes that. -/
def Lettered.owedAt (L : Lettered Bk S Cl V W Y Pb) (bs : List (Block S Cl)) (k : Coins Bk)
    (chain : Nat) (mid : Addr → Except Refusal (Mid W Y)) (r : Run)
    (st : List (Nat × Nat × List UInt64)) (called : Addr → Bool := fun _ => true) : Prop :=
  ∀ σ, L.side bs = some σ → ∀ u ∈ σ.members,
    L.bud u.number (r.drawnAt ⟨L.place, u.number⟩) (r.askedAt ⟨L.place, u.number⟩) ∧
    (called ⟨L.place, u.number⟩ = true → ∃ ca m,
      carriedAt Bk k chain ⟨L.place, u.number⟩ u.part = .ok ca ∧
      mid ⟨L.place, u.number⟩ = .ok m ∧
      L.On u ca m (r.beforeAt st ⟨L.place, u.number⟩))

end

end ProofFile.Honest

#print axioms ProofFile.Honest.chainStopAt
#print axioms ProofFile.Honest.silentAt
#print axioms ProofFile.Honest.Lettered
#print axioms ProofFile.Honest.Lettered.side
#print axioms ProofFile.Honest.Sides
#print axioms ProofFile.Honest.Sides.prover
#print axioms ProofFile.Honest.Sides.seated
#print axioms ProofFile.Honest.preOf
#print axioms ProofFile.Honest.Lettered.goodAt
#print axioms ProofFile.Honest.Lettered.owedAt
