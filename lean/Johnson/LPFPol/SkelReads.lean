-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/SkelReads.lean: eight functions by which the tests on the plan (`FileDescription.planOk`,
Johnson/Desc/Block.lean, section 4) and the rows of the cut read a list of blocks read the blocks'
skeletons alone (Johnson/LPFPol/SkR/Skel.lean: with the rounds and the oracles whole). Statements
and proofs. General in the state and in the type of claims.
  `SameSk bs' bs`: the two lists have one list of skeletons.
  `SameSk.rounds`, `.places`, `.blocksOk`, `.sent`, `.oracles`, `.before`, `.cut`, `.firstBad`:
      eight readers.
  `last_rounds`: a chain's last block's rounds, off the flat list's last skeleton.
Limits. That `planOk` reads a first chain by these alone is shown in DescAtPolicy.lean, for
`fileDescBy`'s records. No reader here for `wantedOk` or `owedOk`, which are no part of `planOk`.
Nothing on what a block decides. Nothing on soundness.

-/
import Johnson.LPFPol.SkR.Skel
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFPol
open LPFPol.SkR
open VerifiableInference.Desc

variable {S S' Cl Cl' : Type}

/-- One list of skeletons. -/
def SameSk (bs' : List (Block S' Cl')) (bs : List (Block S Cl)) : Prop := bs'.map skel = bs.map skel

namespace SameSk
variable {bs' : List (Block S' Cl')} {bs : List (Block S Cl)}

theorem map {β : Type} (h : SameSk bs' bs) (f : Skel → β) :
    (bs'.map fun b => f (skel b)) = bs.map fun b => f (skel b) := by
  have e := congrArg (List.map f) h
  rw [List.map_map, List.map_map] at e
  exact e

theorem flatMap {β : Type} (h : SameSk bs' bs) (f : Skel → List β) :
    (bs'.flatMap fun b => f (skel b)) = bs.flatMap fun b => f (skel b) := by
  have e := congrArg (List.flatMap f) h
  rw [List.flatMap_map, List.flatMap_map] at e
  exact e

theorem all (h : SameSk bs' bs) (f : Skel → Bool) :
    (bs'.all fun b => f (skel b)) = bs.all fun b => f (skel b) := by
  have e := congrArg (fun l => List.all l f) h
  dsimp only at e
  rw [List.all_map, List.all_map] at e
  exact e

theorem rounds (h : SameSk bs' bs) : bs'.flatMap (·.rounds) = bs.flatMap (·.rounds) :=
  h.flatMap fun k => k.rounds

theorem places (h : SameSk bs' bs) : placesOf bs' = placesOf bs :=
  h.map fun k => (k.name, k.place, k.rounds.length)

/-- `Block.shaped` on a skeleton. -/
def shapedSk (k : Skel) : Bool :=
  k.oracles.length == k.rounds.length &&
    (k.rounds.zip k.oracles).all fun x => x.2.length == x.1.entry.roots &&
      x.2.all fun o => (o.tenants.map fun t => t.main + t.mask).sum == o.words &&
        o.tenants.all fun t => t.degree == 1 || t.degree == 3

theorem blocksOk (h : SameSk bs' bs) : VerifiableInference.Desc.blocksOk bs' =
    VerifiableInference.Desc.blocksOk bs :=
  h.all fun k => k.planOk && shapedSk k

/-- `sentOf`'s row on a skeleton. -/
def sentSk (k : Skel) : List (Nat × Nat) := k.oracles.flatMap fun l => l.map fun o =>
    (o.logLength, o.words)

theorem sent (h : SameSk bs' bs) : sentOf bs' = sentOf bs := h.flatMap sentSk

theorem oracles (h : SameSk bs' bs) : oraclesOf bs' = oraclesOf bs :=
  h.flatMap fun k => k.oracles.flatMap id

/-- `cutOf`'s row on a skeleton. -/
def cutSk (k : Skel) : String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat) :=
  (k.name, k.place, k.rounds.length, k.oracles.length,
    (k.oracles.zipIdx.filter fun x => !x.1.isEmpty).map (fun x => (x.2, x.1)), k.before)

theorem cut (h : SameSk bs' bs) :
    VerifiableInference.PlanWritten.cutOf bs' = VerifiableInference.PlanWritten.cutOf bs :=
        h.map cutSk

theorem before (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) :
    ∀ {bs' : List (Block S' Cl')} {bs : List (Block S Cl)}, SameSk bs' bs → ∀ n,
      beforeAt D O c n bs' = beforeAt D O c n bs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | b' :: l', b :: l, h, n => by
    have h1 : skel b' = skel b := (List.cons.inj h).1
    have h2 : SameSk l' l := (List.cons.inj h).2
    have eb : b'.before = b.before := congrArg Skel.before h1
    have er : b'.rounds = b.rounds := congrArg Skel.rounds h1
    unfold beforeAt
    rw [eb, er, before D O c h2]

theorem firstBad (h : SameSk bs' bs) :
    VerifiableInference.Desc.firstBad bs' = VerifiableInference.Desc.firstBad bs := by
  have e := congrArg (fun l => (l.find? fun k => !(k.planOk && shapedSk k)).map (·.name)) h
  dsimp only at e
  rw [List.find?_map, List.find?_map, Option.map_map, Option.map_map] at e
  exact e

end SameSk

/-- A chain's last block's rounds stand in the flat list's last skeleton. -/
theorem last_rounds (c : Chain S Cl) :
    ((c.blocksInOrder.map skel).getLast?.map fun k => k.rounds) = some c.last.rounds := by
  unfold Chain.blocksInOrder
  simp only [List.map_cons, List.map_append, List.map_nil, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.map_some]
  rfl

theorem last_same {c' : Chain S' Cl'} {c : Chain S Cl} (h : SameSk c'.blocksInOrder c.blocksInOrder) :
    c'.last.rounds = c.last.rounds := by
  have e' := last_rounds c'
  have e := last_rounds c
  rw [show c'.blocksInOrder.map skel = c.blocksInOrder.map skel from h, e] at e'
  exact (Option.some.inj e').symm

end LPFPol

#print axioms LPFPol.SameSk.before
#print axioms LPFPol.SameSk.cut
#print axioms LPFPol.last_same
