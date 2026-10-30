-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/SkR/Skel.lean: A TWIN, MADE BY PROGRAM, of Johnson/Desc/ProofFile/Law/Skel/Skel.lean:
that file's text with two fields more in the skeleton: a block's rounds and its oracles, whole. The
namespace is LPFPol.SkR. What follows is that file's own head, turned at two places, where it lists
the skeleton's fields and in its limits, so that it is true of this file.
THE SKELETON OF A BLOCK: a block
(Johnson/Desc/Block.lean) less its functions, as plain data with a decidable equality; and what
the makers of blocks and of flat lists do to it. Definitions, statements and proofs. General in
the state and in the type of claims.
Why. The steps by which `ProofFile.onlineDescription` puts the proof file's description together run no block's
decision and no run of claims: they read names, places, counts and tests on the plan. With these
laws such a step can be asked at written skeletons.
  `Skel`, `skel b`     name, place, the number of rounds, the length of `oracles`, its non-empty
                      members with their numbers, THE ROUNDS AND THE ORACLES THEMSELVES, `before`,
                      `planOk`, the names of the runs of claims and of the runs behind the batching
  `toldFrom k l`      the non-empty members of l, numbered from k
  `Skel.quiet`, `Skel.andThen`, `Skel.retype`, `Skel.bare`: the makers' texts on skeletons
  `skel_guarded`, `skel_andThen`, `skel_retype`, `skel_quiet`, `bare_skel`, `noRounds_skel`
  `LinkSk`, `LinkSk.flat`, `ChainSk`, `ChainSk.flat`: `Link.blocksInOrder` and `Chain.blocksInOrder` on skeletons
  `flat_link`: a link's flat list has the skeletons of `LinkSk.flat`, where the batching's
    skeleton is k at the link's own gatherer. `flat_chain`: the like for a chain.
Limits. (That file's first limit, that the rounds themselves are not in a skeleton, does not hold
of this one.) By its type a link's batching may hang on the gatherer that it is handed: `flat_link`
takes its skeleton as a premise. Nothing on soundness.

-/
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFPol.SkR
open VerifiableInference.Desc

variable {S Cl : Type}

/-- The non-empty members of a list of lists, numbered from k. -/
def toldFrom : Nat → List (List Oracle) → List (Nat × List Oracle)
  | _, [] => []
  | k, x :: l => if x.isEmpty then toldFrom (k + 1) l else (k, x) :: toldFrom (k + 1) l

/-- **A block less its functions.** -/
structure Skel where
  name : String
  place : Place
  nRounds : Nat
  nOracles : Nat
  /-- the rounds and the oracles themselves: what this twin adds -/
  rounds : List Fmt.DeclaredRound
  oracles : List (List Oracle)
  told : List (Nat × List Oracle)
  before : List (Nat × Nat)
  planOk : Bool
  claims : List String
  after : List String
  deriving DecidableEq

/-- **The skeleton of a block.** -/
def skel (b : Block S Cl) : Skel :=
  { name := b.name, place := b.place, nRounds := b.rounds.length, nOracles := b.oracles.length
    rounds := b.rounds, oracles := b.oracles
    told := toldFrom 0 b.oracles, before := b.before, planOk := b.planOk
    claims := b.claims.map (·.1), after := b.after.map (·.1) }

/-- `roundlessBlock` on skeletons. -/
def Skel.quiet (name : String) (chain : Nat) (link : Option Nat) (piece : Nat) : Skel :=
  { name := name, place := ⟨chain, link, piece, .frame⟩, nRounds := 0, nOracles := 0, told := []
    rounds := [], oracles := []
    before := [], planOk := true, claims := [], after := [] }

/-- `Block.hasNoClaimsAndNothingAfter` on skeletons. -/
def Skel.bare (k : Skel) : Bool := k.claims.isEmpty && k.after.isEmpty

/-- `Block.andThen` on skeletons: the second one's told rounds are numbered behind the first's. -/
def Skel.andThen (name : String) (p q : Skel) : Skel :=
  { name := name, place := p.place, nRounds := p.nRounds + q.nRounds
    nOracles := p.nOracles + q.nOracles
    rounds := p.rounds ++ q.rounds, oracles := p.oracles ++ q.oracles
    told := p.told ++ q.told.map fun x => (x.1 + p.nOracles, x.2)
    before := p.before ++ q.before, planOk := p.planOk && q.planOk
    claims := p.claims ++ q.claims, after := p.after ++ q.after }

/-- `Block.retype` on skeletons. -/
def Skel.retype (k : Skel) : Skel :=
  { k with planOk := k.planOk && k.claims.isEmpty, claims := [] }

/-! ### told -/

theorem toldFrom_append (a b : List (List Oracle)) :
    ∀ k, toldFrom k (a ++ b) = toldFrom k a ++ toldFrom (k + a.length) b := by
  induction a with
  | nil => intro k; simp [toldFrom]
  | cons x a ih =>
    intro k
    have e : k + 1 + a.length = k + (x :: a).length := by
      simp only [List.length_cons]; omega
    simp only [List.cons_append, toldFrom]
    split
    · rw [ih, e]
    · rw [ih, e, List.cons_append]

theorem toldFrom_add (b : List (List Oracle)) (n : Nat) :
    ∀ k, toldFrom (k + n) b = (toldFrom k b).map fun x => (x.1 + n, x.2) := by
  induction b with
  | nil => intro k; simp [toldFrom]
  | cons x b ih =>
    intro k
    have e : k + n + 1 = k + 1 + n := by omega
    simp only [toldFrom]
    split
    · rw [e, ih]
    · rw [e, ih, List.map_cons]

/-! ### the makers of blocks -/

theorem skel_guarded (same : S → S → Bool) (but : Place → Bool) (b : Block S Cl) :
    skel (b.guarded same but) = skel b := by
  simp [skel, Block.guarded, List.map_map, Function.comp_def]

theorem skel_andThen (n : String) (p q : Block S Cl) :
    skel (p.andThen n q) = (skel p).andThen n (skel q) := by
  have e := toldFrom_add q.oracles p.oracles.length 0
  simp only [Nat.zero_add] at e
  simp [skel, Block.andThen, Skel.andThen, toldFrom_append, e]

theorem skel_retype {Cl' : Type} (b : Block S Cl) :
    skel (b.retype : Block S Cl') = (skel b).retype := by
  simp [skel, Block.retype, Skel.retype]

theorem skel_quiet (name : String) (chain : Nat) (link : Option Nat) (piece : Nat)
    (f : S → Except String S) :
    skel (roundlessBlock name chain link piece f : Block S Cl) = Skel.quiet name chain link piece := by
  simp [skel, roundlessBlock, Skel.quiet, toldFrom]

theorem bare_skel (b : Block S Cl) : b.hasNoClaimsAndNothingAfter = (skel b).bare := by
  simp [skel, Block.hasNoClaimsAndNothingAfter, Skel.bare]

theorem noRounds_skel (b : Block S Cl) : b.rounds.isEmpty = ((skel b).nRounds == 0) := by
  cases h : b.rounds <;> simp [skel, h]

/-! ### flat lists -/

/-- A link less its functions; `batch`: the batching's skeleton. -/
structure LinkSk where
  name : String
  chain : Nat
  number : Nat
  hear : List Skel
  order : List (Nat × String)
  orderAfter : List (Nat × String)
  batch : Skel
  close : List Skel

/-- `Link.blocksInOrder` on skeletons. -/
def LinkSk.flat (L : LinkSk) : List Skel :=
  { Skel.quiet (L.name ++ ": laid") L.chain (some L.number) 0 with
      planOk :=
        namesOk (L.hear.zipIdx.flatMap fun b => b.1.claims.map fun c => (b.2, c)) L.order &&
        namesOk (L.hear.zipIdx.flatMap fun b => b.1.after.map fun c => (b.2, c)) L.orderAfter &&
        L.close.all Skel.bare && L.batch.bare } ::
    L.hear ++ [L.batch,
      Skel.quiet (L.name ++ ": behind the batching") L.chain (some L.number) (L.hear.length + 2)] ++
    L.close ++
    [Skel.quiet (L.name ++ ": cleared") L.chain (some L.number)
      (L.hear.length + L.close.length + 3)]

/-- A chain less its functions. -/
structure ChainSk where
  first : Skel
  front : List Skel
  links : List LinkSk
  back : List Skel
  last : Skel

/-- `Chain.blocksInOrder` on skeletons. -/
def ChainSk.flat (c : ChainSk) : List Skel :=
  let bare := fun k : Skel => { k with planOk := k.planOk && k.bare }
  bare c.first :: c.front.map bare ++ c.links.flatMap LinkSk.flat ++ c.back.map bare ++
    [bare c.last]

/-- A link's skeleton, at the batching's skeleton k. -/
def linkSk (L : Link S Cl) (k : Skel) : LinkSk :=
  { name := L.name, chain := L.chain, number := L.number, hear := L.hear.map skel, order := L.order
    orderAfter := L.orderAfter, batch := k, close := L.close.map skel }

theorem claimNames (bs : List (Block S Cl)) :
    (bs.zipIdx.flatMap fun b => b.1.claims.map fun c => (b.2, c.1)) =
      (bs.map skel).zipIdx.flatMap fun b => b.1.claims.map fun c => (b.2, c) := by
  simp [List.zipIdx_map, List.flatMap_map, skel, List.map_map, Function.comp_def]

theorem afterNames (bs : List (Block S Cl)) :
    (bs.zipIdx.flatMap fun b => b.1.after.map fun c => (b.2, c.1)) =
      (bs.map skel).zipIdx.flatMap fun b => b.1.after.map fun c => (b.2, c) := by
  simp [List.zipIdx_map, List.flatMap_map, skel, List.map_map, Function.comp_def]

theorem all_bare (bs : List (Block S Cl)) : bs.all Block.hasNoClaimsAndNothingAfter = (bs.map skel).all Skel.bare := by
  rw [List.all_map]
  exact congrArg (fun f => bs.all f) (funext fun b => bare_skel b)

/-- **A link's flat list, in skeletons.** -/
theorem flat_link (L : Link S Cl) (k : Skel)
    (hk : skel (L.batch (claimsInBy L.each L.hear L.order)) = k) :
    L.blocksInOrder.map skel = (linkSk L k).flat := by
  have h0 : skel ({ roundlessBlock (L.name ++ ": laid") L.chain (some L.number) 0 L.lay with
      planOk := orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
        L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter } :
        Block S Cl) =
      { Skel.quiet (L.name ++ ": laid") L.chain (some L.number) 0 with
        planOk := namesOk ((L.hear.map skel).zipIdx.flatMap fun b =>
            b.1.claims.map fun c => (b.2, c)) L.order &&
          namesOk ((L.hear.map skel).zipIdx.flatMap fun b =>
            b.1.after.map fun c => (b.2, c)) L.orderAfter &&
          (L.close.map skel).all Skel.bare && k.bare } := by
    rw [← claimNames, ← afterNames, ← all_bare, ← hk, ← bare_skel]
    simp [skel, roundlessBlock, Skel.quiet, toldFrom, orderOk, orderAfterOk]
  unfold Link.blocksInOrder LinkSk.flat linkSk
  simp only [List.map_cons, List.map_append, List.map_nil, h0, hk, skel_quiet, List.length_map]

/-- A chain's skeleton, at its links' skeletons. -/
def chainSk (c : Chain S Cl) (ls : List LinkSk) : ChainSk :=
  { first := skel c.first, front := c.front.map skel, links := ls, back := c.back.map skel
    last := skel c.last }

theorem skel_bared (b : Block S Cl) :
    skel { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } =
      { skel b with planOk := (skel b).planOk && (skel b).bare } := by
  rw [← bare_skel]
  rfl

/-- **A chain's flat list, in skeletons**: where each link's flat list is its skeleton's. -/
theorem flat_chain (c : Chain S Cl) (ls : List LinkSk)
    (hl : c.links.map (fun L => L.blocksInOrder.map skel) = ls.map LinkSk.flat) :
    c.blocksInOrder.map skel = (chainSk c ls).flat := by
  have h1 : (c.links.flatMap Link.blocksInOrder).map skel = ls.flatMap LinkSk.flat := by
    rw [List.map_flatMap, List.flatMap_def, List.flatMap_def, hl]
  unfold Chain.blocksInOrder ChainSk.flat chainSk
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_map, h1, skel_bared,
    Function.comp_def]

end LPFPol.SkR

#print axioms LPFPol.SkR.toldFrom_append
#print axioms LPFPol.SkR.toldFrom_add
#print axioms LPFPol.SkR.skel_guarded
#print axioms LPFPol.SkR.skel_andThen
#print axioms LPFPol.SkR.skel_retype
#print axioms LPFPol.SkR.skel_quiet
#print axioms LPFPol.SkR.bare_skel
#print axioms LPFPol.SkR.noRounds_skel
#print axioms LPFPol.SkR.claimNames
#print axioms LPFPol.SkR.afterNames
#print axioms LPFPol.SkR.all_bare
#print axioms LPFPol.SkR.flat_link
#print axioms LPFPol.SkR.skel_bared
#print axioms LPFPol.SkR.flat_chain
