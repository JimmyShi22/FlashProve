-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RootsCut.lean: THE
COUNT OF ROOTS AT
EVERY CUT OF THE FIRST CHAIN's FLAT LIST IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, at an opening
of onlineDescription: from the fold's return alone. UNDER ONE FIELD A LOT: FIFTEEN LOTS: NONE OF THEM IS PAID
HERE: THEY ARE PAID IN Johnson/IMR/CarryLots.lean AND Johnson/IMR/RootsSeat.lean
(roots_at_cut_paid).

For a statement on 128 bits a step, which holds at its record the fold's return alone (no promise,
no yes of the whole file).
  LotCarry Pr R₀ L G: what Johnson/IMR/CarrySeat.lean's LotsCarry asks, of one lot. lots_of.
    LotRoots L G: at
      RootsStep (Johnson/Desc/K12/Law/RootsFold.lean) and "the count is as it was".
  open_frontP: O : Open o pol lay KL F Z Bs base c A B · ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotCarry Pr R₀ L Bs.G₀
      ⇒ c.blocksInOrder = frontOf c ++ backOf c ∧ ∀ b ∈ frontOf c, Pr b. General in the property.
  roots_at_cut: **O · ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotRoots L Bs.G₀ · k ≤ (frontOf c).length · every block
      of c.blocksInOrder.take k passes its test on the plan · foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r
      ⇒ r.1.roots = s.roots + rootsOf (declOf (c.blocksInOrder.take k)).** AT EVERY o, ANY FIRST RECORD s,
      ANY ft. No "there is" stands in it.
WHO CAN PAY. The tests on the plan: F.planOk (a yes of F.run holds it). The fifteen fields: each
kind's files' sentence on its maker, carried through the lot's own text.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription o's value; not verify(). User: that
statement. Letters: none.
OVER WHICH FILES: as CarrySeat.lean, Johnson/Goal/Meaning/CarryRoots.lean; SeatOpen.lean.
Compiled with the whole library.
Limits. By itself empty: see Johnson/IMR/RootsSeat.lean. Nothing behind the last link (there:
Johnson/IMR/RootsEnd.lean).
Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.CarrySeat
import Johnson.IMR.SeatOpen
import Johnson.Goal.Meaning.CarryRoots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)
open Meaning.K2 (frontOf backOf flat_eq all_of_made chainBy_noFront)
open H2K.First (RootsStep declOf)
open Johnson.G.OfPlan (rootsOf)
open ProofFile (Lot Ground)

/-- **What is asked of one lot.** -/
structure LotCarry (Pr : Block S ProofFile.Cl → Prop) (R₀ : S → S → Prop) (L : Lot) (G : Ground) :
    Prop where
  blocks : ∀ b ∈ L.blocks G, b.place.link ≠ none → WholeP Pr R₀ b
  framesIn : ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → b.place.link ≠ none →
    QuietW R₀ b
  framesOut : ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → b.place.link = none →
    Pr b
  batch : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R₀ f → WholeP Pr R₀ (mk f)

theorem lots_of {Pr : Block S ProofFile.Cl → Prop} {R₀ : S → S → Prop} {lots : List Lot} {G : Ground}
    (h : ∀ L ∈ lots, LotCarry Pr R₀ L G) : LotsCarry Pr R₀ lots G :=
  ⟨fun L hL => (h L hL).blocks, fun L hL => (h L hL).framesIn, fun L hL => (h L hL).framesOut,
    fun L hL => (h L hL).batch⟩

/-- The sentence on the roots, of one lot. -/
abbrev LotRoots (L : Lot) (G : Ground) : Prop :=
  LotCarry (RootsStep fun s : S => s.roots) (Same fun s : S => s.roots) L G

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At an opening of onlineDescription: every block in front of the blocks behind the last link has the
property that the seat's lots' blocks have.** -/
theorem open_frontP {Pr : Block S ProofFile.Cl → Prop} {R₀ : S → S → Prop} (C : Carried Pr R₀)
    (O : IM.Open o pol lay KL F Z Bs base c A B)
    (K : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotCarry Pr R₀ L Bs.G₀) :
    c.blocksInOrder = frontOf c ++ backOf c ∧ ∀ b ∈ frontOf c, Pr b := by
  have hall := all_of_made (T := ProofFile.pureSeat o Z) (IM.base_made O.made).2.2.2
  have K' : LotsCarry Pr R₀ (ProofFile.pureSeat o Z).lots Bs.G₀ := lots_of K
  exact ⟨flat_eq (chainBy_noFront O.chain), chainBy_frontP C O.chain
    (partsAt_baseP C K' hall O.places) (partsAt_framesP C K' hall)
    (fun a mk e f hf => (partsAt_roadP C K' e f hf).1)⟩

/-- **THE COUNT OF ROOTS AT EVERY CUT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK**: from the fold's
return alone, at any first record and any number of the first tree. -/
theorem roots_at_cut (O : IM.Open o pol lay KL F Z Bs base c A B)
    (K : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotRoots L Bs.G₀) (k : Nat) (hk : k ≤ (frontOf c).length)
    (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (ft : Nat) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) :
    r.1.roots = s.roots + rootsOf (declOf (c.blocksInOrder.take k)) := by
  obtain ⟨e, hf⟩ := open_frontP (carried_roots fun s : S => s.roots) O K
  have e2 : c.blocksInOrder.take k = (frontOf c).take k := by
    rw [e, List.take_append_of_le_length hk]
  rw [e2] at hp h ⊢
  exact roots_at_take (fun s : S => s.roots) ft (frontOf c) hf k hp s rs cols r h

end

#print axioms open_frontP
#print axioms roots_at_cut

end Meaning.Carry
