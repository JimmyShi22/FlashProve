-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Ledger.lean: THE LEDGER of the proof file's description: where each step of
`ProofFile.onlineDescription` (Johnson/Desc/ProofFile/OnlineDescription.lean, Pure.lean) returns or finds nothing,
`onlineDescription` returns, and at which value. Every step is a NAMED PREMISE, in the step's own terms, so
that whoever shows one part has its statement to the letter.

  `baseOf_of_parts`: the places (`spotsOf`), the first chain's shape (`shapeOf`), the segments'
    records without a request (`blankBy`); all five fields of what is returned are said.
  `pureZ_of_parts`: `baseOf`; no fault (`faultsAt`); nothing lacking (`lackingAt`); the blocks at
    the places (`PureParts.base`); the first chain (`chainBy`); the two later seats.
  `descPure_of_parts`: the same behind the public part's return, at `pureSeat o Z`.
  `descPure_of_open`: the converse of `IM.seat_open` (Johnson/IMR/SeatOpen.lean): an opening gives
    the return.
  `shared_at`, `second_at`, `plans_at`, `depth_at`: what the returned description's two later
    chains, declared rounds and depth are: by definition. (The first chain's: `ProofFile.first_of`,
    Johnson/Desc/ProofFile/Law/LinkAtLaw.lean.)

Limits. A JOINING: each proof unfolds one definition and rewrites by the premises. IT PAYS NO
PREMISE. No soundness is claimed.
-/
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open ProofFile
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (S kindsBeforeBatching)

/-- **Where its three steps return (q₁, q₂, q₃: premises), `baseOf` returns**, and all five fields
of its value are said. -/
theorem baseOf_of_parts {Z : Pub} {T : PureSeat} {ps : List Spot} {sh : List (String × Place)}
    {G : Ground} (q₁ : spotsOf Z.cuts = some ps) (q₂ : shapeOf Z = .ok sh)
    (q₃ : blankBy T.links Z = some G) :
    ∃ Bs, baseOf Z T = .ok Bs ∧ Bs.spots = ps ∧ Bs.shape = sh ∧ Bs.G₀ = G ∧
      (Bs.all = T.lots.map fun L => (L, L.blocks G)) ∧
      Bs.batchAt = (subsOf Z).zipIdx.map fun x =>
        (x.2, ⟨1, some x.2, (kindsBeforeBatching x.1 (x.2 == 0)).length + 1, KindName.K9⟩) := by
  unfold baseOf
  rw [q₁, q₂, q₃]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Where each of its seven steps returns or finds nothing (the named premises), `onlineDescriptionFromPublicPart`
returns.** -/
theorem pureZ_of_parts {Z : Pub} {T : PureSeat} {Bs : PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (r₁ : baseOf Z T = .ok Bs) (r₂ : faultsAt T Bs = [])
    (r₃ : lackingAt T (partsAt T Bs) = []) (r₄ : (partsAt T Bs).base = .ok base)
    (r₅ : chainBy Z base (partsAt T Bs).frames (partsAt T Bs).road = .ok c)
    (r₆ : T.shared = some A) (r₇ : T.second = some B) :
    onlineDescriptionFromPublicPart Z T = .ok (fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c) := by
  unfold onlineDescriptionFromPublicPart
  rw [r₁]
  simp only [Except.bind, r₂, r₃, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
  unfold onlineDescriptionAfterTests
  rw [r₄]
  simp only [Except.bind, r₅, r₆, r₇]

/-- **Where the public part returns and each of `onlineDescriptionFromPublicPart`'s seven steps returns or finds nothing (the
named premises), `onlineDescription` returns.** -/
theorem descPure_of_parts {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} {Bs : PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (p₁ : pubPlain o pol lay KL = .ok Z)
    (r₁ : baseOf Z (pureSeat o Z) = .ok Bs) (r₂ : faultsAt (pureSeat o Z) Bs = [])
    (r₃ : lackingAt (pureSeat o Z) (partsAt (pureSeat o Z) Bs) = [])
    (r₄ : (partsAt (pureSeat o Z) Bs).base = .ok base)
    (r₅ : chainBy Z base (partsAt (pureSeat o Z) Bs).frames (partsAt (pureSeat o Z) Bs).road =
      .ok c)
    (r₆ : onlineSharedChain Z = some A) (r₇ : onlineLastChain Z = some B) :
    onlineDescription o pol lay KL =
      .ok (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c) := by
  have h : pureRoad.pub o pol lay KL = .ok Z := p₁
  unfold onlineDescription onlineDescriptionFromBlockTables
  rw [h]
  exact pureZ_of_parts (T := pureSeat o Z) r₁ r₂ r₃ r₄ r₅ r₆ r₇

/-- **An opening gives the return**: the converse of `IM.seat_open`. -/
theorem descPure_of_open {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) : onlineDescription o pol lay KL = .ok F := by
  rw [O.desc]
  exact descPure_of_parts O.pub O.made O.sound O.whole O.places O.chain O.shared O.second

section
variable (o : SecondHashFunctionArgument) (Z : Pub) (A : SharedSeat) (B : SecondSeat) (c : Chain S Cl)

theorem shared_at :
    (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c).shared = A.chain.retype := rfl

theorem second_at :
    (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c).second = B.chain.retype := rfl

theorem plans_at :
    (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c).plans = Z.D := rfl

theorem depth_at :
    (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c).tableDepth = Z.depth := rfl

end

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.baseOf_of_parts
#print axioms Johnson.AtFull.Desc.pureZ_of_parts
#print axioms Johnson.AtFull.Desc.descPure_of_parts
#print axioms Johnson.AtFull.Desc.descPure_of_open
#print axioms Johnson.AtFull.Desc.shared_at
#print axioms Johnson.AtFull.Desc.second_at
#print axioms Johnson.AtFull.Desc.plans_at
#print axioms Johnson.AtFull.Desc.depth_at
