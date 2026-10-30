-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/DescDeclAt.lean: the joint with the laws on the sub-protocols'
declared rounds: `ProofFile.onlineDescription` returns at the full size, and the first third of what it declares is
the written one. It is `desc_at_full` (Full/DescAt.lean) once more, with the sub-protocols at the
places and the chain kept in sight, so that `first_decl_lists` (Full/RoundsLists.lean) can be laid
on them. One definition, two theorems: calls.
  `desc_decl_at_full`  ⊢ there is a chain c with: `onlineDescription o pol lay KL` returns the description F
                       over c; `c.blocksInOrder.map skel = flatW`; `F.roundsDeclaredByBlocks.1 = declProofFull.1`
The premises. `desc_at_full`'s, to the letter; and the second rows: wl: `RowL G L` at each lot L: at
each sub-protocol b of the lot and the written spot p at b's place: b has no round, or b's rounds
are the table `listAt` (Johnson/AtFull/Rounds/ListAt.lean) at p's name. `rowL_of_name`: a row that
is stated at the written name of b's place (`nameW`, Full/Names.lean) gives it. k9: the like of what
K9's lot's batching makes at a written spot's place, under that spot's name, at every gatherer. n13
n14: the two lots of `p4Pure Z` supply no batching.
Limits. A JOINING: IT PAYS NO PREMISE. That the premises can be met together is not shown here. The
first chain alone: of the shared and the second chain's declared rounds nothing is said. The full
size alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.DescAt
import Johnson.Desc.ProofFile.Law.Skel.Full.RoundsLists
import Johnson.Desc.ProofFile.Law.Skel.Full.PureLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open Johnson.AtFull.ProofRows (declProofFull)

/-- **A lot's second row**: each sub-protocol of the lot, under the name of the written spot at its
place, has no round or the table's list at that name. -/
def RowL (G : Ground) (L : Lot) : Prop :=
  ∀ b ∈ L.blocks G, ∀ p ∈ spotsW, p.place = b.place →
    Lst Johnson.AtFull.Rounds.listAt p.name b.rounds

/-- From the row at the written name of the sub-protocol's place. -/
theorem rowL_of_name {G : Ground} {L : Lot}
    (w : ∀ b ∈ L.blocks G, Lst Johnson.AtFull.Rounds.listAt (nameW b.place) b.rounds) :
    RowL G L := by
  intro b hb p hp e
  have n : nameW p.place = p.name := eq_of_beq (List.all_eq_true.1 names_full p hp)
  rw [← n, e]
  exact w b hb

theorem desc_decl_at_full {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} {G : Ground}
    {A : SharedSeat} {B : SecondSeat} {L13 L14 : Lot}
    (p₁ : pubPlain o pol lay KL = .ok Z)
    (q₁ : spotsOf Z.cuts = some spotsW) (q₂ : shapeOf Z = .ok shapeW)
    (q₃ : blankBy (pureSeat o Z).links Z = some G) (h₄ : subsOf Z = subsW)
    (hp : p4Pure Z = [L13, L14])
    (r0 : RowAt G (framesLot Z) lot0) (r1 : RowAt G (k1Pure Z) lot1)
    (r2 : RowAt G (k2Pure Z) lot2) (r3 : RowAt G (K3Lot.lot Z) lot3)
    (r4 : RowAt G (k4Lot Z) lot4) (r5 : RowAt G (H2K5.lotN Z) lot5)
    (r6 : RowAt G (P1K8.lot Z) lot6) (r7 : RowAt G (k9Ninth Z) lot7)
    (r8 : RowAt G (K11.lot Z) lot8)
    (r9 : RowAt G (VerifiableInference.Desc.K12.lot Z) lot9)
    (r10 : RowAt G (VerifiableInference.Desc.K13.lot Z) lot10)
    (r11 : RowAt G (VerifiableInference.Desc.K13.lot4 Z) lot11)
    (r12 : RowAt G (VerifiableInference.Desc.K13.lotEnd Z) lot12)
    (r13 : RowAt G L13 lot13) (r14 : RowAt G L14 lot14)
    (s7 : Steady G (k9Ninth Z)) (s13 : Steady G L13) (s14 : Steady G L14)
    (hA : ((onlineSharedChain Z).map fun A => (A.lot, A.standIns)) = sharedW)
    (hB : ((onlineLastChain Z).map fun A => (A.lot, A.standIns)) = secondW)
    (rA : onlineSharedChain Z = some A) (rB : onlineLastChain Z = some B)
    (wl : ∀ L ∈ onlineFirstChainBlockTables Z, RowL G L)
    (k9 : ∀ p ∈ spotsW, ∀ mk, (k9Ninth Z).batch G p.place = some mk →
      ∀ g, Lst Johnson.AtFull.Rounds.listAt p.name (mk g).rounds)
    (n13 : ∀ a, L13.batch G a = none) (n14 : ∀ a, L14.batch G a = none) :
    ∃ c, onlineDescription o pol lay KL =
        .ok (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c) ∧
      c.blocksInOrder.map skel = flatW ∧
      (fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c).roundsDeclaredByBlocks.1 = declProofFull.1 := by
  obtain ⟨Bs, r₁, e₁, e₂, e₃, e₄, e₅⟩ :=
    Johnson.AtFull.Desc.baseOf_of_parts (T := pureSeat o Z) q₁ q₂ q₃
  subst e₃
  have h₃ : Bs.batchAt = batchAtW := by
    rw [e₅, h₄]
    exact batchAt_tie.symm
  obtain ⟨r₂, r₃, base, r₄, -, c, r₅, hc⟩ :=
    back_at_pure o Z Bs e₁ e₂ h₃ h₄ e₄ hp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
      s7 s13 s14 hA hB
  have k9' : ∀ p ∈ Bs.spots, ∀ mk, (k9Ninth Z).batch Bs.G₀ p.place = some mk →
      ∀ g, Lst Johnson.AtFull.Rounds.listAt p.name (mk g).rounds := by
    rw [e₁]
    exact k9
  have wL : ∀ L ∈ (pureSeat o Z).lots, ∀ b ∈ L.blocks Bs.G₀, ∀ p ∈ Bs.spots,
      p.place = b.place → Lst Johnson.AtFull.Rounds.listAt p.name b.rounds := by
    intro L hL b hb p hp e
    rw [e₁] at hp
    exact wl L hL b hb p hp e
  refine ⟨c, Johnson.AtFull.Desc.descPure_of_parts p₁ r₁ r₂ r₃ r₄ r₅ rA rB, hc, ?_⟩
  show c.blocksInOrder.flatMap (·.rounds) = declProofFull.1
  exact first_decl_lists Z (pureSeat o Z) Bs (onlineFirstChainBlockTables Z) e₁ e₂ h₄ e₄ rfl
    (rows_fifteen hp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) wL
    (wK_pure hp k9' n13 n14) r₄ r₅ hc

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.rowL_of_name
#print axioms ProofFile.Sk.Full.desc_decl_at_full
