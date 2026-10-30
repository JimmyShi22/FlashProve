-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FitsAll.lean: the hypothesis `FitsAt` (Shape.lean) proved at
every sub-protocol of a chain from one executable test. `FitsAt T b` says that the rounds as played
and the columns as filled pass the two tests of `Block.step` on form (`Block.Fits`). The test is
`halved` (Law/Run.lean): at each sub-protocol either a prover's side is at its place, or none of its
rounds declares an item other than a root. No definition.

How it relates to `fitsAt_half` (ShapeRow.lean). That lemma has two more hypotheses: the prover's
side has as many rounds as the sub-protocol, and the sub-protocol declares one list of oracle
messages for each round. Both are tests of `chainSteps` (Frame.lean), which returns an error where
either fails, and `Thread.Moved` (Pays.lean) says that `chainSteps` returned. So neither is needed.
Where no prover's side is at the place, `Step.tell` shows no item, and the test on the rounds passes
if no round declares an item other than a root: the second arm of `halved`.

  1  `fits_of_halved`   one sub-protocol: `Block.Fits` from what `Thread.Moved` says
  2  `halved_of_half`, `halved_of_quiet`   two cases in which the test passes at one sub-protocol
  3  `fitsAt_member`, `fitsAt_of_halved`   `FitsAt` at one sub-protocol, and at all of a `Thread`
  4  `fitsAt_of_sits`   at a description's three chains, from `Sits` (File.lean) and `halvedAll`

Limits.
  * Conditional lemmas on this folder's own definitions.
  * Nothing here shows that `halved` passes at a description and a prover. At a sub-protocol that
    has rounds and no prover's side it is a fact about the rounds that the sub-protocol declares.
  * `FitsAt` speaks of form only: it says nothing about whether `decide` returns.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

/-! ## 1 One sub-protocol -/

section
variable {S Cl V W X : Type}

/-- The two tests of `Block.step` on form pass at the rounds as played and the columns as filled,
where `chainSteps` returned at the one sub-protocol and `halved` passes there, and the challenges
fit the rounds. The proof is that of `fits_played` (Law/Cut.lean), with `itemsFall_of_halved` in
place of its count of moves. -/
theorem fits_of_halved {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {b : Block S Cl} {hs : List (Placed V W X)} {l : List (Step W X)}
    {ds : List Fmt.Drawn} {m : Mid W X} {y : List Played × Mid W X} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {cols : List OpenedColumn} (hl : chainSteps B rows look v [b] hs = .ok l)
    (h4 : halved [b] hs = true) (hy : play l ds [] m = .ok y)
    (hd : drawsFit b.rounds ds = true)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    b.Fits ft (roundsOf y.1) cols := by
  have hdecl : l.map (·.decl) = b.rounds := by
    rw [steps_decl hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hk := chain_kept hdecl hy (drawsFit_bare _ _ hd) (itemsFall_of_halved hl h4) hc
  obtain ⟨k1, k2⟩ := (kept_iff _ _ _ _).1 hk
  have hdr : (roundsOf y.1).map (·.drawn) = ds :=
    yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  rw [hdr] at k2
  have hlen : ((groupsOf ft b.rounds ds).flatMap id).length = cols.length := by
    rw [← k2, List.length_map]
  have hwant : b.want ft (roundsOf y.1) = (groupsOf ft b.rounds ds).flatMap id := by
    unfold Block.want
    rw [hdr]
  refine ⟨k1, ?_⟩
  rw [hwant, hlen, List.take_length, k2]
  exact beq_self_eq_true _

/-! ## 2 Two cases in which the test passes -/

/-- The test passes at a sub-protocol at whose place a prover's side is found. -/
theorem halved_of_half {b : Block S Cl} {hs : List (Placed V W X)} {g : Placed V W X}
    (hf : (hs.find? fun g => g.place == b.place) = some g) : halved [b] hs = true := by
  unfold halved
  rw [List.all_cons, List.all_nil, Bool.and_true, any_eq_find, hf]
  rfl

/-- The test passes at a sub-protocol without a round. -/
theorem halved_of_quiet {b : Block S Cl} (hs : List (Placed V W X)) (h : b.rounds = []) :
    halved [b] hs = true := by
  unfold halved
  rw [List.all_cons, List.all_nil, Bool.and_true, h, List.all_nil, Bool.or_true]

end

/-! ## 3 At a `Thread` -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- `FitsAt` at the sub-protocol number `b`, where the test passes at it. -/
theorem fitsAt_member {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    (h4 : halved [blk] T.hs = true) : FitsAt T b := by
  intro blk' hblk' k m E ds y cols hd hMv
  rw [hblk] at hblk'
  cases hblk'
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv
  exact fits_of_halved hl h4 hy hd hc

/-- **`FitsAt` at every sub-protocol of a `Thread`**, where the test passes at its list. -/
theorem fitsAt_of_halved (h4 : halved T.bs T.hs = true) (b : Nat) : FitsAt T b := by
  intro blk hblk
  have h1 : halved [blk] T.hs = true := by
    unfold halved at h4 ⊢
    rw [List.all_cons, List.all_nil, Bool.and_true]
    exact List.all_eq_true.1 h4 blk (List.mem_of_getElem? hblk)
  exact fitsAt_member T hblk h1 blk hblk

end

/-! ## 4 At the three chains of a description -/

/-- `FitsAt` at every sub-protocol of the three chains, where the three invariants' parameters are
those of the description and the prover (`Sits`) and the test passes at all three lists. -/
theorem fitsAt_of_sits {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hS : Sits F H T₁ T₂ T₃) (h4 : halvedAll F H = true) :
    (∀ b, FitsAt T₁ b) ∧ (∀ b, FitsAt T₂ b) ∧ ∀ b, FitsAt T₃ b := by
  obtain ⟨⟨-, -, -, b1, h1⟩, ⟨-, -, -, b2, h2⟩, ⟨-, -, -, b3, h3⟩, -⟩ := hS
  simp only [halvedAll, Bool.and_eq_true] at h4
  obtain ⟨⟨a1, a2⟩, a3⟩ := h4
  exact ⟨fitsAt_of_halved T₁ (by rw [b1, h1]; exact a1),
    fitsAt_of_halved T₂ (by rw [b2, h2]; exact a2),
    fitsAt_of_halved T₃ (by rw [b3, h3]; exact a3)⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.fits_of_halved
#print axioms ProofFile.Honest.halved_of_half
#print axioms ProofFile.Honest.halved_of_quiet
#print axioms ProofFile.Honest.fitsAt_member
#print axioms ProofFile.Honest.fitsAt_of_halved
#print axioms ProofFile.Honest.fitsAt_of_sits
