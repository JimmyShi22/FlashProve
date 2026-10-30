-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/DrawsOfDecl.lean: A WRITTEN LIST OF CHALLENGES THAT PASSES THE
FRAME's TEST Draws.due (Honest/Frame.lean), AT EVERY IOP AS WRITTEN IN LEAN (below: the description
F) THAT HAS DATA: a function of the declared rounds, with its law. General in the description: no
kind is named. Two definitions with code; statements with their proofs.

FIRST. IT IS A WRITTEN LIST THAT MEETS A TEST OF FORM: NOT CHALLENGES THAT ANYBODY DRAWS. The
positions of a round repeat where the round draws more than 2 ^ logN of them. Nothing is said on
whether the frame's ready or its player runC returns at this list.

Why. Sentences of the frame speak "at every due list of challenges". That there is one is shown
here.

  drawnOnes       at one declared round: every element is 1; the positions are 0, 1, 2, … modulo 2 ^
                  logN; every matrix entry is 0; no sealed digest (the test allows one at a sealing
                  round and asks none)
  Draws.ofDecl    drawnOnes at every declared round of the three chains, with the empty challenge in
                  the place of the first chain's last round (its sealing round)
  drawnOnes_fits  **drawnOnes passes drawFit at a round whose entry's name has a kind**: as many
                  elements, positions and matrix entries as the entry counts; each position is a
                  remainder modulo 2 ^ logN; where the format marks an element "never 0" it is 1
  drawsFit_ones   so drawsFit along a list of declared rounds whose entries' names have kinds
  Draws.ofDecl_due   **(Draws.ofDecl F).due F = true where FileDescription.data returns**: that the names
                  have kinds, and that the first chain's last round takes the empty challenge, is
                  kinds_of_data (Honest/Law/DataKinds.lean); the first chain's list is cut by
                  drawsFit_append (Honest/Law/Cut.lean)

Kin. due_at_two (Honest/Law/DueData.lean) says that EVERY typed verifier's message is due, under the
same premise and one more: that no declared round draws more elements "never 0" than elements. At
the proof file's description the frame has that premise paid: due_laid, and with it due_exists_laid:
some list is due (Honest/Law/DueHead.lean): that list is taken by choice. Here the second premise is
not asked, neither the goals' scope nor the full size is, and the list is WRITTEN: it can be
evaluated. K1.readsSample (Honest/K1/LotData.lean) lays, over a front stretch of a run's data, the
same round but for the positions, which are all 0 there. The library's oneAt and roundsFit_ones
(Johnson/Desc/First/Att/K05Member.lean) have a view of ones at one kind's rounds, which draw no
position.

Whose. Typed by the writers of kind K14 (the linear claim's sub-protocols), who have the first use;
it lies in the frame's folder because it is general over the frame.

What is not claimed. No run is named. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.DataKinds
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription drawsMarkedNonzeroHaveNonzeroWords fieldPrimeWord)
open OnBytes.Maker (RDT WholeD)

/-- The written challenge at one declared round: every element 1, the positions counted up modulo 2
^ logN, every matrix entry 0. -/
def drawnOnes (d : Fmt.DeclaredRound) : Fmt.Drawn :=
  ⟨List.replicate d.entry.drawE (1, 0, 0),
    (List.range d.entry.poss).map (· % 2 ^ d.entry.logN), List.replicate d.entry.trits 0, none⟩

/-- The written list of challenges of a description: drawnOnes at every declared round, with the
empty challenge for the first chain's last round. -/
def Draws.ofDecl {Xi : Type} (F : FileDescription Xi) : Draws :=
  ⟨F.roundsDeclaredByBlocks.1.dropLast.map drawnOnes ++ [⟨[], [], [], none⟩], F.roundsDeclaredByBlocks.2.1.map drawnOnes,
    F.roundsDeclaredByBlocks.2.2.map drawnOnes⟩

/-- **The written challenge fits a round whose entry's name has a kind.** -/
theorem drawnOnes_fits (d : Fmt.DeclaredRound) (k : Fmt.Kind) (hk : Fmt.kindOf d.entry.name = some k) :
    drawFit d (drawnOnes d) = true := by
  unfold drawFit drawnOnes
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp
  · simp
  · simp
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact decide_eq_true (Nat.mod_lt _ (Nat.two_pow_pos _))
  · rw [List.all_eq_true]
    intro t ht
    rw [List.eq_of_mem_replicate ht]
    rfl
  · unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk]
    show (List.all _ _) = true
    rw [List.all_eq_true]
    intro x hx
    have h2 : x.2 = (1, 0, 0) := List.eq_of_mem_replicate (List.of_mem_zip hx).2
    rw [h2, Bool.or_eq_true]
    exact Or.inr (by decide)
  · rw [List.all_eq_true]
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    decide
  · rfl

/-- Along a list of declared rounds whose entries' names have kinds. -/
theorem drawsFit_ones : ∀ (ds : List RDT) (zs : List Fmt.DeclaredRound), List.Forall₂ KindFits ds zs →
    drawsFit zs (zs.map drawnOnes) = true
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, z :: zs, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.1 h
    show (drawFit z (drawnOnes z) && drawsFit zs (zs.map drawnOnes)) = true
    rw [drawnOnes_fits z d.kind h1.2, drawsFit_ones ds zs h2]
    rfl

/-- **The written list is due**, at every description that has data. -/
theorem Draws.ofDecl_due {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) : (Draws.ofDecl F).due F = true := by
  obtain ⟨k1, k2, k3, d, hd, hd'⟩ := kinds_of_data h
  obtain ⟨A, hA⟩ := List.getLast?_eq_some_iff.1 hd
  have hdl : F.roundsDeclaredByBlocks.1.dropLast = A := by rw [hA, List.dropLast_concat]
  have f1 : drawsFit F.roundsDeclaredByBlocks.1 (F.roundsDeclaredByBlocks.1.dropLast.map drawnOnes ++ [⟨[], [], [], none⟩]) = true := by
    rw [hdl] at k1 ⊢
    rw [hA, drawsFit_append, List.take_left' (by rw [List.length_map]),
      List.drop_left' (by rw [List.length_map]), drawsFit_ones _ _ k1]
    show (true && (drawFit d ⟨[], [], [], none⟩ && true)) = true
    rw [hd']
    rfl
  unfold Draws.due Draws.ofDecl
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨f1, drawsFit_ones _ _ k2⟩, drawsFit_ones _ _ k3⟩, ?_⟩
  rw [List.getLast?_concat]
  decide

end ProofFile.Honest

#print axioms ProofFile.Honest.drawnOnes_fits
#print axioms ProofFile.Honest.drawsFit_ones
#print axioms ProofFile.Honest.Draws.ofDecl_due
