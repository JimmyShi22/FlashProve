-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameQuiet.lean: TWO SMALL THINGS.
(1) THE FRONT AND Link.blocksInOrder's OWN THREE TELL NO ORACLE MESSAGE: b.oracles = [] at c.blocksInOrder[0] · [14 l
+ 1] · [14 l + ‹hear› + 3] · [14 l + ‹hear› + 7]: so «told[k]? = some []» at told := c.blocksInOrder.map
(·.oracles) is a line at each of these 76 places.
(2) AT EVERY LINK OF THE ROW OF LINKS A FRAME's BLOCK OF THE ROLE «lay l» AND ONE OF «clear l» IS IN
THE PARTS' FRAMES: AT EVERY o, NO PREMISE ON SCOPE.

  front_oracles     c.blocksInOrder[0]? = some b → b.oracles = []. At every o.
  laid_tells · behind_tells · cleared_tells   (Block.lean's text; general in the link) Link.blocksInOrder's three are quiet blocks: no oracle message.
  frame_oracles     in scope, at each l < 25: the three blocks by Johnson/IMR/FrameSeat.lean's
                    frame_of's numbers, each with oracles = [].
  roles_at          (subsOf Z)[l]? = some sub → (∃ x ∈ frames, x.1 = .lay l) ∧ ∃ x ∈ frames, x.1 = .clear l. (chain_hear hands a spot of the plan in link l; places_spots makes it an entry of the parts' places; roles_there spends lackingAt = [].)

SEARCHED FOR laid_tells | behind_tells | cleared_tells, AND WHERE (in a version that may not be the one that ships): every line that holds «oracles = []» in the lean/ folder of a stored build of this project, in Johnson/Desc, in a pack of further files and in two successive versions of ProofFile's laws: one, on another block (Close/Law/TailMeans.lean:170, tailHeadBlock); a control («rounds = []») hit 44 times. ProofFile's flat_names (Law/FrameRoles.lean) has Link.blocksInOrder's three by name and place, not what they tell.
What is not claimed. Nothing on decisions. No soundness.
-/
import Johnson.IMR.FrontSeat
import Johnson.IMR.SameSpot

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

theorem laid_tells {σ C : Type} (Lk : Link σ C) : ∃ b, Lk.blocksInOrder[0]? = some b ∧ b.oracles = [] :=
  ⟨_, rfl, rfl⟩

theorem cleared_tells {σ C : Type} (Lk : Link σ C) :
    ∃ b, Lk.blocksInOrder[Lk.blocksInOrder.length - 1]? = some b ∧ b.oracles = [] := by
  refine ⟨roundlessBlock (Lk.name ++ ": cleared") Lk.chain (some Lk.number)
    (Lk.hear.length + Lk.close.length + 3) Lk.clear, ?_, rfl⟩
  unfold Link.blocksInOrder
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.getElem?_concat_length]

theorem behind_tells {σ C : Type} (Lk : Link σ C) :
    ∃ b, Lk.blocksInOrder[Lk.hear.length + 2]? = some b ∧ b.oracles = [] := by
  obtain ⟨b, hb, -, -⟩ := behind_in_flat Lk
  have hq : Lk.blocksInOrder[Lk.hear.length + 2]? = some (roundlessBlock (Lk.name ++ ": behind the batching")
               Lk.chain (some Lk.number) (Lk.hear.length + 2) Lk.runBehind) := by
    unfold Link.blocksInOrder
    refine getElem?_append_some (getElem?_append_some ?_ _) _
    have e : Lk.hear.length + 2 = (({ roundlessBlock (Lk.name ++ ": laid") Lk.chain (some Lk.number) 0
        Lk.lay with
        planOk := VerifiableInference.Desc.orderOk Lk.hear Lk.order &&
          VerifiableInference.Desc.orderAfterOk Lk.hear Lk.orderAfter && Lk.close.all Block.hasNoClaimsAndNothingAfter &&
          (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)).hasNoClaimsAndNothingAfter } :
        Block σ C) :: Lk.hear).length + 1 := by
      rw [List.length_cons]
    rw [e, getElem?_append_add]
    rfl
  exact ⟨_, hq, rfl⟩

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The front tells no oracle message. -/
theorem front_oracles (O : Open o pol lay KL F Z Bs base c A B) {b : Block S Cl}
    (h : c.blocksInOrder[0]? = some b) : b.oracles = [] := by
  have e : c.blocksInOrder[0]? = some { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } := rfl
  obtain rfl := Option.some.inj (e.symm.trans h)
  show c.first.oracles = []
  rw [first_is O]
  rfl

/-- **At every link of the row of links both roles are borne**: at every o; no premise on scope. -/
theorem roles_at (O : Open o pol lay KL F Z Bs base c A B) {l : ℕ} {sub : ModelPart}
    (hl : (ProofFile.subsOf Z)[l]? = some sub) :
    (∃ x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames, x.1 = ProofFile.FrameRole.lay l) ∧
      ∃ x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames, x.1 = ProofFile.FrameRole.clear l := by
  obtain ⟨k, hk⟩ : ∃ k, (kindsBeforeBatching sub (l == 0))[0]? = some k := by
    cases sub <;> cases (l == 0) <;> exact ⟨_, rfl⟩
  have hk9 : k ≠ KindName.K9 := by
    rintro rfl
    revert hk
    cases sub <;> cases (l == 0) <;> decide
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨-, -, -, -, sp, hsp, -, -, -, -, es, -, -⟩ :=
    chain_hear hall (makers_K9 Z Bs.G₀) O.places O.chain l sub hl 0 k hk hk9
  obtain ⟨y, hy⟩ : ∃ y, (sp, y) ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places := by
    have h1 : sp ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places.map (·.1) := by
      rw [places_spots]
      exact hsp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h1
    exact ⟨x.2, hx⟩
  exact roles_there O.whole hy (l := l) (by rw [es])

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Link.blocksInOrder's own three, by their numbers in the chain's flat list, tell no oracle message**: in scope. -/
theorem frame_oracles (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (bL bB bC : Block S Cl), c.links[l]? = some Lk ∧
      Lk.hear.length = (if l = 24 then 9 else 7) ∧
      c.blocksInOrder[14 * l + 1]? = some bL ∧ bL.oracles = [] ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 3]? = some bB ∧ bB.oracles = [] ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 7]? = some bC ∧ bC.oracles = [] := by
  intro l hl
  obtain ⟨-, fs, -, hall⟩ := frame_of hS hR O
  obtain ⟨Lk, f, -, -, -, e1, hn, -⟩ := hall l hl
  obtain ⟨bL, hbL, oL⟩ := laid_tells Lk
  obtain ⟨bB, hbB, oB⟩ := behind_tells Lk
  obtain ⟨bC, hbC, oC⟩ := cleared_tells Lk
  have hix := flatIx_scope hS hR O (l := l) (by omega) 0
  unfold flatIx at hix
  obtain ⟨-, hlp⟩ := link_flat_places O.chain
  obtain ⟨Lk', e1', hpl⟩ := hlp l (subAt l) (subs_scope hS hR O l hl)
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨Lk'', -, e1'', -, -, -, -, -, -, -, hn8, -⟩ :=
    link_fields O.places O.chain l (subAt l) (subs_scope hS hR O l hl)
  obtain rfl : Lk = Lk'' := Option.some.inj (e1.symm.trans e1'')
  have hflen : Lk.blocksInOrder.length = Lk.hear.length + 7 := by
    rw [← List.length_map (f := (·.place)), hpl, linkPlaces_len, hn8]
  refine ⟨Lk, bL, bB, bC, e1, hn, ?_, oL, ?_, oB, ?_, oC⟩
  · have h := link_at_flat e1 hbL
    rw [show (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length + 0) = 14 * l + 1 by
      omega] at h
    exact h
  · have h := link_at_flat e1 hbB
    rw [show (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length +
      (Lk.hear.length + 2)) = 14 * l + Lk.hear.length + 3 by omega] at h
    exact h
  · have h := link_at_flat e1 hbC
    rw [show (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length +
      (Lk.blocksInOrder.length - 1)) = 14 * l + Lk.hear.length + 7 by omega] at h
    exact h

end

end IM

#print axioms IM.front_oracles
#print axioms IM.roles_at
#print axioms IM.frame_oracles
