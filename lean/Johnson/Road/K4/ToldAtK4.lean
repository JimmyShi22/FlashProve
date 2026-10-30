-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ToldAtK4.lean: THE TABLE's TEST k4ToldFit SAYS YES AT THE PROOF FILE's
DESCRIPTION's OWN TELLING, in the goals' scope, where the first chain's blocks are in order. One
definition, two theorems.
Why. K4's row's lines at the table take `k4ToldFit links ps told = true` as a premise ("at every
place of K4's the block tells no tree"): it read the letter told and was closed nowhere. At told
:= the description's own telling it is a fact on the description.
  `k4OnlyB`: A TEST WITH CODE on the two written lists: every place of K4's in `flatPlacesOf
  linksFull true` stands at a number 28 g + 4 with g < 12. `k4OnlyB_full`: it says yes: by the
  kernel. IT IS THE CONVERSE OF `k4HereB_full` (Johnson/Road/K4/K04Tied.lean: at each of the
  twelve numbers stands K4's place): `isK4At` reads neither a place's kind nor its chain, so on an
  arbitrary list it could catch another kind's place; at the written list the two tests together
  say: a number is caught just when it is one of the twelve.
  `k04_toldFit`: **the test's yes**: at such a number the first chain's flat list holds the lot's
  block (`IM.k4_of`, `IM.hear_at_flat`), which declares K4's rounds (`declares_alone`); it is
  shaped (`blocksOk`); so it tells nothing (`k4_tells_nothing`,
  Johnson/Road/K4/TellsNothing.lean).
Limits. IN THE GOALS' SCOPE, AT THE SECOND HASH FUNCTION `OnBytes.secondHashFunction`, at an opening of the
proof file's description. `blocksOk c.blocksInOrder = true` IS ASKED: it comes of the description's test on
the plan (`planOk`), which the verifier's yes gives; "onlineDescription returns" alone does not give it. It
is the one debt here beside the scope and the opening: a Bool on public data, to be booked as a
theorem in scope or as a test that the verifier's entry asks. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.K04Tied
import Johnson.Road.K4.TellsNothing
import Johnson.Desc.First.K4PlanFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Block FileDescription blocksOk)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isK4At k4ToldFit)
open VerifiableInference.Desc.Sound

/-- **A test on the two written lists**: every place of K4's stands at a number 28 g + 4, g < 12. -/
def k4OnlyB : Bool :=
  (List.range (flatPlacesOf linksFull true).length).all fun k =>
    match (flatPlacesOf linksFull true)[k]? with
    | some pl => !isK4At linksFull pl || (decide (k % 28 = 4) && decide (k / 28 < 12))
    | none => true

/-- It says yes: by the kernel. -/
theorem k4OnlyB_full : k4OnlyB = true := by decide +kernel

/-- **The test's yes at the description's own telling.** -/
theorem k04_toldFit {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hok : blocksOk c.blocksInOrder = true) :
    k4ToldFit linksFull (flatPlacesOf linksFull true)
      (c.blocksInOrder.map fun b => b.oracles.flatMap id) = true := by
  unfold k4ToldFit
  refine List.all_eq_true.2 fun k hk => ?_
  have hB := List.all_eq_true.1 k4OnlyB_full k hk
  cases hp : (flatPlacesOf linksFull true)[k]? with
  | none => rfl
  | some pl =>
    simp only [hp] at hB
    show (!isK4At linksFull pl ||
      ((c.blocksInOrder.map fun b => b.oracles.flatMap id)[k]?.any fun os => os.isEmpty)) = true
    cases hK : isK4At linksFull pl with
    | false => rfl
    | true =>
      simp only [hK, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hB
      obtain ⟨h4, h12⟩ := hB
      obtain ⟨Lk, b, x, e1, e2, _, e4, _⟩ := IM.k4_of hS hR O (k / 28) h12
      have hi : IM.flatIx c (2 * (k / 28)) 2 = k := by
        rw [IM.flatIx_scope hS hR O (by omega) 2]
        omega
      have hf : c.blocksInOrder[k]? = some b := by
        rw [← hi]
        exact IM.hear_at_flat e1 e2
      have hsh : b.shaped = true := by
        unfold blocksOk at hok
        have t := List.all_eq_true.1 hok b (List.mem_of_getElem? hf)
        rw [Bool.and_eq_true] at t
        exact t.2
      have ht := k4_tells_nothing hsh (declares_alone e4)
      rw [List.getElem?_map, hf]
      show (!true || Option.any (fun os => os.isEmpty) (some (b.oracles.flatMap id))) = true
      rw [ht]
      rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4OnlyB_full
#print axioms OnBytes.Road.K4.k04_toldFit
