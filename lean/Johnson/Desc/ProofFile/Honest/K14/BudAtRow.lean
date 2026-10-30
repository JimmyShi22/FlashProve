-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudAtRow.lean: kind K14: THE CLAUSE OF THE FRAME's DEBT bud₂ (a
field of BudDebts, Honest/Law/OwedRule.lean) AT THE ROW OF "send o_omega", AT THE PROOF FILE's IOP
AS WRITTEN IN LEAN (below: the description), FOR A LETTER bud THAT IS spBud
(Honest/K14/FreshDefs.lean): in the rule's own term. For all public files Z that pass the library's
two tests InScope and protocolDataWellFormed, and every public part Zp of which the library's LaidAt holds at the
proof file's own data and decision at Z. Counts on public numbers. Statements with their proofs; no
definition.

  made_of_laid    where the description is laid, the library makes its eight sub-protocols of the
                  shared chain's own parameters: the description's test on the plan has passed
  no_later_at, no_later   no member of the description's shared list behind the sixth stands at
                  "send o_omega"'s place (the library's tests_places, tests_places_none,
                  last_place)
  one_tree_u      "send o_u" states ONE oracle message in its first round (an evaluation at the
                  written sizes)
  one_before_omega   so the rule's count of the trees in front of "send o_omega" is 1
  bud_at_omega_row   **at every side whose sub-protocol stands at "send o_omega"'s place and whose
                  row has one part (any), every member, every cut of the shared list at that
                  sub-protocol, every due list of challenges: spBud at the very list of positions
                  that bud₂ names**

What is assumed. InScope Z, protocolDataWellFormed (asDescriptionFiles Z), LaidAt.
What is not claimed. The field bud₂ itself: it runs over ALL rows of a filling's shared chain; this
is its clause at one row, with spBud written for the row's letter. A RUN OF ONE REQUEST: nothing on
the union of the positions that the requests of a batch read. The key file's description is not
treated. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BudAtFiles
import Johnson.Desc.ProofFile.Honest.K14.BudRow
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.K14.AtFilling
import Johnson.Desc.ProofFile.Honest.Law.OwedRule
import Johnson.Desc.K12.Law.SharedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open VerifierAndGoals (InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofData theProofRun)
open P5J (LaidAt F0T TS)
open AtPublicFiles.TreeReads (sized_at written_proof)
open Desc.K14 (St blocks chainOf)
open Desc.K14.Law (flat_retype_all two_sendings bareOf)
open Desc.K14.Honest (flatOf_carried)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Where the description is laid, the library makes its eight of the shared chain's parameters. -/
theorem made_of_laid (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : MadeAt Zp Np :=
  made_carried Zp Np (Cl' := ProofFile.Cl) fun b hb =>
    (((VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk).blocks₂ b hb).1

/-- The step for no_later, at letters. -/
theorem no_later_at {Cl : Type} (b6 b7 b8 e : Block St Unit) (ts : List (Block St Unit))
    (h6 : b6.place ≠ sendPlace 5) (h7 : b7.place ≠ sendPlace 5) (h8 : b8.place ≠ sendPlace 5)
    (ht : ∀ z ∈ ts, z.place ≠ sendPlace 5) (he : e.place ≠ sendPlace 5) :
    ∀ y ∈ b6.retype (Cl' := Cl) :: b7.retype :: b8.retype ::
      ((ts ++ [e]).map (Block.retype (Cl' := Cl))).map bareOf, y.place ≠ sendPlace 5 := by
  intro y hy
  simp only [List.mem_cons, List.mem_map, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | ⟨_, ⟨z, hz | rfl, rfl⟩, rfl⟩
  · exact h6
  · exact h7
  · exact h8
  · exact ht z hz
  · exact he

/-- No member of the shared list behind the sixth stands at "send o_omega"'s place. -/
theorem no_later (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ y ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.drop 6, y.place ≠ sendPlace 5 := by
  obtain ⟨-, -, p7, p8⟩ := places4 (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, p6⟩ := places2 (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 hb
  have ht : ∀ z ∈ tests Np, z.place ≠ sendPlace 5 := fun z hz e => by
    have hm : z.place ∈ (tests Np).map (·.place) := List.mem_map.2 ⟨z, hz, rfl⟩
    rw [e] at hm
    cases hO : Np.O with
    | none =>
      rw [H2K.JointK.tests_places_none Np hO] at hm
      simp [sendPlace] at hm
    | some nO =>
      rw [H2K.JointK.tests_places Np nO hO] at hm
      simp [sendPlace] at hm
  intro y hy
  have hb' : blocks (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8] := hb
  rw [shared_flat_at, flat_retype_all _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb'] at hy
  exact no_later_at b6 b7 b8 (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests Np)) (tests Np)
    (by rw [p6]; decide) (by rw [p7]; decide) (by rw [p8]; decide) ht
    (by rw [H2K.JointK.last_place]; decide) y hy

/-- "send o_u" states one oracle message in its first round. -/
theorem one_tree_u (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (os : List VerifiableInference.Desc.Oracle) (ho : b2.oracles = [os, []]) : os.length = 1 := by
  obtain ⟨sentU, hU, rfl, -⟩ := two_sendings (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 hb
  have e : os = Desc.K14.oraclesOf (qAt Zp Np).codes sentU [[0], []] := by
    have e1 := ((List.cons.inj ho).1).symm
    rwa [Desc.K14.Law.parK1_sent] at e1
  have hk : ((Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).all fun s =>
      (Desc.K14.oraclesOf Zp.p.chains.made.sized.proof.codes s [[0], []]).length == 1) = true := by
    rw [sized_at scope L, written_proof]
    decide +kernel
  have hU' : Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape = some sentU := hU
  rw [hU'] at hk
  rw [e]
  exact beq_iff_eq.1 hk

/-- So the rule's count of the trees in front of "send o_omega" is 1. -/
theorem one_before_omega (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (pre t : List (Block St ProofFile.Cl))
    (b : Block St ProofFile.Cl) (hx : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (hp : b.place = sendPlace 5) :
    (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take
      (pre.flatMap (·.rounds)).length).map (·.2.length)).sum = 1 := by
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := made_of_laid L
  obtain ⟨os, ho, hs⟩ := trees_before_omega
    (xs := (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    (flatOf_carried Zp.p.chains (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 (tests Np) last hb) hb
    (no_later b1 b2 b3 b4 b5 b6 b7 b8 hb) pre t b hx hp
  exact hs.trans (one_tree_u scope L b1 b2 b3 b4 b5 b6 b7 b8 hb os ho)

/-- **THE CLAUSE OF bud₂ AT THE ROW OF "send o_omega"**, with spBud for the row's letter: a run of
one request. -/
theorem bud_at_omega_row (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
      (theProofRun (asDescriptionFiles Z)) Zp Np cF) (a : Nat) {X Pb W₀ Rc Ky : Type}
    (p : Part Empty (Common W₀ Rc Ky) X) (sim : Sim Pb)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X Pb) (hrow : σ.row = [(p, sim)])
    (hp : σ.block.place = sendPlace 5) (u : Member Empty (Common W₀ Rc Ky) X Pb)
    (hu : u ∈ σ.members) (pre t : List (Block St ProofFile.Cl)) (n : Nat)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number) (ρ : Draws)
    (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    spBud ⟨qAt Zp Np, a⟩ (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1)
      (u.rounds.map (·.2.length))
      (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  have h0 : n = (pre.flatMap (·.rounds)).length := hn
  rw [h0, one_before_omega scope L pre t σ.block hx hp]
  exact spBud_at_files Z scope live Zp Np cF L a ρ hρ _

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.made_of_laid
#print axioms ProofFile.Honest.K14.no_later_at
#print axioms ProofFile.Honest.K14.no_later
#print axioms ProofFile.Honest.K14.one_tree_u
#print axioms ProofFile.Honest.K14.one_before_omega
#print axioms ProofFile.Honest.K14.bud_at_omega_row
