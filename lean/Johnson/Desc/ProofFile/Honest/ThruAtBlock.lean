-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruAtBlock.lean: the crossing at one block. A kind states what it
owes at the prover that the maker returns at a filling, with the index a letter. This file carries
that to the prover that the maker returns at the filling read through, and to its committer's
prover, at one block of each chain.

  lots_through, halves_through, shared_through, second_through   by the text of OnlineProverParts.through: a lot
                       that the filling read through lays is the filling's lot read through. No
                       kind owes this: it is rfl, for every lot
  first_made, shared_made, second_made   the three lists of the prover returned
  first_find_made, shared_find_made, second_find_made   what a search by place finds there
  playsOn_first_made, playsOn_shared_made, playsOn_second_made, saysYes_first_made,
  saysYes_shared_made, saysYes_second_made   PlaysOn and SaysYes at one block: the invariant read
                       through Mid.narrow
  proverAt_lists       the committer's prover keeps the three lists

By what. made_thru (Honest/ThruAtPure.lean); PlaysOn.thru, SaysYes.thru (Honest/ThruThreads.lean).

Limits.
  * NOT IN FRONT OF A LAW OVER COINS: PlaysOn and SaysYes are premises and ends here.
  * A Thread does not cross: a sentence at a thread crosses after it has been turned into PlaysOn or
    SaysYes at its block, or into ThreadsC.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruCommitted

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {S Cl Sd Xc W₀ W₀' Rc Rc' Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (P : OnlineProverParts W₀ Rc Tr X₀ X)

/-- The filling read through lays the filling's lots read through. -/
theorem lots_through : (OnlineProverParts.through g rd d P).lots =
    P.lots.map (HLot.thru (Local.thru g rd) (Local.thru g rd)) := rfl

/-- So does each lot: its sides are the sides read through. -/
theorem halves_through (L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) (Z : Pub)
    (G : Ground) :
    (L.thru (Local.thru g rd) (Local.thru g rd)).halves Z G =
      (L.halves Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) := rfl

/-- The shared chain's. -/
theorem shared_through (Z : Pub) (G : Ground) : (OnlineProverParts.through g rd d P).shared Z G =
    (P.shared Z G).map (Placed.thru id (Common.thru g rd)) := rfl

/-- The second chain's. -/
theorem second_through (Z : Pub) (G : Ground) : (OnlineProverParts.through g rd d P).second Z G =
    (P.second Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) := rfl

end

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : Pub} {Gr : Ground}
  {F : FileDescription Inst} {B : ProverCoinCounts} {H₀ : Prover W₀ Rc Inst OnBytes.TableKey Tr X₀ X}
  {H' : Prover W₀' Rc' Inst OnBytes.TableKey Tr X₀ X} {rds₀ : W₀ → Rc → Tr → Readers}
  {rds : W₀' → Rc' → Tr → Readers} {rws₀ rws : RowDataOf Inst}
  (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
  (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
  (hd : P.inRange (g d) = true)
include base made hd

/-- The first chain's sides of the prover returned. -/
theorem first_made :
    H'.first = H₀.first.map (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
  obtain rfl := made_thru g rd d base made hd
  rfl

/-- The shared chain's. -/
theorem shared_made : H'.shared = H₀.shared.map (Placed.thru id (Common.thru g rd)) := by
  obtain rfl := made_thru g rd d base made hd
  rfl

/-- The second chain's. -/
theorem second_made :
    H'.second = H₀.second.map (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
  obtain rfl := made_thru g rd d base made hd
  rfl

/-- A search by place in the first chain, at the prover returned. -/
theorem first_find_made (p : Place) :
    H'.first.find? (fun x => x.place == p) =
      (H₀.first.find? fun x => x.place == p).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
  rw [first_made g rd d base made hd, List.find?_map]
  rfl

/-- In the shared chain. -/
theorem shared_find_made (p : Place) :
    H'.shared.find? (fun x => x.place == p) =
      (H₀.shared.find? fun x => x.place == p).map (Placed.thru id (Common.thru g rd)) := by
  rw [shared_made g rd d base made hd, List.find?_map]
  rfl

/-- In the second chain. -/
theorem second_find_made (p : Place) :
    H'.second.find? (fun x => x.place == p) =
      (H₀.second.find? fun x => x.place == p).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
  rw [second_made g rd d base made hd, List.find?_map]
  rfl

variable {Bk : ProverCoinCounts} {b : Block S Cl} {chain ft : Nat}

/-- **PlaysOn at a block of the first chain's sides, at the prover returned.** -/
theorem playsOn_first_made {A C : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop}
    (h : PlaysOn .own Bk chain ft H₀.first b A C) :
    PlaysOn .own Bk chain ft H'.first b (fun k s m E => A k s (Mid.narrow (Local.thru g rd) m) E)
      (fun k s m E => C k s (Mid.narrow (Local.thru g rd) m) E) := by
  rw [first_made g rd d base made hd]
  exact PlaysOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd) (fun _ => rfl) h

/-- At the shared chain's. -/
theorem playsOn_shared_made
    {A C : Coins Bk → S → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Env → Prop}
    (h : PlaysOn .shared Bk chain ft H₀.shared b A C) :
    PlaysOn .shared Bk chain ft H'.shared b
      (fun k s m E => A k s (Mid.narrow (Common.thru g rd) m) E)
      (fun k s m E => C k s (Mid.narrow (Common.thru g rd) m) E) := by
  rw [shared_made g rd d base made hd]
  exact PlaysOn.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd) (fun _ => rfl) h

/-- At the second chain's. -/
theorem playsOn_second_made {A C : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop}
    (h : PlaysOn .own Bk chain ft H₀.second b A C) :
    PlaysOn .own Bk chain ft H'.second b (fun k s m E => A k s (Mid.narrow (Local.thru g rd) m) E)
      (fun k s m E => C k s (Mid.narrow (Local.thru g rd) m) E) := by
  rw [second_made g rd d base made hd]
  exact PlaysOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd) (fun _ => rfl) h

/-- **SaysYes at a block of the first chain's sides, at the prover returned.** -/
theorem saysYes_first_made {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop}
    (h : SaysYes .own Bk chain ft H₀.first b fall A) :
    SaysYes .own Bk chain ft H'.first b fall
      (fun k s m E => A k s (Mid.narrow (Local.thru g rd) m) E) := by
  rw [first_made g rd d base made hd]
  exact SaysYes.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd) (fun _ => rfl) h

/-- At the shared chain's. -/
theorem saysYes_shared_made {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Env → Prop}
    (h : SaysYes .shared Bk chain ft H₀.shared b fall A) :
    SaysYes .shared Bk chain ft H'.shared b fall
      (fun k s m E => A k s (Mid.narrow (Common.thru g rd) m) E) := by
  rw [shared_made g rd d base made hd]
  exact SaysYes.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd) (fun _ => rfl) h

/-- At the second chain's. -/
theorem saysYes_second_made {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid (Local W₀ Rc Inst Tr) X → Env → Prop}
    (h : SaysYes .own Bk chain ft H₀.second b fall A) :
    SaysYes .own Bk chain ft H'.second b fall
      (fun k s m E => A k s (Mid.narrow (Local.thru g rd) m) E) := by
  rw [second_made g rd d base made hd]
  exact SaysYes.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd) (fun _ => rfl) h

end

/-- The committer's prover keeps the three lists: so the laws of this file speak of it too. -/
theorem proverAt_lists (Cm : Committer W₀' Rc' Sd Xc Inst OnBytes.TableKey) (item₀ : Nat)
    (H' : Prover W₀' Rc' Inst OnBytes.TableKey Tr X₀ X) :
    (Cm.proverAt item₀ H').first = H'.first ∧ (Cm.proverAt item₀ H').shared = H'.shared ∧
      (Cm.proverAt item₀ H').second = H'.second := ⟨rfl, rfl, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.lots_through
#print axioms ProofFile.Honest.halves_through
#print axioms ProofFile.Honest.shared_through
#print axioms ProofFile.Honest.second_through
#print axioms ProofFile.Honest.first_made
#print axioms ProofFile.Honest.shared_made
#print axioms ProofFile.Honest.second_made
#print axioms ProofFile.Honest.first_find_made
#print axioms ProofFile.Honest.shared_find_made
#print axioms ProofFile.Honest.second_find_made
#print axioms ProofFile.Honest.playsOn_first_made
#print axioms ProofFile.Honest.playsOn_shared_made
#print axioms ProofFile.Honest.playsOn_second_made
#print axioms ProofFile.Honest.saysYes_first_made
#print axioms ProofFile.Honest.saysYes_shared_made
#print axioms ProofFile.Honest.saysYes_second_made
#print axioms ProofFile.Honest.proverAt_lists
