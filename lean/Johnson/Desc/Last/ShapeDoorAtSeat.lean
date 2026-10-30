-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorAtSeat.lean: SH₃ (the premise on `PL.shape 0` of the joint between the
shared and the last chain) AT THE SEATED DESCRIPTION'S OWN START OF THE LAST CHAIN, with both of its
letters laid as terms and the first table's item laid by the door's layer. Statements and proofs; no
definition.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`sh₃_at_seat`**: `sh₃_at_beside` (Johnson/Desc/Last/ShapeDoorBeside.lean) CALLED at P :=
    `ProofFile.InstPub`, S₁ := `First.S`, start₃ := the start of `ProofFile.seatedAt o Z Np c` as the rule of
    composition takes it, p := `ProofFile.pAt Z`, with `ProofFile.hmark_at` and `ProofFile.hstart_at`
    (Johnson/Desc/Plain/StartThreeAtPure.lean) for hmark and hstart. LEFT: hitem, hopen, ahead; and
    hg: the reader g of (public part, first record) has the record for its second half.
  `door_open_at_fill`: at `fillDoor Mg₀` the item "K13.doorFirst" is open at the last border, where
    the list of places is a ++ p :: l with p a place of kind K1 behind the links of chain 1, and no
    row of `Mg₀.more` at a place of l drops the name: by `First.pubSets_last_of_made`
    (Johnson/Desc/First/BordersKept.lean).
  **`sh₃_at_seat_filled`**: so at Mg₁ := `fillDoor Mg₀`: hitem by the make, hopen by that law. LEFT:
    hg · the list's shape (three equations on one place) · hd (nobody behind drops the name) ·
    ahead: `(ProofFile.pAt Z).S.masksAhead = true`.

Every "there is": none.
WHAT IS OWED BESIDE THE PREMISES, AND BY WHOM (others' words). The promise in front is dearer by two
texts: (1) `doorX` beside the shared table's `shape`: the shared chain's last block owes
`doorSharedB` at its yes: taken on by that chain's files, by `doorSharedB_of_parts`
(Johnson/Desc/Last/ShapeDoorParts.lean). (2) "K13.doorFirst" in the first table: the block at that
place of kind K1 owes `doorFirstB` at its yes, and the blocks behind it keep it: NOT TYPED; what it
comes down to: `doorFirstB_of_items` (Johnson/Desc/Last/ShapeDoorItems.lean).
Limits. N, Pm₀, Mg₀, N₁, links, split, T, R, g are letters still. That `onlineDescription`'s value is
`seatedAt …`: `descPure_cut` (StartThreeAtPure.lean). NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorBeside
import Johnson.Desc.Plain.StartThreeAtPure
import Johnson.Desc.First.BordersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart moreItem nDoor pubSets fillDoor doorMore)
open _root_.Desc.K14 (St)

/-- **SH₃ AT THE SEATED DESCRIPTION's OWN START, UNDER THREE PREMISES.** -/
theorem sh₃_at_seat {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (R : List Fmt.DeclaredRound) (g : ProofFile.InstPub × First.S → P₀ × First.S)
    (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place)
    (hitem : ∀ a, Mg₁.pub (moreItem nDoor) a = doorFirstB a.2)
    (hopen : moreItem nDoor ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (ahead : (ProofFile.pAt Z).S.masksAhead = true)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ (doorX (ProofFile.pAt Z) (1 + T.l₂.length))) (ocEnd g N₁ Mg₁ links ps)
      split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true :=
  sh₃_at_beside (ProofFile.pAt Z) R g
    (fun q a d => ((ProofFile.seatedAt o Z Np c).start₃ q a d).toOption) T N Pm₀ split N₁ Mg₁ links ps
    hitem hopen (ProofFile.hmark_at o Z Np c g hg) (ProofFile.hstart_at o Z Np c g hg) ahead b s hb hs

/-- **At the door's layer the item is open at the last border**, where the list of places has a
place of kind K1 behind the links and no later row of what lay there before drops the name. -/
theorem door_open_at_fill {P₀ W₁ : Type} (Mg₀ : Meaning P₀ W₁) (links : List ModelPart)
    (a : List Place) (p : Place) (l : List Place) (h1 : p.chain = 1) (h2 : p.link = none)
    (h3 : p.kind = .K1) (hd : ∀ p' ∈ l, nDoor ∉ (Mg₀.more.rows links p').drops) :
    moreItem nDoor ∈
      (pubSets (fillDoor Mg₀).more links (a ++ p :: l))[(a ++ p :: l).length]?.getD [] := by
  refine First.pubSets_last_of_made _ links a p l nDoor ?_ fun p' hp' h => ?_
  · show nDoor ∈ (Mg₀.more.rows links p).makes ++ (doorMore.rows links p).makes
    refine List.mem_append_right _ ?_
    simp [doorMore, h1, h2, h3]
  · have h' : nDoor ∈ (Mg₀.more.rows links p').drops ++ (doorMore.rows links p').drops := h
    rcases List.mem_append.1 h' with c | c
    · exact hd p' hp' c
    · unfold doorMore at c
      dsimp only at c
      split at c
      · cases c
      · split at c <;> cases c

/-- **SH₃ AT THE SEATED START AND THE DOOR's LAYER**: hitem by the make, hopen by the table's
law. -/
theorem sh₃_at_seat_filled {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (R : List Fmt.DeclaredRound) (g : ProofFile.InstPub × First.S → P₀ × First.S)
    (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₀ : Meaning P₀ W₁) (links : List ModelPart)
    (a : List Place) (p : Place) (l : List Place) (h1 : p.chain = 1) (h2 : p.link = none)
    (h3 : p.kind = .K1) (hd : ∀ p' ∈ l, nDoor ∉ (Mg₀.more.rows links p').drops)
    (ahead : (ProofFile.pAt Z).S.masksAhead = true)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ (doorX (ProofFile.pAt Z) (1 + T.l₂.length)))
      (ocEnd g N₁ (fillDoor Mg₀) links (a ++ p :: l)) split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true :=
  sh₃_at_seat o Z Np c R g hg T N Pm₀ split N₁ (fillDoor Mg₀) links (a ++ p :: l)
    (fun _ => rfl) (door_open_at_fill Mg₀ links a p l h1 h2 h3 hd) ahead b s hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.door_open_at_fill
#print axioms VerifiableInference.Desc.Last.sh₃_at_seat_filled
#print axioms VerifiableInference.Desc.Last.sh₃_at_seat
