-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlatScope.lean. link_flat_places' clause «front = []» is proved over firstChain_shape (Johnson/Desc/First/Link/Law/Shape.lean).
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND THE DRIVER: WHICH NUMBER a block in front of a link's batching has in
onlineDescription's first chain's flat list, in the goals' scope: 14 l + i + 2.
OBJECT. IM.flatIx c l i (Johnson/IMR/FlatIx.lean) at onlineDescription's chain c. USER. The count «341 at the full size» for K6's place (14 · 24 + 3 + 2) and whoever wants «pre.length = k».
LETTERS. As in Johnson/IMR/K6Seat.lean.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean)).

  link_flat_places  (general in the seat) a link of chainBy's chain: the places of its flat list are
                    the driver's linkPlaces l sub (by guarded_link_places).
                    its first clause: chainBy's chain has nothing in its field front.
  link_at_flat      (general in the chain) number j of link l's flat list is number (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length + j) of the chain's.
  take_flat_len     where each of the first l links has a flat list of k blocks, these l lists in a row have k * l.
  flatIx_scope      in scope, l ≤ 24: flatIx c l i = 14 * l + i + 2.
  k6_at_341         c.blocksInOrder[341]? = some b for K6's seated block b (c.links[24]? = some Lk · Lk.hear[3]? = some b); so c.blocksInOrder = c.blocksInOrder.take 341 ++ b :: c.blocksInOrder.drop 342.

What is not claimed. That b stands in the flat list once. No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs
import Johnson.IMR.FlatIx

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart firstChain firstChainWithoutReplyGuard kindsBeforeBatching hearsReply linkPlaces)
open ProofFile (Cl)

/-- **The places of a link's flat list are the driver's**, and the chain's field front is empty. -/
theorem link_flat_places {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl}
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) :
    c.front = [] ∧ ∀ (l : ℕ) (sub : ModelPart), (ProofFile.subsOf Z)[l]? = some sub →
      ∃ Lk, c.links[l]? = some Lk ∧ Lk.blocksInOrder.map (·.place) = linkPlaces l sub := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        refine ⟨?_, fun l sub hl => ?_⟩
        · obtain ⟨-, c0, ⟨-, hfr, -, -, -⟩, rfl⟩ :=
            VerifiableInference.Desc.Shape.firstChain_shape h1
          show c0.front.map _ = []
          rw [hfr]
          rfl
        · obtain ⟨Lk, hLk, eLk⟩ := firstChain_link h1 l sub hl
          exact ⟨_, eLk, VerifiableInference.Desc.First.guarded_link_places _ _ _ l sub Lk hLk⟩

/-- **Any block of a link's flat list, in the chain's**: number j of link l's flat list is number (1 + front) + (the links in front, flat) + j of the chain's. General in the chain. (Johnson/IMR/FlatIx.lean's hear_at_flat
is this at j = 1 + i.) -/
theorem link_at_flat {σ C : Type} {c : Chain σ C} {l j : ℕ} {Lk : Link σ C} {b : Block σ C}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.blocksInOrder[j]? = some b) :
    c.blocksInOrder[(1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length + j)]? = some b := by
  obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 h1
  have hs : c.links = c.links.take l ++ Lk :: c.links.drop (l + 1) := by
    rw [← e, ← List.drop_eq_getElem_cons hl, List.take_append_drop]
  have hM : (c.links.flatMap Link.blocksInOrder)[((c.links.take l).flatMap Link.blocksInOrder).length + j]? =
      some b := by
    generalize c.links.take l = P at hs ⊢
    generalize c.links.drop (l + 1) = Q at hs
    rw [hs, List.flatMap_append, List.flatMap_cons, getElem?_append_add]
    exact getElem?_append_some h2 _
  unfold Chain.blocksInOrder
  refine getElem?_append_some (getElem?_append_some ?_ _) _
  have hA : (1 + c.front.length) =
      (({ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } : Block σ C) ::
        c.front.map fun b : Block σ C => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }).length := by
    rw [List.length_cons, List.length_map, Nat.add_comm]
  rw [hA, getElem?_append_add]
  exact hM

theorem take_flat_len {σ C : Type} (ls : List (Link σ C)) (k : ℕ) : ∀ l : ℕ,
    (∀ j < l, ∃ Lk, ls[j]? = some Lk ∧ Lk.blocksInOrder.length = k) →
      ((ls.take l).flatMap Link.blocksInOrder).length = k * l
  | 0, _ => by simp
  | l + 1, h => by
    obtain ⟨Lk, e, hk⟩ := h l (Nat.lt_succ_self l)
    rw [List.take_add_one, e, List.flatMap_append, List.length_append,
      take_flat_len ls k l fun j hj => h j (Nat.lt_succ_of_lt hj)]
    simp [hk, Nat.mul_succ]

theorem linkPlaces_len (l : ℕ) (sub : ModelPart) :
    (linkPlaces l sub).length = (kindsBeforeBatching sub (l == 0)).length + 7 := by
  unfold linkPlaces
  simp [VerifiableInference.Desc.First.length_addresses,
    VerifiableInference.Desc.First.closeAddresses, VerifiableInference.Desc.First.closeKinds]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **In scope: the block's number in the flat list is 14 l + i + 2.** -/
theorem flatIx_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l ≤ 24) (i : ℕ) :
    flatIx c l i = 14 * l + i + 2 := by
  obtain ⟨hfr, hlk⟩ := link_flat_places O.chain
  have hlen : ((c.links.take l).flatMap Link.blocksInOrder).length = 14 * l := by
    refine take_flat_len c.links 14 l fun j hj => ?_
    by_cases he : j % 2 = 0
    · have h := subs_at hS hR O.pub O.blank (g := j / 2) (by omega)
      rw [show 2 * (j / 2) = j by omega] at h
      obtain ⟨Lk, e, hp⟩ := hlk j .layers h
      refine ⟨Lk, e, ?_⟩
      rw [← List.length_map (f := (·.place)), hp, linkPlaces_len]
      cases (j == 0) <;> rfl
    · have h := subs_att hS hR O.pub O.blank (g := j / 2) (by omega)
      rw [show 2 * (j / 2) + 1 = j by omega] at h
      obtain ⟨Lk, e, hp⟩ := hlk j .attention h
      refine ⟨Lk, e, ?_⟩
      rw [← List.length_map (f := (·.place)), hp, linkPlaces_len]
      cases (j == 0) <;> rfl
  unfold flatIx
  rw [hfr, hlen]
  simp
  omega

/-- **K6's seated block is number 341 of the flat list** (from 0). -/
theorem k6_at_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl} {b : Block S Cl}
    (h1 : c.links[24]? = some Lk) (h2 : Lk.hear[3]? = some b) :
    c.blocksInOrder[341]? = some b ∧ c.blocksInOrder = c.blocksInOrder.take 341 ++ b :: c.blocksInOrder.drop 342 := by
  have e : flatIx c 24 3 = 341 := flatIx_scope hS hR O (by decide) 3
  have h3 := hear_at_flat h1 h2
  have h4 := hear_cut h1 h2
  rw [e] at h3 h4
  exact ⟨h3, h4⟩

end

end IM

#print axioms IM.link_at_flat
#print axioms IM.link_flat_places
#print axioms IM.flatIx_scope
#print axioms IM.k6_at_341
