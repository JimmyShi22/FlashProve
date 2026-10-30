-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsAll.lean: THE ROW K10_sits "AT EACH PLACE OF THE KIND", FOR THE FIRST CHAIN: IN SCOPE, EVERY BLOCK OF THE FIRST CHAIN's FLAT LIST WHOSE PLACE IS OF THE
KIND K10 IS THE SECOND CLOSING BLOCK OF ONE OF THE 25 LINKS, SEATED AS k10_sits SAYS: THERE IS NO TWENTY-SIXTH IN THAT CHAIN. Statements and proofs.
WHY. k10_sits (Sits.lean, beside this file) runs over l < 25; the list's sentence runs over the places of the kind.
  close_at_flat    (general in the link) closing block number j stands at number hear.length + 3 + j of the link's flat list.
  seated_unmarked  THE SEATED BLOCK HAS NO YES AT A MARKED RECORD: what its yes returns bears no mark (seated_yes), and K10's writing turns no mark (putRec_keeps, Law/Leaves.lean).
  chain_first      the chain that onlineDescription's yes opens into is the driver's firstChain's, at the public part's row of links (by the way in which the files of Johnson/IMR/ open chainBy).
  subs_eq          in scope that row IS the 25 sorts (subAt): its length from links_25 and link_flat_places, its members from subs_scope (IM.links_25, IM.subs_scope: Johnson/IMR/LinkSeat.lean; IM.link_flat_places: Johnson/IMR/FlatScope.lean).
  ixK10 · table_k10   BY THE KERNEL: the driver's own table of places (flatPlacesOf) at these 25 sorts has just 25 places of the kind K10, at the numbers 14 l + n + 5 (n: the link's hearing
                   blocks), whichever of the two ways the blocks behind the links go.
  k10_at_flat      K10's block of link l stands at that number of the chain's flat list (link_at_flat · flatIx_scope: IM's).
  k10_sits_each    so: b in c.blocksInOrder with b.place.kind = K10: the driver's flat_places (Johnson/Desc/First/Driver/PlacesLaw.lean) puts b's place at b's number of the table; the table puts that
                   number among the 25; there stands k10_sits' block: so b is it.
With seated_yes and k10_seated (Sits.lean): at each such b the law holds at the piece of b itself (hk7: the address's kind is K10: by rfl). The two are not joined in one term here.
LIMITS. THE SHARED AND THE LAST CHAIN (F.shared, F.second) ARE NOT TREATED: that they hold no place
of the kind K10 is shown in Johnson/LPFK10R/SitsFile.lean (no_k10_elsewhere), at an opening
(IM.Open), not here.
(By their seats' own words they lay: a front block, K14's
six, K1's two, K12's, the end; and K14's second part, the taken trees' sources, K12's own block, the
chain's end. A try at the last chain closed three of its four blocks by
evaluation and stuck at K12's own block's place.) That F.first is c stands inside Open.desc. All limits of Sits.lean. Nothing on soundness of the protocol.

-/
import Johnson.LPFK10R.Sits
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.First.Close.Law.Leaves

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain closeKinds kindsBeforeBatching flatPlacesOf flat_places)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile (Cl)
open IM

/-- A closing block of a link, in the link's flat list. General in the link. -/
theorem close_at_flat {σ C : Type} {L : Link σ C} {j : ℕ} {b : Block σ C}
    (h : L.close[j]? = some b) : L.blocksInOrder[L.hear.length + 3 + j]? = some b := by
  unfold Link.blocksInOrder
  refine getElem?_append_some ?_ _
  have hA : L.hear.length + 3 = (({ VerifiableInference.Desc.roundlessBlock (L.name ++ ": laid") L.chain
      (some L.number) 0 L.lay with
      planOk := VerifiableInference.Desc.orderOk L.hear L.order &&
        VerifiableInference.Desc.orderAfterOk L.hear L.orderAfter &&
        L.close.all Block.hasNoClaimsAndNothingAfter &&
        (L.batch (VerifiableInference.Desc.claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter } : Block σ C) ::
    L.hear ++ [L.batch (VerifiableInference.Desc.claimsInBy L.each L.hear L.order),
      VerifiableInference.Desc.roundlessBlock (L.name ++ ": behind the batching") L.chain
        (some L.number) (L.hear.length + 2) L.runBehind]).length := by
    simp
  rw [hA, getElem?_append_add]
  exact h

/-- **The seated block has no yes at a marked record**: what its yes returns bears no mark
(`seated_yes`), and K10's writing turns no mark (`putRec_keeps`). -/
theorem seated_unmarked {same : S → S → Bool} {b : Block S Cl} {Q : Par} {name : String} {a : Place}
    (h : LaidAlone same b (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype name a)
    (hk : a.kind ≠ KindName.K7) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hy : b.decide s rs gs = .ok t) : s.failed = none := by
  obtain ⟨⟨x, -, rfl⟩, h2, -⟩ := seated_yes h hk s t rs gs hy
  rw [← (VerifiableInference.Desc.First.Close.putRec_keeps s ⟨none, x.1, x.2⟩).2.2.1]
  exact h2

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}

/-- The chain is the driver's `firstChain`'s, at the public part's row of links. -/
theorem chain_first (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ (H : Blocks S Cl) (several : Bool), firstChain H (ProofFile.subsOf Z) several = some c := by
  have hc := O.chain
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
        exact ⟨_, _, h1⟩

/-- In scope the row of links is the 25 sorts. -/
theorem subs_eq (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ProofFile.subsOf Z = (List.range 25).map subAt := by
  have h25 := links_25 hS hR O
  have hs := subs_scope hS hR O
  have hlen : (ProofFile.subsOf Z).length = 25 := by
    have h1 : 24 < (ProofFile.subsOf Z).length := (List.getElem?_eq_some_iff.1 (hs 24 (by omega))).1
    by_contra hne
    have h2 : 25 < (ProofFile.subsOf Z).length := by omega
    obtain ⟨Lk, e, -⟩ := (link_flat_places O.chain).2 25 _ (List.getElem?_eq_getElem h2)
    have := (List.getElem?_eq_some_iff.1 e).1
    omega
  apply List.ext_getElem?
  intro l
  by_cases hl : l < 25
  · rw [hs l hl, List.getElem?_map, List.getElem?_range hl]
    rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- The number, in the first chain's flat list, of K10's block of link l, in scope. -/
def ixK10 (l : ℕ) : ℕ := 14 * l + (kindsBeforeBatching (subAt l) (l == 0)).length + 5

set_option maxRecDepth 100000 in
/-- **The driver's table of places at the 25 sorts has just 25 places of the kind K10**, whichever way
the blocks behind the links go: at the numbers `ixK10 l`. -/
theorem table_k10 : ∀ several : Bool,
    ((flatPlacesOf ((List.range 25).map subAt) several).zipIdx.filter
      fun x => x.1.kind == KindName.K10).map (·.2) = (List.range 25).map ixK10 := by
  decide +kernel

/-- K10's block of link l stands at that number of the flat list. -/
theorem k10_at_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Cl} {b : Block S Cl} (h1 : c.links[l]? = some Lk) (h2 : Lk.close[1]? = some b) :
    c.blocksInOrder[ixK10 l]? = some b := by
  obtain ⟨Lk', p, e1, -, -, -, -, -, -, -, -, -, -, -, hn, -⟩ :=
    k9_alone O l (subAt l) (subs_scope hS hR O l hl)
  obtain rfl : Lk = Lk' := Option.some.inj (h1.symm.trans e1)
  have h3 := link_at_flat h1 (close_at_flat h2)
  have h4 := flatIx_scope hS hR O (l := l) (by omega) (Lk.hear.length + 3)
  unfold flatIx at h4
  have e : (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length +
      (Lk.hear.length + 3 + 1)) = ixK10 l := by
    unfold ixK10
    rw [← hn]
    omega
  rw [e] at h3
  exact h3

/-- **K10_sits, AT EACH PLACE OF THE KIND IN THE FIRST CHAIN**: every block of the flat list whose place
is of the kind K10 is the second closing block of one of the 25 links, and is seated as
`k10_sits` says. -/
theorem k10_sits_each (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l < 25, ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        c.links[l]? = some Lk ∧ k9At Z l = some p ∧
        ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ Lk.close[1]? = some b ∧
        c.blocksInOrder[ixK10 l]? = some b ∧
        LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype b.name
          (cAt l (subAt l) 1 KindName.K10) := by
  intro b hb hk
  obtain ⟨H, several, hf⟩ := chain_first O
  have hp := flat_places H _ several c hf
  rw [subs_eq hS hR O] at hp
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
  -- the place at number i of the table is b's
  have hpi : (flatPlacesOf ((List.range 25).map subAt) several)[i]? = some b.place := by
    rw [← hp, List.getElem?_map, hi]
    rfl
  -- so i is one of the 25 numbers
  have hm : i ∈ ((flatPlacesOf ((List.range 25).map subAt) several).zipIdx.filter
      fun x => x.1.kind == KindName.K10).map (·.2) := by
    refine List.mem_map.2 ⟨(b.place, i), List.mem_filter.2 ⟨?_, by simpa using hk⟩, rfl⟩
    exact List.mem_zipIdx_iff_getElem?.2 hpi
  rw [table_k10 several] at hm
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
  have hl' : l < 25 := List.mem_range.1 hl
  obtain ⟨Lk, p, Q, b1, h1, h2, h3, h4, h5⟩ := k10_sits hS hR O l hl'
  have h6 := k10_at_flat hS hR O hl' h1 h4
  obtain rfl : b = b1 := Option.some.inj (hi.symm.trans h6)
  exact ⟨l, hl', Lk, p, Q, h1, h2, h3, h4, h6, h5⟩

end LPFK10

#print axioms LPFK10.close_at_flat
#print axioms LPFK10.seated_unmarked
#print axioms LPFK10.chain_first
#print axioms LPFK10.subs_eq
#print axioms LPFK10.table_k10
#print axioms LPFK10.k10_at_flat
#print axioms LPFK10.k10_sits_each
