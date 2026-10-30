-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/PureChain.lean. chain_hear's two arms follow chainBy's text (it joins by the link's number and the name): the block is alone ∧ no member of the parts' frames bears the role «behind l ‹the spot's name›», or a member x with x.1 = .behind l sp.name (the link itself) is joined. linkAt_hear | firstChain_link are proved over linkAt_shape | firstChain_shape (Johnson/Desc/First/Link/Law/Shape.lean).
Where the rest of this head and the Lean text differ, the Lean text holds.
 A LAW ABOUT ProofFile.chainBy AND THE DRIVER, NO PART OF THEM: BY INDEX: the block
number i in front of the batching in link number l of onlineDescription's first chain is a lot's block at the blank letters, in the form of
Johnson/IMR/SeatForm.lean.
OBJECT. ProofFile.onlineDescriptionFromPublicPart · baseOf · partsAt · faultsAt · chainBy · chainC · fill (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean · Frames1.lean · FillCore.lean) and the driver's
firstChain · firstChainWithoutReplyGuard · linkAt · blockAt · kindsBeforeBatching · addresses (Johnson/Desc/First/Driver/Chain.lean).
USER. The seats (Johnson/IMR/K6Seat.lean …).
LETTERS. Z: the public part · T: the seat · B: baseOf's record (B.G₀: the blank letters; B.spots: the places) · base: the places' blocks · c: the chain.


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  (CALLED, NOT TYPED: OnBytes.Road.L5.mapM_mem (Johnson/Road/Lane5AttCalls.lean): a member of a list
    that mapM has made.)
  linkAt_hear       where the driver's linkAt returns a link: its block number i in front of the batching is what the socket gives at the
                    address (1, l, i + 1, the i-th of kindsBeforeBatching), with that address written into it.
  firstChain_link   where the driver's firstChain returns a chain: its link number l is linkAt's BEHIND THE DRIVER's GUARD.
  places_from_lots  a place's block is the batching's maker's face, or (where no maker is given) a lot's block at the blank letters, at that
                    place, marked, under the place's name.
  MakersK9 · face_kind   THE ONE PREMISE ON THE SEAT: every batching's maker of a lot makes blocks that bear the kind K9: then the face that stands in
                    the list of places for K9's place is found at no other kind's address. WHO PAYS IT: LotKinds.lean: makers_K9, at onlineDescription's seat.
  chain_hear        THE JOIN: for every link l of the row of links and every i whose kind is not K9: the chain's link l is there, and its
                    block i in front of the batching is Laid (Johnson/IMR/SeatForm.lean) of a block
                      b' ∈ L.blocks B.G₀ of a lot L of the seat, under the
                    name of a spot sp ∈ B.spots that stands at the driver's address; b'.place is that address. THE SECOND ARM NAMES WHAT IS JOINED:
                    a member x of the parts' frames whose role is «behind l ‹sp.name›».
  hear_mem_flat | hear_split   a block in front of a link's batching stands in the chain's flat list; the list cut at it.

What is not claimed. WHICH lot (Johnson/IMR/LotKinds.lean). Whether something is joined behind
(Johnson/IMR/LaidFirst.lean). Nothing on the batching, the closing,
the frames, the chain's back. No soundness.
-/
import Johnson.IMR.PureJoin
import Johnson.IMR.SeatForm
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.First.Link.Law.Shape
import OnBytes.Desc.First.K4.RowsLaws
import Johnson.Road.Lane5AttCalls

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt blockAt kindsBeforeBatching addresses hearsReply)
open OnBytes.L5.LinksOrder (ok_bind)
open ProofFile (Cl)

/-! ## 2 The driver -/

section
variable {σ C : Type}

theorem addresses_at (link : Option ℕ) (ks : List KindName) (i : ℕ) (k : KindName)
    (h : ks[i]? = some k) :
    (addresses link ks)[i]? = some { chain := 1, link := link, piece := i + 1, kind := k } := by
  unfold addresses
  rw [List.getElem?_map, List.getElem?_zipIdx, h]
  simp

/-- **A link's block in front of the batching is the socket's at the driver's address.** -/
theorem linkAt_hear {H : Blocks σ C} {l : ℕ} {sub : ModelPart} {Lk : Link σ C}
    (h : linkAt H l sub = some Lk) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) :
    ∃ b, H.block { chain := 1, link := some l, piece := i + 1, kind := k } = some b ∧
      Lk.hear[i]? =
        some { b with place := { chain := 1, link := some l, piece := i + 1, kind := k } } := by
  have hh := congrArg (·[i]?) (VerifiableInference.Desc.Shape.linkAt_shape h).2.1
  simp only [List.getElem?_map, addresses_at (some l) _ i k hk, Option.map_some] at hh
  obtain ⟨c, e, hc⟩ := Option.map_eq_some_iff.1 hh
  unfold blockAt at hc
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hc.symm
  exact ⟨b, hb, e⟩

/-- **The chain's link number l is linkAt's, behind the driver's guard.** -/
theorem firstChain_link {H : Blocks σ C} {links : List ModelPart} {several : Bool} {c : Chain σ C}
    (h : firstChain H links several = some c) (l : ℕ) (sub : ModelPart) (hl : links[l]? = some sub) :
    ∃ Lk, linkAt H l sub = some Lk ∧ c.links[l]? = some (Lk.guarded H.same hearsReply) := by
  obtain ⟨-, c0, ⟨-, -, hls, -, -⟩, rfl⟩ := VerifiableInference.Desc.Shape.firstChain_shape h
  have hz : links.zipIdx[l]? = some (sub, l) := by
    rw [List.getElem?_zipIdx, hl]
    simp
  have h1 := congrArg (·[l]?) hls
  simp only [List.getElem?_map, hz, Option.map_some] at h1
  obtain ⟨Lk, h2, h3⟩ := Option.map_eq_some_iff.1 h1
  refine ⟨Lk, h3.symm, ?_⟩
  show (c0.links.map (Link.guarded H.same hearsReply))[l]? = _
  rw [List.getElem?_map, h2]
  rfl

end

/-! ## 3 onlineDescription's first chain -/

/-- **A place's block: the maker's face, or a lot's block at the blank letters.** -/
theorem places_from_lots {T : ProofFile.PureSeat} {B : ProofFile.PureBase}
    (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) (sp : ProofFile.Spot) (b : Block S Cl)
    (hb : (sp, Except.ok b) ∈ (ProofFile.partsAt T B).places) :
    sp ∈ B.spots ∧
      ((∃ mk, (ProofFile.partsAt T B).road.batch sp.place = some mk ∧ b = mk fun s => .ok ([], s)) ∨
        ((ProofFile.partsAt T B).road.batch sp.place = none ∧ ∃ L ∈ T.lots, ∃ b' ∈ L.blocks B.G₀,
          b'.place = sp.place ∧ b = marked b' sp.name)) := by
  simp only [ProofFile.partsAt] at hb ⊢
  obtain ⟨q, hq, e⟩ := List.mem_map.1 hb
  obtain ⟨rfl, e2⟩ := Prod.mk.inj e
  refine ⟨hq, ?_⟩
  split at e2
  · rename_i f hface
    obtain rfl := Except.ok.inj e2
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    exact Or.inl ⟨mk, hmk, rfl⟩
  · rename_i x hface hsits
    obtain rfl := Except.ok.inj e2
    refine Or.inr ⟨Option.map_eq_none_iff.1 hface, ?_⟩
    have hm := List.mem_of_find?_eq_some hsits
    obtain ⟨y, hy, ey⟩ := List.mem_filterMap.1 hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ey
    rw [hall] at hy
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hy
    exact ⟨L, hL, c, List.mem_of_find?_eq_some hc, by simpa using List.find?_some hc, rfl⟩
  · split at e2 <;> cases e2

/-- Every batching's maker of the seat's lots makes blocks that bear the kind K9 (LotKinds.lean pays it at onlineDescription's seat). -/
def MakersK9 (T : ProofFile.PureSeat) (G₀ : ProofFile.Ground) : Prop :=
  ∀ L ∈ T.lots, ∀ (a : Place) (mk : ProofFile.Gatherer → Block S Cl), L.batch G₀ a = some mk →
    ∀ g, (mk g).place.kind = KindName.K9

theorem face_kind {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (hM : MakersK9 T B.G₀) {a : Place}
    {mk : ProofFile.Gatherer → Block S Cl} (h : (ProofFile.partsAt T B).road.batch a = some mk)
    (g : ProofFile.Gatherer) : (mk g).place.kind = KindName.K9 := by
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk0, hmk, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some hmk
  exact hM L (List.mem_filter.1 hL).1 a mk0 e g

/-- **THE JOIN, BY INDEX: a block in front of the batching is a lot's block at the blank letters**: alone, or with a block of a frame's
place joined behind it WHOSE ROLE IS «behind THIS LINK, ‹this spot's name›» (chainBy joins by the link's number and the name); ALONE ONLY WHERE NO MEMBER OF THE PARTS' FRAMES BEARS THAT ROLE. -/
theorem chain_hear {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hM : MakersK9 T B.G₀) (hb : (ProofFile.partsAt T B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) (l : ℕ)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) (hk9 : k ≠ KindName.K9) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      ∃ sp ∈ B.spots, ∃ L ∈ T.lots, ∃ b' ∈ L.blocks B.G₀,
        sp.place = { chain := 1, link := some l, piece := i + 1, kind := k } ∧
        b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } ∧
        ((LaidAlone T.same b b' sp.name { chain := 1, link := some l, piece := i + 1, kind := k } ∧
            ∀ x ∈ (ProofFile.partsAt T B).frames, x.1 ≠ ProofFile.FrameRole.behind l sp.name) ∨
          ∃ x ∈ (ProofFile.partsAt T B).frames, x.1 = ProofFile.FrameRole.behind l sp.name ∧
            b = seatedWith T.same b' x.2 sp.name
              { chain := 1, link := some l, piece := i + 1, kind := k }) := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · rename_i z hz
    dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        obtain ⟨Lk, hLk, eLk⟩ := firstChain_link h1 l sub hl
        obtain ⟨b, hbk, eb⟩ := linkAt_hear hLk i k hk
        refine ⟨_, _, eLk, (by
          show (Lk.hear.map _)[i]? = _
          rw [List.getElem?_map, eb]
          rfl), ?_⟩
        have hbk' := hbk
        have hm := List.mem_of_find?_eq_some hbk'
        have hpl : b.place = { chain := 1, link := some l, piece := i + 1, kind := k } := by
          simpa using List.find?_some hbk'
        obtain ⟨b0, hb0, ej⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hm)
        obtain ⟨x, hx, ex⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hb b0 hb0
        obtain ⟨sp, y⟩ := x
        obtain rfl : y = .ok b0 := ex
        obtain ⟨hsp, harm⟩ := places_from_lots hall sp b0 hx
        have eplace : b0.place = { chain := 1, link := some l, piece := i + 1, kind := k } := by
          split at ej <;> subst ej <;> exact hpl
        rcases harm with ⟨mk, hmk, rfl⟩ | ⟨-, L, hL, b', hb', ep, rfl⟩
        · exfalso
          have hk' := face_kind hM hmk (fun s => .ok ([], s))
          rw [eplace] at hk'
          exact hk9 hk'
        · refine ⟨sp, hsp, L, hL, b', hb', ep.symm.trans eplace, eplace, ?_⟩
          split at ej
          · rename_i w hw
            subst ej
            refine Or.inr ⟨w, List.mem_of_find?_eq_some hw, ?_⟩
            have hpred := List.find?_some hw
            obtain ⟨r, q⟩ := w
            cases r with
            | behind l' m =>
              have em : sp.name = m ∧ b'.place.link = some l' := by simpa using hpred
              obtain ⟨rfl, el⟩ := em
              have eplace' : b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } := eplace
              rw [eplace'] at el
              obtain rfl : l = l' := Option.some.inj el
              exact ⟨rfl, rfl⟩
            | front => cases hpred
            | lay _ => cases hpred
            | clear _ => cases hpred
            | common => cases hpred
            | stray => cases hpred
          · rename_i hnone
            subst ej
            refine Or.inl ⟨rfl, fun x hx hr => ?_⟩
            have hn := List.find?_eq_none.1 hnone x hx
            rw [hr] at hn
            have eplace' : b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } := eplace
            apply hn
            show ((marked b' sp.name).name == sp.name && (marked b' sp.name).place.link == some l) = true
            have e1 : (marked b' sp.name).name = sp.name := rfl
            have e2 : (marked b' sp.name).place.link = some l := by
              show b'.place.link = some l
              rw [eplace']
            rw [e1, e2]
            simp

/-- A block in front of a link's batching stands in the chain's flat list. -/
theorem hear_mem_flat {σ C : Type} {c : Chain σ C} {l i : ℕ} {Lk : Link σ C} {b : Block σ C}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) : b ∈ c.blocksInOrder := by
  have hb : b ∈ Lk.blocksInOrder := by
    unfold Link.blocksInOrder
    simp [List.mem_of_getElem? h2]
  unfold Chain.blocksInOrder
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨Lk, List.mem_of_getElem? h1, hb⟩)))

/-- The same as a cut of the flat list (for a law that wants «blocksInOrder = pre ++ b :: post»). pre and post are what stands in front and behind: nothing more is said of them. -/
theorem hear_split {σ C : Type} {c : Chain σ C} {l i : ℕ} {Lk : Link σ C} {b : Block σ C}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) : ∃ pre post, c.blocksInOrder = pre ++ b :: post :=
  List.append_of_mem (hear_mem_flat h1 h2)

end IM

#print axioms IM.linkAt_hear
#print axioms IM.firstChain_link
#print axioms IM.places_from_lots
#print axioms IM.chain_hear
#print axioms IM.hear_mem_flat
