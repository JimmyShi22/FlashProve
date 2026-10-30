-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SameSpot.lean: A LAW ABOUT ProofFile.pureSeat, NO PART OF IT: «opened» SITS: AT A LINK's FIRST
PLACE THE «opened» OF THE LINK's OWN ROW OF framesOf IS JOINED
BEHIND THE LOT's BLOCK: NO ARM IS LEFT.
flat_block_at is read off Johnson/IMR/DriverWalk.lean's chain_walk. Joined stands here · role_once (in a seat without a fault a role «behind l n» is borne by one block) · joined_at: «opened» SITS AT EVERY o WITH NO PREMISE BUT THE LINK's SORT: HeadIsTwo, framesOf's return and the row at l are conclusions. opened_joined stays for its callers.
OBJECT. c.links[l].hear[0] of onlineDescription's first chain, as ProofFile.chainBy joins it (Johnson/Desc/ProofFile/Frames1.lean: «fr.find? fun x => behind b x.1», behind b (.behind l m) := b.name == m && b.place.link == some l).
USER. frames_sit's middle third (Johnson/IMR/FrameYes.lean) · «K07_sits» (declared nowhere in this library) · «K02_sits» (the files Johnson/P1K2R/Sits….lean) · other files of this folder: Johnson/IMR/FirstSeats.lean has the tops in scope.
LETTERS. As in Johnson/IMR/K6Seat.lean; fs · f as in Johnson/IMR/FrameSeat.lean; sp: a spot of the plan's list Bs.spots; e: an entry (name, place) of the shape Bs.shape.
OVER WHICH FILES: Block.lean · Driver/Chain.lean
· SeatGuard.lean · Johnson/Desc/ProofFile/OnlineDescription.lean · Pure.lean · Frames1.lean · Lots/PureLots.lean.
Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT
EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where
publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean ·
Ladder/Bits.lean) hand every o: for these the in-scope halves are still owed, at PublicCut (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean)).

  flat_block_at   (the driver; general in the record H) a block of the chain's flat list whose place
                  is of a kind other than «frame» and K9 bears the name of what the record gives AT
                  THAT PLACE.
  shape_name_at     so the shape's name at such a place is the name of THE FIRST SPOT, BUT THE LAST, AT THAT PLACE (the shape is the driver's chain over idle blocks, one a spot, in the spots' order).
  find_side · dropLast_at · base_at   two lists of one length whose members agree number by number on two tests: the first that passes the one stands at the number of the first that passes the other; the list of the places' blocks against the list of spots.
  hear_first_spot   so a block in front of a link's batching, of a kind other than K9, bears the name of THAT SAME SPOT.
  link_first_is | _mem · flat_of_link · frames_in_seat · opened_role   a member of the parts' frames bears the role «behind l n», n the shape's name at link l's first place: it is guardMark of link l's own row's «opened» (the frames' lot lays one for every row).
  opened_joined     (AT EVERY o; NO PREMISE ON SCOPE BUT WHAT IS NAMED: HeadIsTwo Z · framesOf has returned fs · fs[l]? = some f · the sort at l) hear[0] = seatedWith sameReply b' (guardMark (openedOf f).retype) b.name (1, some l, 1, k), b' a lot's block at that address.

HOW: Johnson/IMR/PureChain.lean's chain_hear: alone ONLY where no member bears the role «behind l ‹the spot's name›»; opened_role's member bears it, since both names are the first spot's. ProofFile's lackingAt («enters») and String.endsWith ".quiet" are not needed.
WHO PAYS THE PREMISES: in scope: head_is_two · frame_of · subs_scope (Johnson/IMR/FirstSeats.lean: first_sits).
What is not claimed. What f.opened is at which link (Johnson/IMR/FrameSeat.lean: frames_arms, arm by
arm; Johnson/IMR/FirstSeats.lean: the head's is the identity). What the blocks decide. No soundness.
-/
import Johnson.IMR.FrameSeat
import Johnson.IMR.BackSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt blockAt kindsBeforeBatching addresses
  hearsReply closeAddresses closeKinds backKinds mem_of_mapM linkPlaces flatPlacesOf frameAt)
open OnBytes.L5.LinksOrder (ok_bind)
open ProofFile (Cl)

/-! ## 1 The driver: a block of the flat list at an address of a kind is the socket's at that address -/

/-- A block of the driver's chain's flat list whose place is of a kind other than «frame» and K9 bears the name of what the record gives at that place. (Johnson/IMR/DriverWalk.lean's chain_walk, read off.) -/
theorem flat_block_at {σ C : Type} {H : Blocks σ C} {links : List ModelPart} {several : Bool}
    {c : Chain σ C} (h : firstChain H links several = some c) {x : Block σ C} (hx : x ∈ c.blocksInOrder)
    (hk : x.place.kind ≠ KindName.frame) (hk9 : x.place.kind ≠ KindName.K9) :
    ∃ b, H.block x.place = some b ∧ x.name = b.name := by
  rcases chain_walk h hx with ⟨l, sub, -, hm⟩ | ⟨b, hb, en, -, -⟩ | ⟨hkf, -⟩
  · rcases hm with ⟨b, hb, en, -, -⟩ | ⟨mk, g, -, -, ep⟩ | ⟨hkf, -⟩
    · exact ⟨b, hb, en⟩
    · exact absurd (by rw [ep]) hk9
    · exact absurd hkf hk
  · exact ⟨b, hb, en⟩
  · exact absurd hkf hk

/-! ## 2 The shape's name at an address is the name of the first spot, but the last, at that place -/

theorem shape_name_at {Z : ProofFile.Pub} {spots : List ProofFile.Spot} {shape : List (String × Place)}
    (hs : ProofFile.spotsOf Z.cuts = some spots) (h : ProofFile.shapeOf Z = .ok shape) {e : String × Place}
    (he : e ∈ shape) (hk : e.2.kind ≠ KindName.frame) (hk9 : e.2.kind ≠ KindName.K9) :
    ∃ p, spots.dropLast.find? (fun p => p.place == e.2) = some p ∧ e.1 = p.name := by
  unfold ProofFile.shapeOf at h
  obtain ⟨spots', hs', h⟩ := ok_bind h
  obtain rfl : spots = spots' := Option.some.inj (hs.symm.trans (orSay_ok hs'))
  dsimp only at h
  obtain ⟨c, hc, h⟩ := ok_bind h
  cases h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
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
        obtain ⟨b, hb, en⟩ := flat_block_at h1 hx hk hk9
        have hb' : (List.map (fun p : ProofFile.Spot =>
            ({ (roundlessBlock p.name 1 none 0 .ok : Block Unit Unit) with place := p.place } :
              Block Unit Unit)) spots).dropLast.find? (fun b => b.place == x.place) = some b := hb
        rw [← List.map_dropLast, List.find?_map] at hb'
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hb'
        exact ⟨p, hp, en⟩

/-! ## 3 Two lists searched side by side -/

/-- Two lists of one length whose members agree, number by number, on two tests: the first member that passes the one stands at the number of the first that passes the other. -/
theorem find_side {α β : Type} (p : α → Bool) (q : β → Bool) (R : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (∀ (i : ℕ) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → R x y ∧ p x = q y) →
      ∀ y, ys.find? q = some y → ∃ x, xs.find? p = some x ∧ R x y
  | [], [], _, _, y, h => by cases h
  | [], _ :: _, hl, _, _, _ => by cases hl
  | _ :: _, [], hl, _, _, _ => by cases hl
  | x :: xs, y0 :: ys, hl, hR, y, h => by
    obtain ⟨r0, e0⟩ := hR 0 x y0 rfl rfl
    rw [List.find?_cons] at h ⊢
    rw [e0]
    cases hq : q y0 with
    | true =>
      rw [hq] at h
      obtain rfl : y0 = y := Option.some.inj h
      exact ⟨x, rfl, r0⟩
    | false =>
      rw [hq] at h
      exact find_side p q R xs ys (Nat.succ.inj hl) (fun i a b ha hb => hR (i + 1) a b ha hb) y h

theorem dropLast_at {α : Type} {l : List α} {i : ℕ} {x : α} (h : l.dropLast[i]? = some x) :
    l[i]? = some x := by
  rw [List.getElem?_dropLast] at h
  split at h
  · exact h
  · cases h

/-! ## 4 The true chain takes, at an address of a kind, the block of that same spot -/

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Number by number: the list of the places' blocks against the list of spots. -/
theorem base_at (O : Open o pol lay KL F Z Bs base c A B) {i : ℕ} {s : ProofFile.Spot} {b0 : Block S Cl}
    (hs : Bs.spots[i]? = some s) (hb : base[i]? = some b0) :
    (s, Except.ok b0) ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places := by
  have h1 : ((ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places.map (·.1))[i]? = some s := by
    rw [places_spots]
    exact hs
  rw [List.getElem?_map] at h1
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨s', y⟩ := x
  obtain rfl : s' = s := e
  obtain ⟨b, hb', e'⟩ := OnBytes.Road.Hd.mapM_ok _ _ _ O.places i _ hx
  obtain rfl : b = b0 := Option.some.inj (hb'.symm.trans hb)
  obtain rfl : y = .ok b := e'
  exact List.mem_of_getElem? hx

/-- **A block in front of a link's batching bears the name of the FIRST spot, but the last, at its address.** -/
theorem hear_first_spot (O : Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) (hk9 : k ≠ KindName.K9) :
    ∃ Lk b sp, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      Bs.spots.dropLast.find? (fun p => p.place ==
        { chain := 1, link := some l, piece := i + 1, kind := k }) = some sp ∧ b.name = sp.name := by
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  have hc := O.chain
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
        obtain ⟨bj, hbk, eb⟩ := linkAt_hear hLk i k hk
        have hbk' := hbk
        simp only [ProofFile.fill] at hbk'
        obtain ⟨sp, hsp, b0, hR, en, epl⟩ : ∃ sp, Bs.spots.dropLast.find? (fun p : ProofFile.Spot => p.place ==
            { chain := 1, link := some l, piece := i + 1, kind := k }) = some sp ∧
            ∃ b0, (sp, Except.ok b0) ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places ∧
              bj.name = b0.name ∧ bj.place = b0.place := by
          refine find_side _ _ (fun s b => ∃ b0, (s, Except.ok b0) ∈
            (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places ∧ b.name = b0.name ∧ b.place = b0.place)
            _ _ ?_ ?_ bj hbk'
          · rw [List.length_dropLast, List.length_dropLast, List.length_map,
              OnBytes.Road.Hd.mapM_length _ _ _ O.places, ← places_spots (ProofFile.pureSeat o Z) Bs,
              List.length_map]
          · intro j s b hs hb
            have hb2 := dropLast_at hb
            rw [List.getElem?_map] at hb2
            obtain ⟨b0, hb0, ej⟩ := Option.map_eq_some_iff.1 hb2
            have hm := base_at O (dropLast_at hs) hb0
            have hkeep : b.name = b0.name ∧ b.place = b0.place := by
              split at ej <;> subst ej <;> exact ⟨rfl, rfl⟩
            refine ⟨⟨b0, hm, hkeep⟩, ?_⟩
            rw [hkeep.2]
            obtain ⟨-, harm⟩ := places_from_lots hall s b0 hm
            rcases harm with ⟨mk, hmk, rfl⟩ | ⟨-, L, -, b', -, ep, rfl⟩
            · have k1 := face_kind (makers_K9 Z Bs.G₀) hmk (fun s => .ok ([], s))
              obtain ⟨mk0, h0, -⟩ := road_batch_some hmk
              obtain ⟨-, -, k2, -⟩ := k9_batch_some h0
              have n1 : (s.place == ({ chain := 1, link := some l, piece := i + 1, kind := k } : Place))
                  = false := by
                apply beq_false_of_ne
                intro e
                rw [e] at k2
                exact hk9 k2
              have n2 : ((mk fun s => .ok ([], s)).place ==
                  ({ chain := 1, link := some l, piece := i + 1, kind := k } : Place)) = false := by
                apply beq_false_of_ne
                intro e
                rw [e] at k1
                exact hk9 k1
              rw [n1, n2]
            · show _ = (b'.place == _)
              rw [ep]
        refine ⟨_, _, sp, eLk, (by
          show (Lk.hear.map _)[i]? = _
          rw [List.getElem?_map, eb]
          rfl), hsp, ?_⟩
        have hpl : bj.place = { chain := 1, link := some l, piece := i + 1, kind := k } := by
          simpa using List.find?_some hbk'
        obtain ⟨-, harm⟩ := places_from_lots hall sp b0 hR
        have hname : b0.name = sp.name := by
          rcases harm with ⟨mk, hmk, rfl⟩ | ⟨-, L, -, b', -, ep, rfl⟩
          · exfalso
            have k1 := face_kind (makers_K9 Z Bs.G₀) hmk (fun s => .ok ([], s))
            rw [← epl, hpl] at k1
            exact hk9 k1
          · rfl
        show bj.name = sp.name
        rw [en, hname]

/-! ## 5 The role «behind l ‹the first place's name›» is borne, by link l's own row's «opened» -/

/-- In a link's places the one of piece 1 is the first hearing place. -/
theorem link_first_is (l : ℕ) (sub : ModelPart) : ∀ a ∈ linkPlaces l sub, a.piece = 1 →
    (kindsBeforeBatching sub (l == 0))[0]? = some a.kind ∧ a.chain = 1 ∧ a.link = some l := by
  cases sub <;> cases hb : (l == 0) <;>
    simp [linkPlaces, kindsBeforeBatching, addresses, closeAddresses, closeKinds, frameAt,
      VerifiableInference.Desc.First.kindOfModelPart, hb]

/-- And it is there. -/
theorem link_first_mem (l : ℕ) (sub : ModelPart) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[0]? = some k) :
    ({ chain := 1, link := some l, piece := 1, kind := k } : Place) ∈ linkPlaces l sub := by
  revert hk
  cases sub <;> cases hb : (l == 0) <;>
    simp [linkPlaces, kindsBeforeBatching, addresses, closeAddresses, closeKinds, frameAt,
      VerifiableInference.Desc.First.kindOfModelPart, hb] <;> rintro rfl <;> simp

theorem flat_of_link {links : List ModelPart} (several : Bool) {a : Place} {l : ℕ} {sub : ModelPart}
    (hl : links[l]? = some sub) (h : a ∈ linkPlaces l sub) : a ∈ flatPlacesOf links several := by
  unfold flatPlacesOf
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_flatMap.2 ⟨(sub, l), ?_, h⟩)))
  exact List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using hl)

theorem frames_in_seat (Z : ProofFile.Pub) : ProofFile.framesLot Z ∈ ProofFile.onlineFirstChainBlockTables Z := by
  unfold ProofFile.onlineFirstChainBlockTables
  simp

/-- **A member of the parts' frames bears the role «behind l n», n the shape's name at link l's first place; it is guardMark of link l's own row's «opened».** -/
theorem opened_role (O : Open o pol lay KL F Z Bs base c A B)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs) {l : ℕ}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} (hf : fs[l]? = some f) {sub : ModelPart}
    (hl : (ProofFile.subsOf Z)[l]? = some sub) {k : KindName}
    (hk : (kindsBeforeBatching sub (l == 0))[0]? = some k) (hkf : k ≠ KindName.frame) :
    ∃ e ∈ Bs.shape, e.2 = { chain := 1, link := some l, piece := 1, kind := k } ∧
      (ProofFile.FrameRole.behind l e.1, ProofFile.guardMark (openedOf f).retype) ∈
        (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames := by
  obtain ⟨-, hsh, -, hall⟩ := base_made O.made
  obtain ⟨several, hpls⟩ := shape_places hsh
  obtain ⟨hlink, -⟩ := frames_idx hfs l f hf
  -- the shape has an entry at the first place
  have hmem : ({ chain := 1, link := some l, piece := 1, kind := k } : Place) ∈
      Bs.shape.map (·.2) := by
    rw [hpls]
    exact flat_of_link several hl (link_first_mem l sub k hk)
  obtain ⟨e0, he0, ee0⟩ := List.mem_map.1 hmem
  -- so roleOf's search finds one
  have hsome : (Bs.shape.find? fun b => b.2.chain == 1 && b.2.link == some l &&
      b.2.piece == 1).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨e0, he0, by rw [ee0]; simp⟩
  obtain ⟨e, hfind⟩ := Option.isSome_iff_exists.1 hsome
  have he := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  -- and what it finds is the first place's
  have hin : e.2 ∈ flatPlacesOf (ProofFile.subsOf Z) several := by
    rw [← hpls]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨sub', hsub', hin'⟩ := flat_in_link hin hp.1.2
  obtain rfl : sub = sub' := Option.some.inj (hl.symm.trans hsub')
  obtain ⟨hk', -, -⟩ := link_first_is l sub e.2 hin' hp.2
  have ek : e.2.kind = k := Option.some.inj (hk'.symm.trans hk)
  have ee : e.2 = { chain := 1, link := some l, piece := 1, kind := k } := by
    obtain ⟨n, ⟨ch, lk, pc, kd⟩⟩ := e
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    dsimp only at h1 h2 h3 ek
    subst h1 h2 h3 ek
    rfl
  refine ⟨e, he, ee, ?_⟩
  have hrole : ProofFile.roleOf Bs.shape ((openedOf f).retype : Block S Cl).place =
      ProofFile.FrameRole.behind l e.1 := by
    show ProofFile.roleOf Bs.shape { chain := 1, link := some f.link, piece := 1, kind := .frame } = _
    rw [hlink]
    unfold ProofFile.roleOf
    dsimp only
    rw [hfind]
    dsimp only
    rw [if_pos (by rw [ek]; simpa using hkf)]
  simp only [ProofFile.partsAt]
  refine List.mem_flatMap.2 ⟨(ProofFile.framesLot Z, (ProofFile.framesLot Z).blocks Bs.G₀), ?_, ?_⟩
  · rw [hall]
    exact List.mem_map.2 ⟨_, frames_in_seat Z, rfl⟩
  · dsimp only
    rw [if_neg (by
      show ¬ (false = true)
      decide)]
    refine List.mem_filterMap.2 ⟨(openedOf f).retype, List.mem_filter.2 ⟨?_, rfl⟩, ?_⟩
    · unfold ProofFile.Lot.blocks ProofFile.asCl
      refine List.mem_append_left _ (List.mem_map.2 ⟨openedOf f, ?_, rfl⟩)
      show openedOf f ∈ P1L20.blocksOf Z
      unfold P1L20.blocksOf
      rw [hfs]
      refine List.mem_flatMap.2 ⟨f, List.mem_of_getElem? hf, ?_⟩
      unfold ProofFile.frameBlocks openedOf
      simp
    · rw [hrole]

/-! ## 6 «opened» sits -/

/-- **AT A LINK's FIRST PLACE THE «opened» OF THE LINK's OWN ROW IS JOINED BEHIND THE LOT's BLOCK.** No premise on scope but what is named: HeadIsTwo Z · framesOf has returned · the row and the sort at l. -/
theorem opened_joined (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs) {l : ℕ}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} (hf : fs[l]? = some f) {sub : ModelPart}
    (hl : (ProofFile.subsOf Z)[l]? = some sub) {k : KindName}
    (hk : (kindsBeforeBatching sub (l == 0))[0]? = some k) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
      ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks Bs.G₀,
        b'.place = { chain := 1, link := some l, piece := 0 + 1, kind := k } ∧
        b = seatedWith ProofFile.sameReply b' (ProofFile.guardMark (openedOf f).retype) b.name
          { chain := 1, link := some l, piece := 0 + 1, kind := k } := by
  have hkk : k ≠ KindName.K9 ∧ k ≠ KindName.frame := by
    constructor <;> rintro rfl <;> revert hk <;> cases sub <;> cases (l == 0) <;> decide
  obtain ⟨hs, hsh, -, hall⟩ := base_made O.made
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, harm⟩ :=
    chain_hear hall (makers_K9 Z Bs.G₀) O.places O.chain l sub hl 0 k hk hkk.1
  refine ⟨Lk, b, e1, e2, L, hL, b', hb', ep, ?_⟩
  rcases harm with ⟨h, hno⟩ | ⟨x, hx, hr, h⟩
  · exfalso
    -- the name of the block is the first spot's at the address, and so is the shape's name there
    obtain ⟨Lk', b1, sp1, e1', e2', hfind1, en1⟩ := hear_first_spot O l sub hl 0 k hk hkk.1
    obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
    obtain rfl : b = b1 := Option.some.inj (e2.symm.trans e2')
    obtain ⟨e, he, ee, hmem⟩ := opened_role O hfs hf hl hk hkk.2
    obtain ⟨p, hfind2, en2⟩ := shape_name_at hs hsh he (by rw [ee]; exact hkk.2)
      (by rw [ee]; exact hkk.1)
    rw [ee] at hfind2
    obtain rfl : sp1 = p := Option.some.inj (hfind1.symm.trans hfind2)
    refine hno _ hmem ?_
    show ProofFile.FrameRole.behind l e.1 = ProofFile.FrameRole.behind l sp.name
    rw [en2, ← en1, alone_name h]
  · obtain ⟨fs', f', hfs', hf', ex⟩ := behind_block O.made hk2 hx hr
    obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
    obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
    have hname : b.name = sp.name := by
      rw [h]
      rfl
    rw [ex] at h
    rw [hname]
    exact h

/-! ## 7 The same with no premise but the link's sort: at every o -/

/-- b is the lot's block b' with THE «opened» OF LINK l's OWN ROW OF framesOf joined behind it. -/
def Joined (Z : ProofFile.Pub) (l : ℕ) (b b' : Block S Cl) (a : Place) : Prop :=
  ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
    fs[l]? = some f ∧
    b = seatedWith ProofFile.sameReply b' (ProofFile.guardMark (openedOf f).retype) b.name a

/-- **In a seat without a fault a role «behind l n» is borne by one block.** -/
theorem role_once {T : ProofFile.PureSeat} {Bq : ProofFile.PureBase} (hf : ProofFile.faultsAt T Bq = [])
    (hall : Bq.all = T.lots.map fun L => (L, L.blocks Bq.G₀)) {x y : ProofFile.FrameRole × Block S Cl}
    (hx : x ∈ (ProofFile.partsAt T Bq).frames) (hy : y ∈ (ProofFile.partsAt T Bq).frames) {l : ℕ} {n : String}
    (rx : x.1 = .behind l n) (ry : y.1 = .behind l n) : x.2 = y.2 := by
  obtain ⟨L₁, hL₁, b₁, hb₁, k₁, r₁, e₁⟩ := frames_from_lots hall hx
  obtain ⟨L₂, hL₂, b₂, hb₂, k₂, r₂, e₂⟩ := frames_from_lots hall hy
  have m : ∀ {L : ProofFile.Lot} {b : Block S Cl}, L ∈ T.lots → b ∈ L.blocks Bq.G₀ →
      b ∈ Bq.all.flatMap fun x => x.2 := fun {L b} hL hb => by
    rw [hall]
    exact List.mem_flatMap.2 ⟨(L, L.blocks Bq.G₀), List.mem_map.2 ⟨L, hL, rfl⟩, hb⟩
  simp only [ProofFile.faultsAt, ProofFile.faultsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  generalize hfr : List.map (fun o : Block S Cl => (ProofFile.roleOf Bq.shape o.place, o))
    (List.filter (fun o => o.place.kind == KindName.frame) (Bq.all.flatMap fun x => x.2)) = fr at h2
  have p₁ : (ProofFile.FrameRole.behind l n, b₁) ∈ fr := by
    rw [← hfr]
    exact List.mem_map.2 ⟨b₁, List.mem_filter.2 ⟨m hL₁ hb₁, by simpa using k₁⟩, by rw [← r₁, rx]⟩
  have p₂ : (ProofFile.FrameRole.behind l n, b₂) ∈ fr := by
    rw [← hfr]
    exact List.mem_map.2 ⟨b₂, List.mem_filter.2 ⟨m hL₂ hb₂, by simpa using k₂⟩, by rw [← r₂, ry]⟩
  have hrefl : (ProofFile.FrameRole.behind l n == ProofFile.FrameRole.behind l n) = true := by
    show (l == l && n == n) = true
    simp
  have h3 := List.filterMap_eq_nil_iff.1 h2 _ p₁
  dsimp only at h3
  split at h3
  · cases h3
  · split at h3
    · cases h3
    · split at h3
      · cases h3
      · split at h3
        · cases h3
        · rename_i hc
          have hne : (ProofFile.FrameRole.behind l n != ProofFile.FrameRole.common) = true := rfl
          rw [hne, Bool.and_true] at hc
          have hlen : (fr.filter fun y => y.1 == ProofFile.FrameRole.behind l n).length ≤ 1 := by
            simpa using hc
          have q₁ : (ProofFile.FrameRole.behind l n, b₁) ∈ fr.filter fun y => y.1 == .behind l n :=
            List.mem_filter.2 ⟨p₁, hrefl⟩
          have q₂ : (ProofFile.FrameRole.behind l n, b₂) ∈ fr.filter fun y => y.1 == .behind l n :=
            List.mem_filter.2 ⟨p₂, hrefl⟩
          generalize (fr.filter fun y => y.1 == ProofFile.FrameRole.behind l n) = Lq at hlen q₁ q₂
          match Lq, hlen, q₁, q₂ with
          | [z], _, q₁, q₂ =>
            have e := (List.mem_singleton.1 q₁).trans (List.mem_singleton.1 q₂).symm
            rw [e₁, e₂, (Prod.mk.inj e).2]

/-- **AT A LINK's FIRST PLACE, AT EVERY o, WITH NO PREMISE BUT THE LINK's SORT IN THE ROW OF LINKS: THE LOT's BLOCK WITH THE LINK's OWN ROW's «opened» JOINED.** framesOf's return and the row are CONCLUSIONS (off lackingAt's ask «cleared» and the role's bearer). -/
theorem joined_at (O : Open o pol lay KL F Z Bs base c A B) {l : ℕ} {sub : ModelPart}
    (hl : (ProofFile.subsOf Z)[l]? = some sub) {k : KindName}
    (hk : (kindsBeforeBatching sub (l == 0))[0]? = some k) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
      ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks Bs.G₀,
        b'.place = { chain := 1, link := some l, piece := 1, kind := k } ∧
        Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := k } := by
  have hkk : k ≠ KindName.K9 ∧ k ≠ KindName.frame := by
    constructor <;> rintro rfl <;> revert hk <;> cases sub <;> cases (l == 0) <;> decide
  obtain ⟨hs, hsh, -, hall⟩ := base_made O.made
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, harm⟩ :=
    chain_hear hall (makers_K9 Z Bs.G₀) O.places O.chain l sub hl 0 k hk hkk.1
  -- framesOf has returned, and has a row at l
  obtain ⟨y, hy⟩ : ∃ y, (sp, y) ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places := by
    have h1 : sp ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places.map (·.1) := by
      rw [places_spots]
      exact hsp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h1
    exact ⟨x.2, hx⟩
  obtain ⟨-, xc, hxc, rc⟩ := roles_there O.whole hy (l := l) (by rw [es])
  obtain ⟨fs, f, hfs, hf, -⟩ := clear_block O.made hxc rc
  -- the block's name is the shape's at the address
  have hname : b.name = sp.name := by
    rcases harm with ⟨h, -⟩ | ⟨x, -, -, h⟩
    · exact alone_name h
    · rw [h]
      rfl
  obtain ⟨Lk', b1, sp1, e1', e2', hfind1, en1⟩ := hear_first_spot O l sub hl 0 k hk hkk.1
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : b = b1 := Option.some.inj (e2.symm.trans e2')
  obtain ⟨e, he, ee, hmem⟩ := opened_role O hfs hf hl hk hkk.2
  obtain ⟨p, hfind2, en2⟩ := shape_name_at hs hsh he (by rw [ee]; exact hkk.2)
    (by rw [ee]; exact hkk.1)
  rw [ee] at hfind2
  obtain rfl : sp1 = p := Option.some.inj (hfind1.symm.trans hfind2)
  have ename : e.1 = sp.name := by rw [en2, ← en1, hname]
  refine ⟨Lk, b, e1, e2, L, hL, b', hb', ep, fs, f, hfs, hf, ?_⟩
  rcases harm with ⟨-, hno⟩ | ⟨x, hx, hr, h⟩
  · exact absurd (by rw [← ename]) (hno _ hmem)
  · have ex : x.2 = ProofFile.guardMark (openedOf f).retype :=
      role_once O.sound hall hx hmem hr (by rw [ename])
    rw [ex] at h
    rw [hname]
    exact h

end

end IM

#print axioms IM.role_once
#print axioms IM.joined_at
#print axioms IM.opened_role
#print axioms IM.opened_joined
#print axioms IM.find_side
#print axioms IM.hear_first_spot
#print axioms IM.flat_block_at
#print axioms IM.shape_name_at
