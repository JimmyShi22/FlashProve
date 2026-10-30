-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BackSeat.lean. chain_back_any IS ALONE OUTRIGHT; chain_last's second arm: ∃ l', b0.place.link = some l'; back_of's clause on «M:3»: b' = (k13Dress Z).retype, k13Dress Z := { atM3 (whereOf Z) with planOk := … && (K13.fromOf? Z).isSome }; b' ∈ (K13.lot Z).blocks G₀. SealLast is brought down to one closed sentence in Johnson/IMR/SealSeat.lean.
The rest of this head may differ from this file's text; where it does, the text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: THE BLOCKS BEHIND THE LINKS of onlineDescription's
first chain: «F:2» (K12) · «M:3» (K13) · «M:4» (K1: W's sending) · and what can be said of the
chain's last block (the seal).
(«F:1»: Johnson/IMR/K2Seat.lean: k2_finish_of.)
OBJECT. THE SEATED CONSTANTS, each a member b' of its lot's blocks at the blank letters G₀: K12.lot
Z (Johnson/Desc/ProofFile/Lot/K12.lean): (K12.atFinish (H2U.p12OfMade Z.made)).retype · K13.lot Z
(Johnson/Desc/ProofFile/Lot/K13.lean): (k13Dress Z).retype · K13.lot4 Z
(Johnson/Desc/ProofFile/Lot/K13At4.lean):
(K13.atM4 (K13.whereOf Z) w).retype, w given by K13.wBlock Z = some w; as they stand at c.back[1 | 2
| 3] (c is F.first: by rfl behind «subst» on Open.desc). NOT SEATED, BUT UNDER A PREMISE THAT IS
NOT PAID HERE (SealLast; see `seal_last`, Johnson/IMR/SealSeat.lean): K13.lotEnd Z (K13End.lean):
(ChainEnd.chainEnd 1 5 true (K13.inFrontOf Z) endAsks).retype at c.last.
LETTERS. As in Johnson/IMR/K6Seat.lean; b': by its membership in the lot's blocks AND by an
equation.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).
NO TWIN (NOT SHOWN HERE): K12 at «F:2» is had in the form Sits (Johnson/Loose/H2K12/SitsInPure.lean), not in LaidAlone; elsewhere no lemma of this form; LaidAlone at c.back[j], ending at the lots' blocks, is
no twin of the laws that begin at these blocks: it is the other half. SEARCHED, AND WHERE: for laws on List.mapM at Except: every theorem whose name holds «mapM» in a version of the library's sources (Johnson/ · OnBytes/ · Fmt/) and in the files laid over them: CALLED HERE: OnBytes.Road.Hd.mapM_ok | mapM_length (Johnson/Road/HeadL5Grp.lean) · Fo.Pub.mapM_at
(OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean).

  firstChain_back_len · chain_back_any   (general in the seat) AT THE CHAIN's OWN FLAG «several»
    (true just if a block of the list of the places' blocks has the kind K13): as many blocks behind
    the links as backKinds at that flag; each a lot's block at the blank letters: alone.
                    (Johnson/IMR/BackPlace.lean's chain_back asks backKinds' entry at both values of
                      the flag and so reaches j = 0, 1 alone.)
  k13_in_seat · base_has_K13   at onlineDescription's seat the flag is true: K13's lot lays its block whatever the plan; a seat without a fault (Open.sound) has it at a place of the shape; that place is a spot's; the spot's entry is a lot's block at the spot's place.
  lot_K13 · lot_M4 · lot_end   the lots by kind: K13 · K1 behind the links · «frame» behind the links.
  back_of           (NO PREMISE ON SCOPE; AT EVERY o) c.back.length = 4; c.back[1 | 2 | 3] IS seatedAs sameReply b' b.name (1, none, 2 | 3 | 4, K12 | K13 | K1): ALONE, b' as above.
  places_spots · chain_last   (general in the seat) chainC TAKES THE CHAIN's LAST BLOCK BY POSITION: it stems from the entry of THE LAST SPOT of the plan's list.
  SealLast · seal_of   UNDER A PREMISE THAT IS NOT PAID HERE (the plan's last spot is of the kind «frame» and stands behind the links; see `seal_last`, SealSeat.lean): c.last IS seatedAs sameReply (chainEnd …).retype c.last.name (1, none, 5, frame): ALONE.
  back_at_flat | last_at_flat   (general in the chain; Block.lean's text) their numbers in the flat list, where each stands as { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }.
  links_flat_352 · back_numbers   in scope, at secondHashFunction: the 25 links' flat lists hold 352 blocks; c.back[j] is number 353 + j; c.last is number 357.

WHO PAYS THE PREMISES: an opening: IM.seat_open, off onlineDescription's yes. FOR THE JOIN: alone_underDressed (here) : LaidAlone same b b' name a → b.UnderR { guardMark b' with name := name } (Block.UnderR · Block.UnderR.trans: Johnson/Desc/Sound/SeatGuardChain.lean): IT ENDS AT THE DRESSED TERM; Johnson/IMR/SeatForm.lean's alone_underR goes on to b' itself: EITHER COMPOSES (a
trial over another version of these files joins by alone_underR and its own «b' is UnderR the law's block»); yes_alone | step_alone both ways.
What is not claimed. NOT «c.back[j] = { guardMark x with name := n }»: TWO WRAPPERS MORE STAND AROUND THAT TERM: the driver's address written into it and the driver's guard: c.back[j] = Block.guarded sameReply hearsReply { { guardMark x with name := n } with place := a }; and in the flat list «&& hasNoClaimsAndNothingAfter» is
laid to its test on the plan. «Guards c x» (Johnson/Desc/First/K8/LawSeated.lean) is not spoken of. THE SEAL IS SEATED IN Johnson/IMR/SealSeat.lean (seal_seated: no premise); here seal_of stands under SealLast, which hangs on the cut's grammar (membersCut's list ends in the cut «seal.behind» of the kind «SEAL», under a head of its own; byPlace leaves it a group of its own; spotsFrom's last spot is then of the kind «frame», behind the
links): by a reading it can be paid at every o off Open.pub; not typed here. Open's other clauses do not pay it. No lemma here says b.hasNoClaimsAndNothingAfter = b'.hasNoClaimsAndNothingAfter (for «&& hasNoClaimsAndNothingAfter» in the flat list). That K13.wBlock Z returns is a CONCLUSION here (else the driver found no block at (1, none, 4, K1)). Nothing on what the blocks decide. The names. No soundness.
-/
import Johnson.IMR.CloseSeat
import Johnson.IMR.K1Seat
import Johnson.Road.HeadL5Grp
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard blockAt backKinds addresses hearsReply
  flatPlacesOf)
open OnBytes.L5.LinksOrder (ok_bind)
open ProofFile (Cl)

/-! ## 1 How many blocks stand behind the links -/

theorem firstChain_back_len {σ C : Type} {H : Blocks σ C} {links : List ModelPart} {several : Bool}
    {c : Chain σ C} (h : firstChain H links several = some c) :
    c.back.length = (backKinds several).length := by
  obtain ⟨-, c0, ⟨-, -, -, hbk, -⟩, rfl⟩ := VerifiableInference.Desc.Shape.firstChain_shape h
  have h1 := congrArg List.length hbk
  rw [List.length_map, List.length_map, VerifiableInference.Desc.First.length_addresses] at h1
  show (c0.back.map _).length = _
  rw [List.length_map, h1]

/-- **THE JOIN BEHIND THE LINKS, BY INDEX, AT THE CHAIN's OWN «several»**: chainC's flag is true just if a block of the list of places has the kind K13; the chain has as many blocks behind the links as backKinds at that flag; each is a lot's block
at the blank letters: alone, or with a member of the parts' frames joined. (Johnson/IMR/BackPlace.lean's chain_back asks backKinds' entry at BOTH values of the flag: so it reaches j = 0, 1 alone.) -/
theorem chain_back_any {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hM : MakersK9 T B.G₀) (hb : (ProofFile.partsAt T B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) :
    ∃ several : Bool, (several = true ↔ ∃ b0 ∈ base, b0.place.kind = KindName.K13) ∧
      c.back.length = (backKinds several).length ∧
      ∀ (j : ℕ) (k : KindName), (backKinds several)[j]? = some k → k ≠ KindName.K9 →
        ∃ b, c.back[j]? = some b ∧
          ∃ sp ∈ B.spots, ∃ L ∈ T.lots, ∃ b' ∈ L.blocks B.G₀,
            sp.place = { chain := 1, link := none, piece := j + 1, kind := k } ∧
            b'.place = { chain := 1, link := none, piece := j + 1, kind := k } ∧
            LaidAlone T.same b b' sp.name { chain := 1, link := none, piece := j + 1, kind := k } := by
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
        refine ⟨_, ?_, firstChain_back_len h1, fun j k hk hk9 => ?_⟩
        · rw [List.any_eq_true]
          constructor
          · rintro ⟨y, hy, e⟩
            obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hy
            refine ⟨b0, hb0, ?_⟩
            have e' := e
            split at e' <;> simpa using e'
          · rintro ⟨b0, hb0, e⟩
            refine ⟨_, List.mem_map.2 ⟨b0, hb0, rfl⟩, ?_⟩
            split <;> simpa using e
        · obtain ⟨b, hbk, eb⟩ := firstChain_back h1 j k hk
          refine ⟨_, eb, ?_⟩
          have hm := List.mem_of_find?_eq_some hbk
          have hpl : b.place = { chain := 1, link := none, piece := j + 1, kind := k } := by
            simpa using List.find?_some hbk
          obtain ⟨b0, hb0, ej⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hm)
          obtain ⟨x, hx, ex⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hb b0 hb0
          obtain ⟨sp, y⟩ := x
          obtain rfl : y = .ok b0 := ex
          obtain ⟨hsp, harm⟩ := places_from_lots hall sp b0 hx
          have eplace : b0.place = { chain := 1, link := none, piece := j + 1, kind := k } := by
            split at ej <;> subst ej <;> exact hpl
          rcases harm with ⟨mk, hmk, rfl⟩ | ⟨-, L, hL, b', hb', ep, rfl⟩
          · exfalso
            have hk' := face_kind hM hmk (fun s => .ok ([], s))
            rw [eplace] at hk'
            exact hk9 hk'
          · refine ⟨sp, hsp, L, hL, b', hb', ep.symm.trans eplace, eplace, ?_⟩
            split at ej
            · rename_i w hw
              exfalso
              have hpred := List.find?_some hw
              obtain ⟨r, q⟩ := w
              cases r with
              | behind l' m =>
                have em : sp.name = m ∧ b'.place.link = some l' := by simpa using hpred
                have eplace' : b'.place = { chain := 1, link := none, piece := j + 1, kind := k } :=
                  eplace
                rw [eplace'] at em
                exact nomatch em.2
              | front => cases hpred
              | lay _ => cases hpred
              | clear _ => cases hpred
              | common => cases hpred
              | stray => cases hpred
            · subst ej
              rfl

/-! ## 2 At onlineDescription's seat «several» is true: four blocks stand behind the links -/

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- K13's lot's one block: the kind's block at the plan's numbers, with «and the step from which its rounds are counted is found» laid to its test on the plan. -/
abbrev k13Dress (Z : ProofFile.Pub) : Block S Unit :=
  { (VerifiableInference.Desc.K13.atM3 (VerifiableInference.Desc.K13.whereOf Z) : Block S Unit) with
    planOk := (VerifiableInference.Desc.K13.atM3 (VerifiableInference.Desc.K13.whereOf Z) :
      Block S Unit).planOk && (VerifiableInference.Desc.K13.fromOf? Z).isSome }

theorem k13_in_seat (Z : ProofFile.Pub) : VerifiableInference.Desc.K13.lot Z ∈ ProofFile.onlineFirstChainBlockTables Z := by
  unfold ProofFile.onlineFirstChainBlockTables
  simp

/-- **A block of the kind K13 stands in the list of the places' blocks**: K13's lot lays one whatever the plan; a seat without a fault has it at a place of the shape; that place is a spot's; the spot's entry is a lot's block at the spot's place. -/
theorem base_has_K13 (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ b0 ∈ base, b0.place.kind = KindName.K13 := by
  obtain ⟨hs, hsh, -, hall⟩ := base_made O.made
  have hblk : ((k13Dress Z).retype : Block S Cl) ∈ Bs.all.flatMap fun x => x.2 := by
    rw [hall]
    refine List.mem_flatMap.2 ⟨(VerifiableInference.Desc.K13.lot Z, _),
      List.mem_map.2 ⟨_, k13_in_seat Z, rfl⟩, ?_⟩
    unfold ProofFile.Lot.blocks ProofFile.asCl
    exact List.mem_append_left _ (List.mem_map.2 ⟨_, List.mem_singleton.2 rfl, rfl⟩)
  obtain ⟨e, he, ee⟩ := stands_in_shape O.sound hblk (by
    show KindName.K13 ≠ KindName.frame
    decide)
  have hke : e.2.kind = KindName.K13 := by rw [ee]; rfl
  obtain ⟨sp, hsp, -, ep⟩ := shape_spot hs hsh he (by rw [hke]; decide)
  have hpl : ∃ y, (sp, y) ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).places := by
    simp only [ProofFile.partsAt]
    exact ⟨_, List.mem_map.2 ⟨sp, hsp, rfl⟩⟩
  obtain ⟨y, hy⟩ := hpl
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
  obtain ⟨b0, hb0, e0⟩ := OnBytes.Road.Hd.mapM_ok _ _ _ O.places i _ hi
  obtain rfl : y = .ok b0 := e0
  refine ⟨b0, List.mem_of_getElem? hb0, ?_⟩
  obtain ⟨-, harm⟩ := places_from_lots hall sp b0 hy
  rcases harm with ⟨mk, hmk, -⟩ | ⟨-, L, -, b', -, ep', rfl⟩
  · exfalso
    obtain ⟨mk0, h0, -⟩ := road_batch_some hmk
    obtain ⟨-, -, k1, -⟩ := k9_batch_some h0
    rw [ep, hke] at k1
    cases k1
  · show b'.place.kind = _
    rw [ep', ep, hke]

/-! ## 3 The lots by kind, behind the links -/

/-- A block of the kind K13 of the seat is K13's lot's one. -/
theorem lot_K13 {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) {b : Block S Cl}
    (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.K13) :
    L = VerifiableInference.Desc.K13.lot Z ∧ b = (k13Dress Z).retype := by
  have hLe : L = VerifiableInference.Desc.K13.lot Z := by
    unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl)
    · rw [kind_frames Z G b hb] at hk; cases hk
    · rw [kind_K1 Z G b hb] at hk; cases hk
    · rw [kind_K2 Z G b hb] at hk; cases hk
    · rw [kind_K3 Z G b hb] at hk; cases hk
    · rw [kind_K4 Z G b hb] at hk; cases hk
    · rw [kind_K5 Z G b hb] at hk; cases hk
    · rw [kind_K8 Z G b hb] at hk; cases hk
    · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
    · rw [kind_K11 Z G b hb] at hk; cases hk
    · rw [kind_K12 Z G b hb] at hk; cases hk
    · rfl
    · rw [kind_K13_4 Z G b hb] at hk; cases hk
    · rw [kind_K13_end Z G b hb] at hk; cases hk
    · rw [kind_K6 Z G b hb] at hk; cases hk
    · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk
  subst hLe
  refine ⟨rfl, ?_⟩
  rcases blocks_mem hb with ⟨x, hx, rfl⟩ | h
  · obtain rfl := List.mem_singleton.1 hx
    rfl
  · exact nomatch h

/-- A block of the kind K1 of the seat that stands behind the links is the second lot's of K13's files (K13.lot4): W's sending with the own group and (Eval) behind it. -/
theorem lot_M4 {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) {b : Block S Cl}
    (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.K1) (hl : b.place.link = none) :
    L = VerifiableInference.Desc.K13.lot4 Z ∧ ∃ w, VerifiableInference.Desc.K13.wBlock Z = some w ∧
      b = (VerifiableInference.Desc.K13.atM4 (VerifiableInference.Desc.K13.whereOf Z) w :
        Block S Unit).retype := by
  have hLe : L = VerifiableInference.Desc.K13.lot4 Z := by
    unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl)
    · rw [kind_frames Z G b hb] at hk; cases hk
    · exfalso
      rcases blocks_mem hb with ⟨x, hx, rfl⟩ | h
      · have hl' : x.place.link = none := hl
        rcases k1_mem hx with rfl | ⟨l, X, pr, pd, reads, digits, -, -, rfl | rfl⟩
        · exact nomatch hl'
        · exact nomatch hl'
        · exact nomatch hl'
      · exact nomatch h
    · rw [kind_K2 Z G b hb] at hk; cases hk
    · rw [kind_K3 Z G b hb] at hk; cases hk
    · rw [kind_K4 Z G b hb] at hk; cases hk
    · rw [kind_K5 Z G b hb] at hk; cases hk
    · rw [kind_K8 Z G b hb] at hk; cases hk
    · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
    · rw [kind_K11 Z G b hb] at hk; cases hk
    · rw [kind_K12 Z G b hb] at hk; cases hk
    · rw [kind_K13 Z G b hb] at hk; cases hk
    · rfl
    · rw [kind_K13_end Z G b hb] at hk; cases hk
    · rw [kind_K6 Z G b hb] at hk; cases hk
    · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk
  subst hLe
  refine ⟨rfl, ?_⟩
  rcases blocks_mem hb with ⟨x, hx, rfl⟩ | h
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    rw [Option.mem_toList] at hw
    exact ⟨w, hw, rfl⟩
  · exact nomatch h

/-! ## 4 The blocks behind the links -/

/-- **FOR A JOIN THAT BEGINS AT THE DRESSED TERM**: the seated block has the rounds of { guardMark b' with name := name }, and its yes is that term's yes at the same record. (Johnson/IMR/SeatForm.lean's alone_underR goes one layer deeper, to b' itself: it composes, by Block.UnderR.trans, with a law that begins at b'; this one with a law that begins at the dressed
term. To join by the first: (alone_underR h).trans ‹b' is UnderR the law's block›.) -/
theorem alone_underDressed {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) : b.UnderR { ProofFile.guardMark b' with name := name } := by
  subst h
  exact ⟨rfl, fun s rs gs t hy =>
    VerifiableInference.Desc.guarded_under same hearsReply { marked b' name with place := a } s rs gs t hy⟩

/-- The address of block number j behind the links. -/
abbrev bAt (j : ℕ) (k : KindName) : Place := { chain := 1, link := none, piece := j + 1, kind := k }

/-- **BEHIND THE LINKS OF onlineDescription's FIRST CHAIN STAND FOUR BLOCKS; THE SECOND, THIRD AND FOURTH ARE K12's, K13's AND K13's FILES' SECOND LOT's OWN, EACH ALONE.** No premise on scope. (The first, «F:1»: Johnson/IMR/K2Seat.lean: k2_finish_of.) -/
theorem back_of (O : Open o pol lay KL F Z Bs base c A B) :
    c.back.length = 4 ∧
    (∃ b b', c.back[1]? = some b ∧ b' ∈ (VerifiableInference.Desc.K12.lot Z).blocks Bs.G₀ ∧
      b' = (VerifiableInference.Desc.K12.atFinish (H2U.p12OfMade Z.made)).retype ∧
      LaidAlone ProofFile.sameReply b b' b.name (bAt 1 .K12)) ∧
    (∃ b b', c.back[2]? = some b ∧ b' ∈ (VerifiableInference.Desc.K13.lot Z).blocks Bs.G₀ ∧
      b' = (k13Dress Z).retype ∧
      LaidAlone ProofFile.sameReply b b' b.name (bAt 2 .K13)) ∧
    (∃ b b' w, c.back[3]? = some b ∧ b' ∈ (VerifiableInference.Desc.K13.lot4 Z).blocks Bs.G₀ ∧
      VerifiableInference.Desc.K13.wBlock Z = some w ∧
      b' = (VerifiableInference.Desc.K13.atM4 (VerifiableInference.Desc.K13.whereOf Z) w :
        Block S Unit).retype ∧
      LaidAlone ProofFile.sameReply b b' b.name (bAt 3 .K1)) := by
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨sv, hsv, hlen, hat⟩ := chain_back_any hall (makers_K9 Z Bs.G₀) O.places O.chain
  obtain rfl : sv = true := hsv.2 (base_has_K13 O)
  have alone : ∀ (j : ℕ) (k : KindName), (backKinds true)[j]? = some k → k ≠ KindName.K9 →
      k ≠ KindName.K10 → 1 ≤ j → j ≤ 8 → ∃ b, c.back[j]? = some b ∧ ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z,
        ∃ b' ∈ L.blocks Bs.G₀, b'.place = bAt j k ∧ LaidAlone ProofFile.sameReply b b' b.name (bAt j k) := by
    intro j k hk h9 h10 h1 h8
    obtain ⟨b, e, sp, hsp, L, hL, b', hb', es, ep, h⟩ := hat j k hk h9
    refine ⟨b, e, L, hL, b', hb', ep, ?_⟩
    rw [alone_name h]
    exact h
  refine ⟨hlen, ?_, ?_, ?_⟩
  · obtain ⟨b, e, L, hL, b', hb', ep, h⟩ := alone 1 .K12 rfl (by decide) (by decide) (by decide) (by decide)
    obtain rfl : L = VerifiableInference.Desc.K12.lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
    refine ⟨b, b', e, hb', ?_, h⟩
    rcases blocks_mem hb' with ⟨x, hx, rfl⟩ | h'
    · obtain rfl := List.mem_singleton.1 hx
      rfl
    · exact nomatch h'
  · obtain ⟨b, e, L, hL, b', hb', ep, h⟩ := alone 2 .K13 rfl (by decide) (by decide) (by decide) (by decide)
    obtain ⟨rfl, eb⟩ := lot_K13 hL hb' (by rw [ep])
    exact ⟨b, b', e, hb', eb, h⟩
  · obtain ⟨b, e, L, hL, b', hb', ep, h⟩ := alone 3 .K1 rfl (by decide) (by decide) (by decide) (by decide)
    obtain ⟨rfl, w, hw, eb⟩ := lot_M4 hL hb' (by rw [ep]) (by rw [ep])
    exact ⟨b, b', w, e, hb', hw, eb, h⟩

end

/-! ## 5 The chain's last block: what can be said -/

/-- The driver's address of the chain's last block, behind n blocks behind the links. -/
abbrev sealAt (n : ℕ) : Place := { chain := 1, link := none, piece := n + 1, kind := .frame }

theorem places_spots (T : ProofFile.PureSeat) (B : ProofFile.PureBase) :
    (ProofFile.partsAt T B).places.map (·.1) = B.spots := by
  simp only [ProofFile.partsAt, List.map_map]
  exact List.map_id _

/-- **chainC TAKES THE CHAIN's LAST BLOCK BY POSITION**: it stems from the entry of THE LAST SPOT of the plan's list: with the driver's address of the seal written into it, behind the driver's guard; or something is joined behind it. General in the seat. -/
theorem chain_last {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hb : (ProofFile.partsAt T B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) :
    ∃ sp b0, B.spots.getLast? = some sp ∧ (sp, Except.ok b0) ∈ (ProofFile.partsAt T B).places ∧
      (c.last = Block.guarded T.same hearsReply { b0 with place := sealAt c.back.length } ∨
        ∃ l', b0.place.link = some l') := by
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
        rw [List.getLast?_map] at hz
        obtain ⟨b0, hb0, ez⟩ := Option.map_eq_some_iff.1 hz
        rw [List.getLast?_eq_getElem?] at hb0
        obtain ⟨x, hx, ex⟩ := Fo.Pub.mapM_at _ _ _ hb _ b0 hb0
        obtain ⟨sp, y⟩ := x
        obtain rfl : y = .ok b0 := ex
        have hlen : base.length = B.spots.length := by
          rw [OnBytes.Road.Hd.mapM_length _ _ _ hb, ← places_spots T B, List.length_map]
        have hsp : B.spots.getLast? = some sp := by
          rw [List.getLast?_eq_getElem?, ← hlen, ← places_spots T B, List.getElem?_map, hx]
          rfl
        refine ⟨sp, b0, hsp, List.mem_of_getElem? hx, ?_⟩
        have hblen := firstChain_back_len h1
        obtain ⟨-, c0, ⟨-, -, -, -, hlast⟩, rfl⟩ := VerifiableInference.Desc.Shape.firstChain_shape h1
        split at ez
        · rename_i w hw
          right
          have hpred := List.find?_some hw
          obtain ⟨r, q⟩ := w
          cases r with
          | behind l' m =>
            have em : b0.name = m ∧ b0.place.link = some l' := by simpa using hpred
            exact ⟨l', em.2⟩
          | front => cases hpred
          | lay _ => cases hpred
          | clear _ => cases hpred
          | common => cases hpred
          | stray => cases hpred
        · subst ez
          left
          rw [hblen]
          show Block.guarded _ hearsReply c0.last = _
          rw [hlast]
          rfl

/-- A block of the kind «frame» of the seat that stands behind the links is the third lot's of K13's files (K13.lotEnd): the first chain's end. -/
theorem lot_end {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) {b : Block S Cl}
    (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.frame) (hl : b.place.link = none) :
    L = VerifiableInference.Desc.K13.lotEnd Z ∧
      b = (VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Z)
        VerifiableInference.Desc.First.endAsks : Block S Unit).retype := by
  have hLe : L = VerifiableInference.Desc.K13.lotEnd Z := by
    unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl)
    · exfalso
      rcases blocks_mem hb with ⟨x, hx, rfl⟩ | h
      · have hl' : x.place.link = none := hl
        have hx' : x ∈ P1L20.blocksOf Z := hx
        unfold P1L20.blocksOf at hx'
        split at hx'
        · obtain ⟨f, -, h⟩ := List.mem_flatMap.1 hx'
          unfold ProofFile.frameBlocks at h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> exact nomatch hl'
        · obtain rfl := List.mem_singleton.1 hx'
          exact nomatch hl'
      · exact nomatch h
    · rw [kind_K1 Z G b hb] at hk; cases hk
    · rw [kind_K2 Z G b hb] at hk; cases hk
    · rw [kind_K3 Z G b hb] at hk; cases hk
    · rw [kind_K4 Z G b hb] at hk; cases hk
    · rw [kind_K5 Z G b hb] at hk; cases hk
    · rw [kind_K8 Z G b hb] at hk; cases hk
    · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
    · rw [kind_K11 Z G b hb] at hk; cases hk
    · rw [kind_K12 Z G b hb] at hk; cases hk
    · rw [kind_K13 Z G b hb] at hk; cases hk
    · rw [kind_K13_4 Z G b hb] at hk; cases hk
    · rfl
    · rw [kind_K6 Z G b hb] at hk; cases hk
    · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk
  subst hLe
  refine ⟨rfl, ?_⟩
  rcases blocks_mem hb with ⟨x, hx, rfl⟩ | h
  · obtain rfl := List.mem_singleton.1 hx
    rfl
  · exact nomatch h

/-- A PREMISE THAT IS NOT PAID HERE (see `seal_last`, SealSeat.lean): the plan's last spot is of the kind «frame» and stands behind the links. (It hangs on the cut's grammar: that the list of cuts ends in the one of the kind «SEAL», under a head of its own that stands behind the links. Its chain and piece need not
be premised: the lot's block at that spot's place is the chain's end, whose place is (1, none, 5, frame).) -/
def SealLast (spots : List ProofFile.Spot) : Prop :=
  ∀ sp, spots.getLast? = some sp → sp.place.kind = KindName.frame ∧ sp.place.link = none

/-- **THE SEAL, UNDER THAT PREMISE: THE CHAIN's LAST BLOCK IS K13's FILES' THIRD LOT's OWN, ALONE.** -/
theorem seal_of {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : Open o pol lay KL F Z Bs base c A B) (hz : SealLast Bs.spots) :
    ∃ b', b' ∈ (VerifiableInference.Desc.K13.lotEnd Z).blocks Bs.G₀ ∧
      b' = (VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Z)
        VerifiableInference.Desc.First.endAsks : Block S Unit).retype ∧
      LaidAlone ProofFile.sameReply c.last b' c.last.name
        { chain := 1, link := none, piece := 5, kind := .frame } := by
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨h4, -⟩ := back_of O
  obtain ⟨sp, b0, hsp, hx, harm⟩ := chain_last O.places O.chain
  obtain ⟨hkf, hln⟩ := hz sp hsp
  obtain ⟨hmem, harm2⟩ := places_from_lots hall sp b0 hx
  rcases harm2 with ⟨mk, hmk, -⟩ | ⟨-, L, hL, b', hb', ep, rfl⟩
  · exfalso
    obtain ⟨mk0, h0, -⟩ := road_batch_some hmk
    obtain ⟨-, -, k1, -⟩ := k9_batch_some h0
    rw [hkf] at k1
    cases k1
  · obtain ⟨rfl, eb⟩ := lot_end hL hb' (by rw [ep, hkf]) (by rw [ep, hln])
    have hpl : sp.place = { chain := 1, link := none, piece := 5, kind := .frame } := by
      rw [← ep, eb]
      rfl
    have hla : LaidAlone ProofFile.sameReply c.last b' sp.name
        { chain := 1, link := none, piece := 5, kind := .frame } := by
      rcases harm with h | ⟨l', hl'⟩
      · rw [h4] at h
        exact h
      · exfalso
        have e0 : b'.place.link = some l' := hl'
        rw [ep, hln] at e0
        cases e0
    exact ⟨b', hb', eb, by rw [alone_name hla]; exact hla⟩

/-! ## 6 Their numbers in the flat list -/

/-- By Block.lean's text: block number j behind the links stands in the chain's flat list behind the first block, the front and the links' flat lists, with «and it is bare» laid to its test on the plan. General in the chain. -/
theorem back_at_flat {σ C : Type} {c : Chain σ C} {j : ℕ} {b : Block σ C} (h : c.back[j]? = some b) :
    c.blocksInOrder[(1 + c.front.length) + (c.links.flatMap Link.blocksInOrder).length + j]? =
      some { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := by
  unfold Chain.blocksInOrder
  refine getElem?_append_some ?_ _
  have hA : (1 + c.front.length) + (c.links.flatMap Link.blocksInOrder).length =
      ((({ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } : Block σ C) ::
        c.front.map fun b : Block σ C => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
        c.links.flatMap Link.blocksInOrder).length := by
    rw [List.length_append, List.length_cons, List.length_map, Nat.add_comm 1]
  rw [hA, getElem?_append_add, List.getElem?_map, h]
  rfl

/-- The like for the chain's last block. -/
theorem last_at_flat {σ C : Type} (c : Chain σ C) :
    c.blocksInOrder[(1 + c.front.length) + (c.links.flatMap Link.blocksInOrder).length + c.back.length]? =
      some { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter } := by
  unfold Chain.blocksInOrder
  have hA : (1 + c.front.length) + (c.links.flatMap Link.blocksInOrder).length + c.back.length =
      (((({ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } : Block σ C) ::
        c.front.map fun b : Block σ C => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
        c.links.flatMap Link.blocksInOrder) ++
        c.back.map fun b : Block σ C => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }).length + 0 := by
    rw [List.length_append, List.length_append, List.length_cons, List.length_map, List.length_map,
      Nat.add_comm 1]
    rfl
  rw [hA, getElem?_append_add]
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **In scope the 25 links' flat lists hold 352 blocks**, and nothing stands in the field front. -/
theorem links_flat_352 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    c.front = [] ∧ (c.links.flatMap Link.blocksInOrder).length = 352 := by
  obtain ⟨hfr, hlk⟩ := link_flat_places O.chain
  obtain ⟨Lk, e, hp⟩ := hlk 24 .head (subs_head hS hR O.pub O.blank)
  have h25 := links_25 hS hR O
  have hix := flatIx_scope hS hR O (l := 24) (by decide) 0
  unfold flatIx at hix
  rw [hfr] at hix
  have h16 : Lk.blocksInOrder.length = 16 := by
    rw [← List.length_map (f := (·.place)), hp, linkPlaces_len]
    rfl
  obtain ⟨hl, e'⟩ := List.getElem?_eq_some_iff.1 e
  have hs : c.links = c.links.take 24 ++ Lk :: c.links.drop (24 + 1) := by
    rw [← e', ← List.drop_eq_getElem_cons hl, List.take_append_drop]
  have hd : c.links.drop (24 + 1) = [] := List.drop_eq_nil_of_le (by omega)
  refine ⟨hfr, ?_⟩
  rw [hs, hd, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_append, h16, List.length_nil]
  simp only [List.length_nil] at hix
  omega

/-- **In scope: block number j behind the links is number 353 + j of the flat list; the chain's last block is number 357.** -/
theorem back_numbers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (∀ j b, c.back[j]? = some b → c.blocksInOrder[353 + j]? = some { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ∧
      c.blocksInOrder[357]? = some { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter } := by
  obtain ⟨hfr, h352⟩ := links_flat_352 hS hR O
  obtain ⟨h4, -⟩ := back_of O
  refine ⟨fun j b h => ?_, ?_⟩
  · have := back_at_flat h
    rw [hfr, h352] at this
    exact this
  · have := last_at_flat c
    rw [hfr, h352, h4] at this
    exact this

end

end IM

#print axioms IM.alone_underDressed
#print axioms IM.places_spots
#print axioms IM.k13_in_seat
#print axioms IM.last_at_flat
#print axioms IM.chain_last
#print axioms IM.lot_end
#print axioms IM.seal_of
#print axioms IM.back_at_flat
#print axioms IM.links_flat_352
#print axioms IM.back_numbers
#print axioms IM.base_has_K13
#print axioms IM.lot_K13
#print axioms IM.lot_M4
#print axioms IM.back_of
#print axioms IM.firstChain_back_len
#print axioms IM.chain_back_any
