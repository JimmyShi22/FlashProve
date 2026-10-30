-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameSeat.lean. roleOf (Johnson/Desc/ProofFile/Frames1.lean) goes by equality with the driver's own names: laid_ne_cleared (one inequality of strings, general in the link); role_lay | role_clear hand out the name; clear_block | lay_block ask no «l < 25». LaidOpened Z l … | first_opened | opened_yes: the joined row is the link's own. «Which arm» is paid in Johnson/IMR/SameSpot.lean (opened_joined). Where the text below speaks of a link l', this paragraph holds.
no_frame_hears · address_kind · FrameName stand in Johnson/IMR/DriverWalk.lean (address_kind hands out the link too); shape_frame_names is read off chain_walk; link_lay_clear calls linkAt_shape (Johnson/Desc/First/Link/Law/Shape.lean).

A law about ProofFile.chainBy and ProofFile.pureSeat, no part of them: the link's frame's own blocks in
onlineDescription's first chain: «link l: laid» · «link l: behind the batching» · «link l: cleared» · and
what is joined behind a
link's first place («opened»).
Object. The seated constants: the rows of Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = ok fs (Johnson/Top/H0/Walk/FrameLot.lean; the lot: Johnson/Desc/ProofFile/Lot/Frames.lean: blocksOf; Johnson/Desc/ProofFile/LotCore.lean: frameBlocks): at link l the row f := fs[l]: f.lay
(= layFront l) · f.opened · f.clear, as they reach the fold: through ProofFile.chainBy's record «frames» (lay | clear: «the first block of the role lay l | clear l, at no round») and the driver's guard, as the fields Lk.lay | Lk.clear of the link, which Block.lean's Link.blocksInOrder lays into its
first and last block.
User. The laws of Johnson/Top/H0/Walk/FramePlain.lean (they take «YesOf p.b f.lay» and the like as premises: Johnson/IMR/FrameYes.lean has this folder's seats in these letters) · this folder's files that state their laws in the goals' scope (the record behind «laid» stands at link l).
Letters. As in Johnson/IMR/K6Seat.lean; fs: by framesOf … = ok fs · f: by fs[l]? = some f · bL | bC:
by their numbers in the flat list.

Compiled with the whole library.
The letter o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (by reading, not machine-checked: the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).
Laws on andThen's yes: LawsCompose.lean's step_andThen_inv, at the step; FramePlain.lean's yesBehind_andThen, at YesOf: neither at seatedWith, Johnson/IMR/SeatForm.lean.



  shape_frame_names (FrameName: Johnson/IMR/DriverWalk.lean)   by Block.lean's and the driver's
    texts: in a driver's link a block of the kind «frame» is one of Link.blocksInOrder's own three: piece 0:
    «link l: laid» · piece n + 2: «… : behind the batching» · piece n + 6:
                    «… : cleared»; so the shape's entries of that kind bear these names.
  role_lay | role_clear · beq_lay | beq_clear (and primes)   roleOf's text; FrameRole's derived test of equality.
  frames_idx · frames_at · frames_arms   (over Fo.Pub.mapM_at, OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean) row number i of framesOf is link i's; its «lay» is layFront i; arm by arm (framesOf's text, opened): the head's frame whole; else f.plan | f.opened | f.clear as planLayZero | planAtt | planLay … · openLayZero | openAtt | openLay … · clearWith … at the letters P that zeroAt |
                    frameAt return. Which arm holds at which link is not said.
  clear_block | lay_block   every member of the parts' frames with the role clear l | lay l is
                            guardMark of link l's own row's block, carried over. clear_block
                            concludes that framesOf has returned; lay_block takes it as a premise.
  stepAt · link_lay_clear · bind_same   Lk.lay t = (stepAt frames (.lay l) t).bind (seatSame same t); the like for clear: by chainBy's, the driver's and the guard's texts.
  roles_there · stepAt_some   a seat that lacks nothing (Open.whole) has both roles at every link at which the plan has a place: so chainBy's arm «no block: the record is handed on: yes to all» is not reached.
  laid_in_flat | cleared_in_flat | behind_in_flat   (general in the link; Block.lean's text) the flat list's first | last block has no round and decides as Lk.lay | Lk.clear; number Lk.hear.length + 2 has none and decides as Link.runBehind (the link's tests behind the adding, then the runs
                    behind the batching).
  frame_of          in scope, at secondHashFunction: c has 25 links; framesOf returns fs; at every l < 25: Lk.hear.length = 9 at 24, else 7 · fs[l]? = some f · f.link = l · f.lay = layFront l · Lk.lay s = ok t ↔ f.lay s = ok t ∧ t.failed = none ∧ sameReply s t = true · the like for clear ·
                    c.blocksInOrder[14 l + 1]? = some bL · c.blocksInOrder[14 l + Lk.hear.length + 3]? = some bB · c.blocksInOrder[14 l + Lk.hear.length + 7]? = some bC: three blocks without a round, which decide as Lk.lay | Lk.runBehind | Lk.clear.
  openedOf · behind_block · yes_with · LaidOpened · first_opened · opened_yes   «opened», as far as
    it is typed (under HeadIsTwo Z, Johnson/IMR/CloseSeat.lean, paid in scope): a member of the
    parts' frames with the role «behind l' m» is guardMark of link l''s own row's «opened»; a link's
    first block b
                    bears the name of link l's own spot sp at piece 1 (sp handed out), and is its
                      lot's block alone, or with the «opened» of link l's own row joined; what a yes
                      then holds.
  framed_no_claims  a block at a first place whose lot's block is carried over by Block.retype states no run of claims.

Who pays the premises: as in Johnson/IMR/K6Seat.lean. One run: onlineDescription secondHashFunction returns at VerifierAndGoals.storedPublicFiles's three files, over sources other than those over which this file stands: an evaluation, no theorem; the scope is wider than what was run (it leaves the scale file and some numbers free).
What is not claimed. «opened» is seated in Johnson/IMR/SameSpot.lean (joined_at: at every o, with no premise but the link's sort), not here: first_opened leaves two arms. Which arm of frames_arms holds at which link (but the head's: Johnson/IMR/FirstSeats.lean's frames_head): a law «framesOf_at» on this framesOf is declared nowhere in this library. What the functions decide. No soundness.
-/
import Johnson.IMR.CloseSeat
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt blockAt kindsBeforeBatching addresses hearsReply
  flatPlacesOf linkPlaces closeAddresses closeKinds backKinds frameAt mem_of_mapM)
open OnBytes.L5.LinksOrder (ok_bind)
open ProofFile (Cl)

/-! ## 1 The names at the frame's own places of a link's flat list -/

/-- **The shape's entries of the kind «frame» in a link bear these names.** -/
theorem shape_frame_names {Z : ProofFile.Pub} {shape : List (String × Place)}
    (h : ProofFile.shapeOf Z = .ok shape) {e : String × Place} (he : e ∈ shape) {l : ℕ}
    (hl : e.2.link = some l) (hk : e.2.kind = KindName.frame) :
    ∃ sub, (ProofFile.subsOf Z)[l]? = some sub ∧ FrameName l (kindsBeforeBatching sub (l == 0)).length e := by
  unfold ProofFile.shapeOf at h
  obtain ⟨spots, _, h⟩ := ok_bind h
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
        rcases chain_walk h1 hx with ⟨l', sub, hs, hm⟩ | ⟨b, -, -, hnf, -⟩ | ⟨-, hn⟩
        · rcases hm with ⟨b, -, -, hnf, -⟩ | ⟨mk, g, -, -, ep⟩ | ⟨-, hn⟩
          · exact absurd hk hnf
          · have hk' : x.place.kind = KindName.frame := hk
            rw [ep] at hk'
            cases hk'
          · obtain rfl : l' = l := Option.some.inj (hn.1.symm.trans hl)
            exact ⟨sub, hs, hn⟩
        · exact absurd hk hnf
        · have hl' : x.place.link = some l := hl
          rw [hn] at hl'
          cases hl'

/-! ## 2 The two names by which ProofFile.roleOf tells «laid» from «cleared» are two -/

theorem laid_ne_cleared (s : String) : s ++ ": laid" ≠ s ++ ": cleared" := by
  intro e
  have e2 := congrArg String.toList e
  rw [String.toList_append, String.toList_append] at e2
  have e3 := List.append_cancel_left e2
  exact absurd e3 (by decide)

/-! ## 3 What the roles «lay» and «clear» say -/

theorem role_lay {shape : List (String × Place)} {p : Place} {l : ℕ}
    (h : ProofFile.roleOf shape p = .lay l) :
    ∃ e ∈ shape, e.2.kind = KindName.frame ∧ e.2.piece = p.piece ∧ e.2.link = some l ∧
      p.link = some l ∧ e.1 = s!"link {l}" ++ ": laid" := by
  unfold ProofFile.roleOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h <;> cases h
  · rename_i e l' hf hl
    split at h
    · cases h
    · rename_i hk
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      split at h
      · rename_i he
        cases h
        exact ⟨e, List.mem_of_find?_eq_some hf, by simpa using hk, hp.2, hp.1.2.trans hl, hl,
          by simpa using he⟩
      · split at h <;> cases h

theorem role_clear {shape : List (String × Place)} {p : Place} {l : ℕ}
    (h : ProofFile.roleOf shape p = .clear l) :
    ∃ e ∈ shape, e.2.kind = KindName.frame ∧ e.2.piece = p.piece ∧ e.2.link = some l ∧
      p.link = some l ∧ e.1 = s!"link {l}" ++ ": cleared" := by
  unfold ProofFile.roleOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h <;> cases h
  · rename_i e l' hf hl
    split at h
    · cases h
    · rename_i hk
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      split at h
      · cases h
      · split at h
        · rename_i he
          cases h
          exact ⟨e, List.mem_of_find?_eq_some hf, by simpa using hk, hp.2, hp.1.2.trans hl, hl,
            by simpa using he⟩
        · cases h

/-- FrameRole's derived test of equality, at «lay» and «clear». -/
theorem beq_lay {r : ProofFile.FrameRole} {l : ℕ} (h : (r == ProofFile.FrameRole.lay l) = true) : r = .lay l := by
  cases r with
  | lay a =>
    have h' : (a == l) = true := h
    rw [show a = l by simpa using h']
  | front => exact nomatch h
  | clear _ => exact nomatch h
  | behind _ _ => exact nomatch h
  | common => exact nomatch h
  | stray => exact nomatch h

theorem beq_clear {r : ProofFile.FrameRole} {l : ℕ} (h : (r == ProofFile.FrameRole.clear l) = true) :
    r = .clear l := by
  cases r with
  | clear a =>
    have h' : (a == l) = true := h
    rw [show a = l by simpa using h']
  | front => exact nomatch h
  | lay _ => exact nomatch h
  | behind _ _ => exact nomatch h
  | common => exact nomatch h
  | stray => exact nomatch h

/-! ## 4 The frames' rows, by index -/

/-- **Row number i of framesOf is link i's, and its «lay» is layFront i.** -/
theorem frames_idx {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) (i : ℕ)
    (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (hi : fs[i]? = some f) :
    f.link = i ∧ f.lay = Johnson.Desc.First.Walk.layFront i := by
  unfold Johnson.Desc.First.Walk.Seat.framesOf at h
  obtain ⟨a, ha, e⟩ := Fo.Pub.mapM_at _ _ _ h i f hi
  obtain rfl : i = a := by
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 ha
    simpa using h2
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl⟩
  · split at e
    · rename_i h0
      obtain rfl : i = 0 := by simpa using h0
      split at e
      · cases e
      · cases e
        exact ⟨rfl, rfl⟩
    · split at e
      · cases e
      · cases e
        exact ⟨rfl, rfl⟩
      · cases e
        exact ⟨rfl, rfl⟩

/-- **Row number i of framesOf, arm by arm, as a record**: framesOf's text, opened: for whoever wants f.opened | f.clear as the frame's files' own functions (Johnson/Desc/First/Walk/Frame.lean · FrameZero.lean). WHICH ARM HOLDS AT WHICH LINK IS NOT SAID HERE. -/
theorem frames_arms {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) (i : ℕ)
    (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (hi : fs[i]? = some f) :
    (∃ X, built[i]? = some X ∧ X.kind = 2 ∧
        f = Johnson.Desc.First.Walk.Seat.headFrame (Johnson.Desc.First.Walk.Seat.pubOf X) i first W) ∨
      (i = 0 ∧ ∃ P, Johnson.Desc.First.Walk.Seat.zeroAt built W = some P ∧
        f.plan = Johnson.Desc.First.Walk.planLayZero first.shape P ∧
        f.opened = Johnson.Desc.First.Walk.openLayZero P (Johnson.Desc.First.Walk.Seat.fvsOf built)
          first.lin.kCol ∧
        f.clear = Johnson.Desc.First.Walk.clearWith P.X (Johnson.Desc.First.Walk.countsLay P.tl₀.NM)
          Johnson.Desc.First.Walk.leftLay (Johnson.Desc.First.Walk.Seat.rowOf W first)) ∨
      (∃ P nLin, Johnson.Desc.First.Walk.Seat.frameAt built W i = some (.att P nLin) ∧
        f.plan = Johnson.Desc.First.Walk.planAtt first.shape P ∧
        f.opened = Johnson.Desc.First.Walk.openAtt P ∧
        f.clear = Johnson.Desc.First.Walk.clearWith P.X (Johnson.Desc.First.Walk.countsAtt nLin)
          (fun _ => none) (Johnson.Desc.First.Walk.Seat.rowOf W first)) ∨
      (∃ P, Johnson.Desc.First.Walk.Seat.frameAt built W i = some (.lay P) ∧
        f.plan = Johnson.Desc.First.Walk.planLay first.shape P ∧
        f.opened = Johnson.Desc.First.Walk.openLay P ∧
        f.clear = Johnson.Desc.First.Walk.clearWith P.X (Johnson.Desc.First.Walk.countsLay P.tl₀.NM)
          Johnson.Desc.First.Walk.leftLay (Johnson.Desc.First.Walk.Seat.rowOf W first)) := by
  unfold Johnson.Desc.First.Walk.Seat.framesOf at h
  obtain ⟨a, ha, e⟩ := Fo.Pub.mapM_at _ _ _ h i f hi
  obtain rfl : i = a := by
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 ha
    simpa using h2
  dsimp only at e
  split at e
  · rename_i hk
    split at e
    · cases e
    · rename_i X hX
      cases e
      rw [hX] at hk
      exact Or.inl ⟨X, hX, by simpa using hk, rfl⟩
  · split at e
    · rename_i h0
      obtain rfl : i = 0 := by simpa using h0
      split at e
      · cases e
      · rename_i P hP
        cases e
        exact Or.inr (Or.inl ⟨rfl, P, hP, rfl, rfl, rfl⟩)
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        exact Or.inr (Or.inr (Or.inl ⟨P, nLin, hP, rfl, rfl, rfl⟩))
      · rename_i P hP
        cases e
        exact Or.inr (Or.inr (Or.inr ⟨P, hP, rfl, rfl, rfl⟩))

/-- So a row stands at its own link's number. -/
theorem frames_at {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) :
    ∀ f ∈ fs, fs[f.link]? = some f ∧ f.lay = Johnson.Desc.First.Walk.layFront f.link := by
  intro f hf
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
  obtain ⟨e1, e2⟩ := frames_idx h i f hi
  rw [e1]
  exact ⟨hi, e2⟩

/-! ## 5 Which block of the frames' lot bears which role -/

section
variable {Z : ProofFile.Pub} {B : ProofFile.PureBase}

/-- **The role «clear l» is borne by link l's own row's «clear»**; and framesOf has returned. -/
theorem clear_block (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B) {l : ℕ}
    {x : ProofFile.FrameRole × Block S Cl} (hx : x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames)
    (hr : x.1 = .clear l) :
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧
      x.2 = ProofFile.guardMark (roundlessBlock s!"link {f.link}: clear" 1 (some f.link) f.last f.clear :
              Block S Unit).retype := by
  obtain ⟨-, hsh, -, hall⟩ := base_made hB
  obtain ⟨L, hL, fb', hfb', hkf, er, e2⟩ := frames_from_lots hall hx
  obtain ⟨e, he, hke, hpe, hle, hlk, hend⟩ := role_clear (er.symm.trans hr)
  obtain ⟨fb, hfb, rfl⟩ := frame_from hL hfb' hkf hlk
  obtain ⟨sub, -, -, hn⟩ := shape_frame_names hsh he hle hke
  have hpl : (fb.retype : Block S Cl).place = fb.place := rfl
  rw [hpl] at hpe hlk
  have hlen := hear_len sub (l == 0)
  -- piece 0 bears the name «… : laid», which ends in «: laid»
  have h0 : e.2.piece ≠ 0 := by
    intro h0
    rcases hn with ⟨-, en⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
    · exact laid_ne_cleared _ (en.symm.trans hend)
    · omega
    · omega
  unfold P1L20.blocksOf at hfb
  split at hfb
  · rename_i fs hfs
    obtain ⟨f, hf, h⟩ := List.mem_flatMap.1 hfb
    obtain ⟨hat, -⟩ := frames_at hfs f hf
    unfold ProofFile.frameBlocks at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact absurd hpe h0
    · exfalso
      have h1 : e.2.piece = 1 := hpe
      rcases hn with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ <;> omega
    · have el : f.link = l := by
        have e' : (some f.link : Option ℕ) = some l := hlk
        exact Option.some.inj e'
      exact ⟨fs, f, hfs, el ▸ hat, e2⟩
  · obtain rfl := List.mem_singleton.1 hfb
    exact absurd hpe h0

/-- **The role «lay l» is borne by a block of piece 0 at link l**: link l's own row's «lay» where framesOf has returned. -/
theorem lay_block (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B) {l : ℕ}
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    {x : ProofFile.FrameRole × Block S Cl} (hx : x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames)
    (hr : x.1 = .lay l) :
    ∃ f, fs[l]? = some f ∧
      x.2 = ProofFile.guardMark (roundlessBlock s!"link {f.link}: lay" 1 (some f.link) 0 f.lay :
              Block S Unit).retype := by
  obtain ⟨-, hsh, -, hall⟩ := base_made hB
  obtain ⟨L, hL, fb', hfb', hkf, er, e2⟩ := frames_from_lots hall hx
  obtain ⟨e, he, hke, hpe, hle, hlk, hend⟩ := role_lay (er.symm.trans hr)
  obtain ⟨fb, hfb, rfl⟩ := frame_from hL hfb' hkf hlk
  obtain ⟨sub, -, -, hn⟩ := shape_frame_names hsh he hle hke
  have hpl : (fb.retype : Block S Cl).place = fb.place := rfl
  rw [hpl] at hpe hlk
  have hlen := hear_len sub (l == 0)
  unfold P1L20.blocksOf at hfb
  rw [hfs] at hfb
  obtain ⟨f, hf, h⟩ := List.mem_flatMap.1 hfb
  obtain ⟨hat, -⟩ := frames_at hfs f hf
  have hlast := frames_last hfs f hf
  unfold ProofFile.frameBlocks at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · have el : f.link = l := by
      have e' : (some f.link : Option ℕ) = some l := hlk
      exact Option.some.inj e'
    exact ⟨f, el ▸ hat, e2⟩
  · exfalso
    have h1 : e.2.piece = 1 := hpe
    rcases hn with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ <;> omega
  · exfalso
    have h1 : e.2.piece = f.last := hpe
    rcases hn with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, en⟩
    · rcases hlast with h | h <;> omega
    · rcases hlast with h | h <;> omega
    · exact laid_ne_cleared _ (hend.symm.trans en)

end

/-! ## 6 A link's «lay» and «clear», by chainBy's, the driver's and the guard's texts -/

/-- The step that chainBy lays for a role: the first block of that role, at no round; where there is none: the record handed on. -/
def stepAt (fr : List (ProofFile.FrameRole × Block S Cl)) (r : ProofFile.FrameRole) (t : S) : Except String S :=
  match (fr.find? fun x => x.1 == r).map fun x => x.2 with
  | some b => b.decide t [] []
  | none => .ok t

theorem link_lay_clear {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl}
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) (l : ℕ)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) :
    ∃ Lk : Link S Cl, c.links[l]? = some Lk ∧
      (∀ t, Lk.lay t = (stepAt (ProofFile.partsAt T B).frames (.lay l) t).bind
        (VerifiableInference.Desc.seatSame T.same t)) ∧
      (∀ t, Lk.clear t = (stepAt (ProofFile.partsAt T B).frames (.clear l) t).bind
        (VerifiableInference.Desc.seatSame T.same t)) := by
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
        obtain ⟨Lk, hLk, eLk⟩ := firstChain_link h1 l sub hl
        obtain ⟨-, -, -, -, -, -, -, -, hlay, hclear⟩ := VerifiableInference.Desc.Shape.linkAt_shape hLk
        refine ⟨_, eLk, fun t => ?_, fun t => ?_⟩
        · unfold stepAt
          dsimp only [Link.guarded]
          rw [hlay]
          dsimp only [ProofFile.fill]
          generalize List.find? (fun x => x.1 == ProofFile.FrameRole.lay l) (ProofFile.partsAt T B).frames = w
          cases w <;> rfl
        · unfold stepAt
          dsimp only [Link.guarded]
          rw [hclear]
          dsimp only [ProofFile.fill]
          generalize List.find? (fun x => x.1 == ProofFile.FrameRole.clear l) (ProofFile.partsAt T B).frames = w
          cases w <;> rfl

/-- A yes behind the guard's test on the reply. -/
theorem bind_same {same : S → S → Bool} {x : Except String S} {s t : S} :
    x.bind (VerifiableInference.Desc.seatSame same s) = .ok t ↔ x = .ok t ∧ same s t = true := by
  constructor
  · intro h
    cases x with
    | error e => cases h
    | ok u =>
      obtain ⟨rfl, e'⟩ := VerifiableInference.Desc.seatSame_ok (show
        VerifiableInference.Desc.seatSame same s u = .ok t from h)
      exact ⟨rfl, e'⟩
  · rintro ⟨rfl, e⟩
    show VerifiableInference.Desc.seatSame same s t = .ok t
    unfold VerifiableInference.Desc.seatSame
    rw [e]
    rfl

/-! ## 7 A seat that lacks nothing has both roles at every link of the plan -/

theorem beq_lay' {r : ProofFile.FrameRole} {l : ℕ} (h : (ProofFile.FrameRole.lay l == r) = true) : r = .lay l := by
  cases r with
  | lay a =>
    have h' : (l == a) = true := h
    rw [show l = a by simpa using h']
  | front => exact nomatch h
  | clear _ => exact nomatch h
  | behind _ _ => exact nomatch h
  | common => exact nomatch h
  | stray => exact nomatch h

theorem beq_clear' {r : ProofFile.FrameRole} {l : ℕ} (h : (ProofFile.FrameRole.clear l == r) = true) :
    r = .clear l := by
  cases r with
  | clear a =>
    have h' : (l == a) = true := h
    rw [show l = a by simpa using h']
  | front => exact nomatch h
  | lay _ => exact nomatch h
  | behind _ _ => exact nomatch h
  | common => exact nomatch h
  | stray => exact nomatch h

theorem ite_nil {c : Bool} {s : String} (h : (if c = true then [] else [s]) = ([] : List String)) :
    c = true := by
  cases c with
  | true => rfl
  | false => cases h

/-- **lackingAt's two asks «laid» and «cleared»**, at a link at which the plan has a place. -/
theorem roles_there {T : ProofFile.PureSeat} {P : ProofFile.PureParts} (hw : ProofFile.lackingAt T P = [])
    {sp : ProofFile.Spot} {y : Except String (Block S Cl)} (hm : (sp, y) ∈ P.places) {l : ℕ}
    (hl : sp.place.link = some l) :
    (∃ x ∈ P.frames, x.1 = ProofFile.FrameRole.lay l) ∧ ∃ x ∈ P.frames, x.1 = ProofFile.FrameRole.clear l := by
  unfold ProofFile.lackingAt at hw
  dsimp only at hw
  simp only [List.append_eq_nil_iff] at hw
  obtain ⟨⟨⟨-, hfr⟩, -⟩, -⟩ := hw
  have hmem : l ∈ (P.places.filterMap fun x => x.1.place.link).eraseDups :=
    List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨(sp, y), hm, hl⟩)
  have h1 := List.flatMap_eq_nil_iff.1 hfr l hmem
  simp only [List.append_eq_nil_iff] at h1
  obtain ⟨⟨⟨⟨⟨ha, -⟩, hc⟩, -⟩, -⟩, -⟩ := h1
  have ha' := ite_nil ha
  have hc' := ite_nil hc
  rw [List.contains_eq_any_beq, List.any_eq_true] at ha' hc'
  obtain ⟨r, hr, e⟩ := ha'
  obtain ⟨r', hr', e'⟩ := hc'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hr'
  exact ⟨⟨x, hx, beq_lay' e⟩, ⟨x', hx', beq_clear' e'⟩⟩

/-- Where a block of a role is there, chainBy's step for the role is the decision, at no round, of a block of that role. -/
theorem stepAt_some {fr : List (ProofFile.FrameRole × Block S Cl)} {r : ProofFile.FrameRole}
    (hrefl : (r == r) = true) (hinv : ∀ r', (r' == r) = true → r' = r) (h : ∃ x ∈ fr, x.1 = r) :
    ∃ x ∈ fr, x.1 = r ∧ ∀ t, stepAt fr r t = x.2.decide t [] [] := by
  obtain ⟨x, hx, e⟩ := h
  cases hf : fr.find? (fun x => x.1 == r) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    rw [e, hrefl] at this
    exact absurd rfl this
  | some x0 =>
    have hp : (x0.1 == r) = true :=
      List.find?_some (p := fun x : ProofFile.FrameRole × Block S Cl => x.1 == r) hf
    refine ⟨x0, List.mem_of_find?_eq_some hf, hinv _ hp, fun t => ?_⟩
    unfold stepAt
    rw [hf]
    rfl

/-! ## 8 «laid» and «cleared» at every link, in the goals' scope -/

/-- By Block.lean's text: a link's flat list begins with «laid», whose decision is the link's lay, and ends with «cleared», whose decision is its clear. General in the link. -/
theorem laid_in_flat {σ C : Type} (Lk : Link σ C) :
    ∃ b, Lk.blocksInOrder[0]? = some b ∧ b.rounds = [] ∧ ∀ s rs gs, b.decide s rs gs = Lk.lay s :=
  ⟨_, rfl, rfl, fun _ _ _ => rfl⟩

theorem cleared_in_flat {σ C : Type} (Lk : Link σ C) :
    ∃ b, Lk.blocksInOrder[Lk.blocksInOrder.length - 1]? = some b ∧ b.rounds = [] ∧
      ∀ s rs gs, b.decide s rs gs = Lk.clear s := by
  refine ⟨roundlessBlock (Lk.name ++ ": cleared") Lk.chain (some Lk.number)
    (Lk.hear.length + Lk.close.length + 3) Lk.clear, ?_, rfl, fun _ _ _ => rfl⟩
  unfold Link.blocksInOrder
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.getElem?_concat_length]

/-- By Block.lean's text: behind the batching stands the frame's own block without a round, whose decision is Link.runBehind: the link's tests behind the adding, then the runs behind the batching in the link's order. General in the link. -/
theorem behind_in_flat {σ C : Type} (Lk : Link σ C) :
    ∃ b, Lk.blocksInOrder[Lk.hear.length + 2]? = some b ∧ b.rounds = [] ∧
      ∀ s rs gs, b.decide s rs gs = Lk.runBehind s := by
  refine ⟨roundlessBlock (Lk.name ++ ": behind the batching") Lk.chain (some Lk.number)
    (Lk.hear.length + 2) Lk.runBehind, ?_, rfl, fun _ _ _ => rfl⟩
  unfold Link.blocksInOrder
  refine getElem?_append_some (getElem?_append_some ?_ _) _
  have e : Lk.hear.length + 2 = (({ roundlessBlock (Lk.name ++ ": laid") Lk.chain (some Lk.number) 0 Lk.lay with
      planOk := VerifiableInference.Desc.orderOk Lk.hear Lk.order &&
        VerifiableInference.Desc.orderAfterOk Lk.hear Lk.orderAfter && Lk.close.all Block.hasNoClaimsAndNothingAfter &&
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)).hasNoClaimsAndNothingAfter } :
      Block σ C) :: Lk.hear).length + 1 := by
    rw [List.length_cons]
  rw [e, getElem?_append_add]
  rfl

theorem hear_len_at (l : ℕ) : (kindsBeforeBatching (subAt l) (l == 0)).length = if l = 24 then 9 else 7 := by
  unfold subAt
  by_cases h24 : l = 24
  · subst h24
    rfl
  · rw [if_neg h24, if_neg h24]
    by_cases he : l % 2 = 0
    · rw [if_pos he]
      cases (l == 0) <;> rfl
    · rw [if_neg he]
      cases (l == 0) <;> rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE FRAME's «laid» AND «cleared» AT EACH OF THE 25 LINKS, IN SCOPE: THE LINK's lay | clear SAY YES JUST WHERE LINK l's OWN ROW OF framesOf DOES, with no mark behind it and the reply as it was; AND THEY, AND Link.runBehind, ARE WHAT THE FOLD RUNS,
in blocks without a round at named numbers of the flat list.** -/
theorem frame_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    c.links.length = 25 ∧
    ∃ fs, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
    ∀ l < 25, ∃ (Lk : Link S Cl) (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (bL bB bC : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear.length = (if l = 24 then 9 else 7) ∧ fs[l]? = some f ∧
      f.link = l ∧ f.lay = Johnson.Desc.First.Walk.layFront l ∧
      (∀ s t, Lk.lay s = .ok t ↔ f.lay s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true) ∧
      (∀ s t, Lk.clear s = .ok t ↔ f.clear s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true) ∧
      c.blocksInOrder[14 * l + 1]? = some bL ∧ bL.rounds = [] ∧ (∀ s rs gs, bL.decide s rs gs = Lk.lay s) ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 3]? = some bB ∧ bB.rounds = [] ∧
      (∀ s rs gs, bB.decide s rs gs = Lk.runBehind s) ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 7]? = some bC ∧ bC.rounds = [] ∧
      (∀ s rs gs, bC.decide s rs gs = Lk.clear s) := by
  refine ⟨links_25 hS hR O, ?_⟩
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  -- at each link: a place of the plan, hence both roles
  have roles : ∀ l < 25, (∃ x ∈ (ProofFile.partsAt (ProofFile.pureSeat OnBytes.secondHashFunction Z) Bs).frames,
      x.1 = ProofFile.FrameRole.lay l) ∧ ∃ x ∈ (ProofFile.partsAt (ProofFile.pureSeat OnBytes.secondHashFunction Z) Bs).frames,
      x.1 = ProofFile.FrameRole.clear l := by
    intro l hl
    obtain ⟨Lk, b, sp, b0, -, -, hx, hpl, -⟩ :=
      chain_close O.places O.chain l (subAt l) (subs_scope hS hR O l hl) 1 .K10 rfl
    obtain ⟨-, harm⟩ := places_from_lots hall sp b0 hx
    refine roles_there O.whole hx ?_
    rcases harm with ⟨mk, hmk, rfl⟩ | ⟨-, L, -, b', -, ep, rfl⟩
    · exfalso
      have hk := face_kind (makers_K9 Z Bs.G₀) hmk (fun s => .ok ([], s))
      rw [hpl] at hk
      cases hk
    · have e : b'.place = cAt l (subAt l) 1 .K10 := hpl
      rw [← ep, e]
  obtain ⟨-, x0, hx0, hr0⟩ := roles 0 (by decide)
  obtain ⟨fs, -, hfs, -, -⟩ := clear_block O.made hx0 hr0
  refine ⟨fs, hfs, fun l hl => ?_⟩
  obtain ⟨hlay, hclear⟩ := roles l hl
  obtain ⟨Lk, e1, hL, hC⟩ := link_lay_clear O.chain l (subAt l) (subs_scope hS hR O l hl)
  obtain ⟨xl, hxl, rl, sl⟩ := stepAt_some (r := .lay l) (by show (l == l) = true; simp)
    (fun _ h => beq_lay h) hlay
  obtain ⟨xc, hxc, rc, sc⟩ := stepAt_some (r := .clear l) (by show (l == l) = true; simp)
    (fun _ h => beq_clear h) hclear
  obtain ⟨f, hf, el⟩ := lay_block O.made hfs hxl rl
  obtain ⟨fs', f', hfs', hf', ec⟩ := clear_block O.made hxc rc
  obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
  obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
  obtain ⟨hlink, hlayf⟩ := frames_idx hfs l f hf
  obtain ⟨bL, hbL, rL, dL⟩ := laid_in_flat Lk
  obtain ⟨bB, hbB, rB, dB⟩ := behind_in_flat Lk
  obtain ⟨bC, hbC, rC, dC⟩ := cleared_in_flat Lk
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
  refine ⟨Lk, f, bL, bB, bC, e1, hn8.trans (hear_len_at l), hf, hlink, hlayf, fun s t => ?_,
    fun s t => ?_, ?_, rL, dL, ?_, rB, dB, ?_, rC, dC⟩
  · rw [hL, bind_same, sl, el]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := (guardMark_yes _ s t [] []).1 h1
      exact ⟨h3, h4, h2⟩
    · rintro ⟨h3, h4, h2⟩
      exact ⟨(guardMark_yes _ s t [] []).2 ⟨h3, h4⟩, h2⟩
  · rw [hC, bind_same, sc, ec]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := (guardMark_yes _ s t [] []).1 h1
      exact ⟨h3, h4, h2⟩
    · rintro ⟨h3, h4, h2⟩
      exact ⟨(guardMark_yes _ s t [] []).2 ⟨h3, h4⟩, h2⟩
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

/-! ## 10 «opened»: what is joined behind a link's first place -/

/-- A row's «opened», as the frames' lot lays it (Johnson/Desc/ProofFile/LotCore.lean: frameBlocks' second). -/
def openedOf (f : Johnson.Desc.First.Walk.Seat.LinkFrame) : Block S Unit :=
  { roundlessBlock s!"link {f.link}: opened" 1 (some f.link) 1 f.opened with planOk := f.plan }

/-- **The role «behind l m» is borne by link l's own row's «opened».** (The walk is behind_first's, Johnson/IMR/CloseSeat.lean, which hands out the spot and not the block.) -/
theorem behind_block {Z : ProofFile.Pub} {B : ProofFile.PureBase}
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B) (hk : HeadIsTwo Z)
    {x : ProofFile.FrameRole × Block S Cl} (hx : x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames) {l : ℕ}
    {m : String} (hr : x.1 = .behind l m) :
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ x.2 = ProofFile.guardMark (openedOf f).retype := by
  obtain ⟨-, hsh, -, hall⟩ := base_made hB
  obtain ⟨L, hL, fb', hfb', hkf, er, e2⟩ := frames_from_lots hall hx
  obtain ⟨e, he, rfl, hke, hpe, hle, hlk⟩ := role_behind_link (er.symm.trans hr)
  obtain ⟨fb, hfb, rfl⟩ := frame_from hL hfb' hkf hlk
  obtain ⟨several, hpls⟩ := shape_places hsh
  have hmem : e.2 ∈ flatPlacesOf (ProofFile.subsOf Z) several := by
    rw [← hpls]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨sub, hsub, hin⟩ := flat_in_link hmem hle
  have hpl : (fb.retype : Block S Cl).place = fb.place := rfl
  rw [hpl] at hpe hlk
  unfold P1L20.blocksOf at hfb
  split at hfb
  · rename_i fs hfs
    obtain ⟨f, hf, h⟩ := List.mem_flatMap.1 hfb
    obtain ⟨X, hX, hlast⟩ := frames_row hfs f hf
    obtain ⟨hat, -⟩ := frames_at hfs f hf
    unfold ProofFile.frameBlocks at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact absurd (link_frame_pieces l sub e.2 hin (Or.inl hpe)) hke
    · have el : f.link = l := by
        have e' : (some f.link : Option ℕ) = some l := hlk
        exact Option.some.inj e'
      exact ⟨fs, f, hfs, el ▸ hat, e2⟩
    · exfalso
      have el : f.link = l := by
        have e' : (some f.link : Option ℕ) = some l := hlk
        exact Option.some.inj e'
      subst el
      have es : sub = ProofFile.subOf X.kind := by
        unfold ProofFile.subsOf at hsub
        rw [List.getElem?_map, Array.getElem?_toList, hX] at hsub
        exact (Option.some.inj hsub).symm
      have hpe' : e.2.piece = f.last := hpe
      refine hke (link_frame_pieces f.link sub e.2 hin (Or.inr ?_))
      rw [hpe', hlast, es]
      by_cases h2 : (X.kind == 2) = true
      · have e2 : X.kind = 2 := by simpa using h2
        rw [if_pos h2, e2]
        cases (f.link == 0) <;> rfl
      · rw [if_neg h2]
        have hne : ProofFile.subOf X.kind ≠ ModelPart.head := fun hh => h2 (by simpa using hk _ X hX hh)
        cases hs' : ProofFile.subOf X.kind with
        | head => exact absurd hs' hne
        | layers => cases (f.link == 0) <;> rfl
        | attention => cases (f.link == 0) <;> rfl
  · obtain rfl := List.mem_singleton.1 hfb
    exact absurd (link_frame_pieces l sub e.2 hin (Or.inl hpe)) hke

/-- A yes of a block with q joined behind: the lot's block's yes at the front of the rounds and groups, no mark behind it, then q's yes from that record on, the reply as it was. (yes_laid's second arm, Johnson/IMR/SeatForm.lean, AT THE q THAT IS NAMED.) -/
theorem yes_with {same : S → S → Bool} {b b' q : Block S Cl} {name : String} {a : Place}
    (h : b = seatedWith same b' q name a) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    ∃ t', b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok t' ∧ t'.failed = none ∧
      q.decide t' (rs.drop b'.rounds.length) (gs.drop b'.openings) = .ok t ∧ same t' t = true := by
  subst h
  have hy1 := VerifiableInference.Desc.guarded_under same hearsReply
    { (marked b' name).andThen name (q.guarded same fun _ => false) with place := a } s rs gs t hy
  have hy' : ((ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings)).bind
      (fun s' => (q.guarded same fun _ => false).decide s' (rs.drop b'.rounds.length)
        (gs.drop b'.openings)) = .ok t := hy1
  cases hd : (ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings) with
  | error e =>
    rw [hd] at hy'
    cases hy'
  | ok u =>
    rw [hd] at hy'
    obtain ⟨h1, h2⟩ := (guardMark_yes b' s u _ _).1 hd
    obtain ⟨h3, h4⟩ := (VerifiableInference.Desc.guarded_yes same (fun _ => false) q rfl u _ _ t).1 hy'
    exact ⟨u, h1, h2, h3, h4⟩

/-- Alone, or with THE «opened» OF LINK l's OWN ROW OF framesOf joined. -/
def LaidOpened (Z : ProofFile.Pub) (l : ℕ) (b b' : Block S Cl) (a : Place) : Prop :=
  LaidAlone ProofFile.sameReply b b' b.name a ∨
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ b = seatedWith ProofFile.sameReply b' (ProofFile.guardMark (openedOf f).retype) b.name a

/-- **A LINK's FIRST PLACE, AS FAR AS IT IS TYPED**: the block bears the name of link l's own spot sp at piece 1; it is the lot's block alone, or with the «opened» OF LINK l's OWN ROW joined (chainBy joins by the link's number and the name). WHICH ARM: the second, always: Johnson/IMR/SameSpot.lean's joined_at. -/
theorem first_opened {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) (l : ℕ)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[0]? = some k) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
      (∃ sp ∈ Bs.spots, sp.place = { chain := 1, link := some l, piece := 0 + 1, kind := k } ∧
        b.name = sp.name) ∧
      ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks Bs.G₀,
        b'.place = { chain := 1, link := some l, piece := 0 + 1, kind := k } ∧
        LaidOpened Z l b b' { chain := 1, link := some l, piece := 0 + 1, kind := k } := by
  have hk9 : k ≠ KindName.K9 := by
    rintro rfl
    revert hk
    cases sub <;> cases (l == 0) <;> decide
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, harm⟩ :=
    chain_hear hall (makers_K9 Z Bs.G₀) O.places O.chain l sub hl 0 k hk hk9
  have hname : b.name = sp.name := by
    rcases harm with ⟨h, -⟩ | ⟨x, -, -, h⟩
    · exact alone_name h
    · rw [h]
      rfl
  refine ⟨Lk, b, e1, e2, ⟨sp, hsp, es, hname⟩, L, hL, b', hb', ep, ?_⟩
  rcases harm with ⟨h, -⟩ | ⟨x, hx, hr, h⟩
  · left
    rw [alone_name h]
    exact h
  · right
    obtain ⟨fs, f, hfs, hf, ex⟩ := behind_block O.made hk2 hx hr
    rw [ex] at h
    exact ⟨fs, f, hfs, hf, by rw [hname]; exact h⟩

/-- **What a yes at a first place holds**: the lot's block's yes; and, where something is joined: the «opened» of link l's own row says yes from that record on. -/
theorem opened_yes {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place}
    (h : LaidOpened Z l b b' a) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    (b'.decide s rs gs = .ok t ∧ t.failed = none) ∨
      ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
          (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S),
        Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
        fs[l]? = some f ∧
        b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok m ∧ m.failed = none ∧
        f.opened m = .ok t ∧ t.failed = none ∧ ProofFile.sameReply m t = true := by
  rcases h with h | ⟨fs, f, hfs, hf, h⟩
  · left
    rcases yes_laid (Or.inl h) hy with ⟨-, h1, h2⟩ | ⟨q, t', hq, -⟩
    · exact ⟨h1, h2⟩
    · exact ⟨(alone_underR h).2 s rs gs t hy, by
        have hy' := hy
        rw [show b = seatedAs ProofFile.sameReply b' b.name a from h] at hy'
        exact ((guardMark_yes b' s t rs gs).1 (VerifiableInference.Desc.guarded_under ProofFile.sameReply
          hearsReply { marked b' b.name with place := a } s rs gs t hy')).2⟩
  · right
    obtain ⟨m, h1, h2, h3, h4⟩ := yes_with h hy
    obtain ⟨h5, h6⟩ := (guardMark_yes _ m t _ _).1 h3
    exact ⟨fs, f, m, hfs, hf, h1, h2, h5, h6, h4⟩

/-- **A block at a link's first place whose lot's block is carried over by Block.retype states no run of claims** (retype strikes them; the frames' blocks have none). -/
theorem framed_no_claims {Z : ProofFile.Pub} {b : Block S Cl} {x : Block S Unit} {name : String} {a : Place}
    (h : LaidFramed Z b x.retype name a) : b.claims = [] := by
  rcases h with h | ⟨fb, -, h⟩ <;> subst h <;> rfl

end IM

#print axioms IM.behind_in_flat
#print axioms IM.behind_block
#print axioms IM.first_opened
#print axioms IM.opened_yes
#print axioms IM.framed_no_claims
#print axioms IM.frames_arms
#print axioms IM.roles_there
#print axioms IM.frame_of
#print axioms IM.clear_block
#print axioms IM.lay_block
#print axioms IM.link_lay_clear
#print axioms IM.bind_same
#print axioms IM.laid_ne_cleared
#print axioms IM.role_lay
#print axioms IM.beq_lay
#print axioms IM.frames_idx
#print axioms IM.frames_at
#print axioms IM.shape_frame_names
