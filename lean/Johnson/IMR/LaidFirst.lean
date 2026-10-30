-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/LaidFirst.lean:
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: at a place in front of
a link's batching whose piece is 2 to 9 NOTHING IS JOINED BEHIND THE LOT's BLOCK: LaidAlone
(Johnson/IMR/SeatForm.lean).
THE WALK THROUGH THE FLAT LIST IS Johnson/IMR/DriverWalk.lean's:
chainC_flat is read off chain_walk. This head's paths are turned by program.
OBJECT. ProofFile.chainBy's joining (Johnson/Desc/ProofFile/Frames1.lean) at onlineDescription's seat ProofFile.pureSeat o Z: the parts' frames (partsAt), their roles (roleOf, off shapeOf),
the spots' names (Johnson/Desc/ProofFile/Places.lean: spotsFrom), the frames' lot's pieces
(Johnson/Desc/ProofFile/Lot/Frames.lean; Johnson/Top/H0/Walk/FrameLot.lean: framesOf).
LETTERS. Z · B: baseOf's record · sp: a spot · x: a member of the parts' frames.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o;
WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o:
for these the in-scope halves are still owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

WHY. chainBy joins a block of a frame's place behind a place's block where a block of the kind «frame» of a lot has the role «behind l ‹that place's name›».
With a block joined, the record behind the chain's block is not the record behind the lot's block.

  name_ne | name_ne_eq | name_ne_shut   a name ‹head›:‹n› with n = 2 … 9 is no name ‹head'›:‹m› with m = 0, 1, 11, 13, 15, and none that ends in «.equation» | «.shut»
                    (by the last two characters).
  spot_name         a spot's name is ‹head›:‹n› and its piece is n, at K10 n + 2; or it is one of K9's two places without a round, ‹head›:‹n›.equation | .shut.
  chainC_flat       every block of the driver's chain, at a filling without a maker of a batching, that is of a kind (not «frame») stems from the list of blocks
                    that chainC was handed, name and place.
  frames_from_lots · shape_spot · role_behind   partsAt's text; the shape's entries of a kind are the spots'; what the role «behind» says.
  frames_last · frame_piece   a block of the kind «frame» of a lot of ProofFile.onlineFirstChainBlockTables stands behind the links or at piece 0, 1, 13 or 15.
  no_behind         so no block of a frame's place has the role «behind» a spot of piece 2 … 9 that is neither K9's nor K10's.
  chain_hear_alone  chain_hear (Johnson/IMR/PureChain.lean) at such an address, at onlineDescription's seat,
                    with LaidAlone outright.

What is not claimed. Nothing at piece 1 (behind a link's first place the frames' «opened» IS joined). Nothing on the batching, on the closing. No soundness.
-/
import Johnson.IMR.LotKinds
import Johnson.IMR.DriverWalk

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt blockAt kindsBeforeBatching addresses hearsReply mem_of_mapM)
open OnBytes.L5.LinksOrder (ok_bind)
open ProofFile (Cl)

/-! ## 1 Names -/

theorem colon_list : (":" : String).toList = [':'] := rfl

theorem tail_one (x d : String) (c : Char) (hd : d.toList = [c]) :
    (x ++ ":" ++ d).toList.reverse.take 2 = [c, ':'] := by
  rw [String.toList_append, String.toList_append, hd, colon_list]
  simp

theorem tail_two (x d : String) (c c' : Char) (hd : d.toList = [c', c]) :
    (x ++ ":" ++ d).toList.reverse.take 2 = [c, c'] := by
  rw [String.toList_append, String.toList_append, hd, colon_list]
  simp

theorem tail_eq (x : String) : (x ++ ".equation").toList.reverse.take 2 = ['n', 'o'] := by
  have e : (".equation" : String).toList = ['.', 'e', 'q', 'u', 'a', 't', 'i', 'o', 'n'] := rfl
  rw [String.toList_append, e]
  simp

theorem tail_shut (x : String) : (x ++ ".shut").toList.reverse.take 2 = ['t', 'u'] := by
  have e : (".shut" : String).toList = ['.', 's', 'h', 'u', 't'] := rfl
  rw [String.toList_append, e]
  simp

/-- The last two characters of a name ‹head›:‹n›, n = 2 … 9. -/
theorem tail_digit (h : String) {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 9) :
    ∃ c, (c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9') ∧
      (s!"{h}:{n}").toList.reverse.take 2 = [c, ':'] := by
  obtain ⟨h1, h2⟩ := hn
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨'2', by simp, tail_one h _ '2' rfl⟩
  · exact ⟨'3', by simp, tail_one h _ '3' rfl⟩
  · exact ⟨'4', by simp, tail_one h _ '4' rfl⟩
  · exact ⟨'5', by simp, tail_one h _ '5' rfl⟩
  · exact ⟨'6', by simp, tail_one h _ '6' rfl⟩
  · exact ⟨'7', by simp, tail_one h _ '7' rfl⟩
  · exact ⟨'8', by simp, tail_one h _ '8' rfl⟩
  · exact ⟨'9', by simp, tail_one h _ '9' rfl⟩

/-- A place's name with a count 2 to 9 is no name with a count 0, 1, 11, 13, 15. -/
theorem name_ne (h h' : String) {n m : ℕ} (hn : 2 ≤ n ∧ n ≤ 9)
    (hm : m = 0 ∨ m = 1 ∨ m = 11 ∨ m = 13 ∨ m = 15) : s!"{h}:{n}" ≠ s!"{h'}:{m}" := by
  intro e
  have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
  dsimp only at e2
  obtain ⟨c, hc, eL⟩ := tail_digit h hn
  rw [eL] at e2
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · have e3 : [c, ':'] = ['0', ':'] := e2.trans (tail_one h' _ '0' rfl)
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at e3
  · have e3 : [c, ':'] = ['1', ':'] := e2.trans (tail_one h' _ '1' rfl)
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at e3
  · have e3 : [c, ':'] = ['1', '1'] := e2.trans (tail_two h' _ '1' '1' rfl)
    simp at e3
  · have e3 : [c, ':'] = ['3', '1'] := e2.trans (tail_two h' _ '3' '1' rfl)
    simp at e3
  · have e3 : [c, ':'] = ['5', '1'] := e2.trans (tail_two h' _ '5' '1' rfl)
    simp at e3

theorem name_ne_eq (h h' : String) {n m : ℕ} (hn : 2 ≤ n ∧ n ≤ 9) :
    s!"{h}:{n}" ≠ s!"{h'}:{m}.equation" := by
  intro e
  have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
  dsimp only at e2
  obtain ⟨c, hc, eL⟩ := tail_digit h hn
  rw [eL] at e2
  have e3 : [c, ':'] = ['n', 'o'] := e2.trans (tail_eq _)
  simp at e3

theorem name_ne_shut (h h' : String) {n m : ℕ} (hn : 2 ≤ n ∧ n ≤ 9) :
    s!"{h}:{n}" ≠ s!"{h'}:{m}.shut" := by
  intro e
  have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
  dsimp only at e2
  obtain ⟨c, hc, eL⟩ := tail_digit h hn
  rw [eL] at e2
  have e3 : [c, ':'] = ['t', 'u'] := e2.trans (tail_shut _)
  simp at e3

/-- A spot's name is its head and its count; its piece is the count, at K10 two more; or it is one of K9's two places without a round. -/
theorem spot_name : ∀ (gs : List (List VerifiableInference.Desc.First.Cut)) (link piece : ℕ)
    (last : String) (l : List ProofFile.Spot), ProofFile.spotsFrom gs link piece last = some l →
    ∀ p ∈ l, ∃ (h : String) (n : ℕ),
      (p.name = s!"{h}:{n}" ∧ p.place.piece = if p.place.kind == KindName.K10 then n + 2 else n) ∨
      (p.place.kind = KindName.K9 ∧ (p.name = s!"{h}:{n}.equation" ∨ p.name = s!"{h}:{n}.shut"))
  | [], _, _, _, l, h, p, hp => by
    unfold ProofFile.spotsFrom at h
    obtain rfl := Option.some.inj h
    cases hp
  | [] :: gs, link, piece, last, l, h, p, hp => by
    unfold ProofFile.spotsFrom at h
    exact spot_name gs link piece last l h p hp
  | (c :: g) :: gs, link, piece, last, l, h, p, hp => by
    unfold ProofFile.spotsFrom at h
    dsimp only at h
    obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 h
    split at hp
    · rename_i hk
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | rfl | hp
      · exact ⟨_, _, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      · refine ⟨_, _, Or.inl ⟨rfl, ?_⟩⟩
        dsimp only
        rw [if_pos hk]
      · exact ⟨_, _, Or.inr ⟨rfl, Or.inr rfl⟩⟩
      · exact spot_name gs _ _ _ l' hl' p hp
    · rename_i hk
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨_, _, Or.inl ⟨rfl, ?_⟩⟩
        dsimp only
        rw [if_neg hk]
      · exact spot_name gs _ _ _ l' hl' p hp

/-! ## 2 The driver's flat list -/

section
variable {σ C : Type}

theorem fill_block {bs : List (Block σ C)} {z : Block σ C} {fr : ProofFile.Frames σ C} {a : Place}
    {b : Block σ C} (h : (ProofFile.fill bs z fr).block a = some b) : b ∈ bs ∧ b.place = a := by
  have h' : (bs.find? fun b => b.place == a) = some b := h
  exact ⟨List.mem_of_find?_eq_some h', by simpa using List.find?_some h'⟩

/-- **Every block of the driver's chain that is of a kind stems from the list, name and place.** -/
theorem chainC_flat {bs : List (Block σ C)} {links : List ModelPart} {fr : ProofFile.Frames σ C}
    (hfr : ∀ a, fr.batch a = none) {c : Chain σ C} (h : ProofFile.chainC bs links fr = .ok c)
    {x : Block σ C} (hx : x ∈ c.blocksInOrder) (hk : x.place.kind ≠ KindName.frame) :
    ∃ b ∈ bs, x.name = b.name ∧ x.place = b.place := by
  unfold ProofFile.chainC at h
  split at h
  · cases h
  · rename_i z hz
    dsimp only at h
    split at h
    · cases h
    · rename_i c1 h1
      split at h
      · cases h
      · obtain rfl := Except.ok.inj h
        have up : ∀ y : Block σ C, (∃ b ∈ bs.dropLast, y.name = b.name ∧ y.place = b.place) →
            ∃ b ∈ bs, y.name = b.name ∧ y.place = b.place := fun y ⟨b, hb, e⟩ =>
          ⟨b, List.mem_of_mem_dropLast hb, e⟩
        have ofBlock : ∀ b : Block σ C, (ProofFile.fill bs.dropLast z fr).block x.place = some b →
            x.name = b.name → ∃ b ∈ bs, x.name = b.name ∧ x.place = b.place := fun b hb en => by
          obtain ⟨hm, hp⟩ := fill_block hb
          exact up x ⟨b, hm, en, hp.symm⟩
        rcases chain_walk h1 hx with ⟨l, sub, -, hm⟩ | ⟨b, hb, en, -, -⟩ | ⟨hkf, -⟩
        · rcases hm with ⟨b, hb, en, -, -⟩ | ⟨mk, g, hmk, en, -⟩ | ⟨hkf, -⟩
          · exact ofBlock b hb en
          · have hb' : (fr.batch x.place <|> (bs.dropLast.find? fun b => b.place == x.place).map
                fun b _ => b) = some mk := hmk
            rw [hfr] at hb'
            replace hb' : ((bs.dropLast.find? fun b => b.place == x.place).map fun b _ => b) =
                some mk := hb'
            obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
            exact up x ⟨b, List.mem_of_find?_eq_some hb, en,
              (by simpa using List.find?_some hb : b.place = x.place).symm⟩
          · exact absurd hkf hk
        · exact ofBlock b hb en
        · exact absurd hkf hk

end

/-! ## 3 The parts' frames, the shape, the roles -/

/-- A member of the parts' frames is a lot's block of the kind «frame», marked, with its role off the shape. -/
theorem frames_from_lots {T : ProofFile.PureSeat} {B : ProofFile.PureBase}
    (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) {x : ProofFile.FrameRole × Block S Cl}
    (hx : x ∈ (ProofFile.partsAt T B).frames) :
    ∃ L ∈ T.lots, ∃ b ∈ L.blocks B.G₀, b.place.kind = KindName.frame ∧
      x.1 = ProofFile.roleOf B.shape b.place ∧ x.2 = ProofFile.guardMark b := by
  simp only [ProofFile.partsAt] at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  rw [hall] at hy
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hy
  dsimp only at hx
  split at hx
  · cases hx
  · obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    refine ⟨L, hL, b, hb1, by simpa using hb2, ?_⟩
    split at e
    · cases e
    · cases e
    · obtain rfl := Option.some.inj e
      exact ⟨rfl, rfl⟩

/-- The shape's entries that are of a kind are the spots', name and place. -/
theorem shape_spot {Z : ProofFile.Pub} {spots : List ProofFile.Spot} {shape : List (String × Place)}
    (hs : ProofFile.spotsOf Z.cuts = some spots) (h : ProofFile.shapeOf Z = .ok shape) {e : String × Place}
    (he : e ∈ shape) (hk : e.2.kind ≠ KindName.frame) :
    ∃ p ∈ spots, p.name = e.1 ∧ p.place = e.2 := by
  unfold ProofFile.shapeOf at h
  obtain ⟨spots', hs', h⟩ := ok_bind h
  obtain rfl : spots = spots' := Option.some.inj (hs.symm.trans (orSay_ok hs'))
  dsimp only at h
  obtain ⟨c, hc, h⟩ := ok_bind h
  cases h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  obtain ⟨b, hb, e1, e2⟩ := chainC_flat (fun _ => rfl) hc hx hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
  exact ⟨p, hp, e1.symm, e2.symm⟩

/-- What the role «behind» says. -/
theorem role_behind {shape : List (String × Place)} {p : Place} {l : ℕ} {m : String}
    (h : ProofFile.roleOf shape p = .behind l m) :
    ∃ e ∈ shape, e.1 = m ∧ e.2.kind ≠ KindName.frame ∧ e.2.piece = p.piece ∧ p.link = some l := by
  unfold ProofFile.roleOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h <;> cases h
  · rename_i e l' hf hl
    split at h
    · rename_i hk
      cases h
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨e, List.mem_of_find?_eq_some hf, rfl, by simpa using hk, hp.2, hl⟩
    · split at h
      · cases h
      · split at h <;> cases h

/-! ## 4 The frames' pieces -/

theorem frames_last {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) :
    ∀ f ∈ fs, f.last = 13 ∨ f.last = 15 := by
  intro f hf
  unfold Johnson.Desc.First.Walk.Seat.framesOf at h
  obtain ⟨l, _, e⟩ := OnBytes.Road.L5.mapM_mem _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact Or.inr rfl
  · split at e
    · split at e
      · cases e
      · cases e
        exact Or.inl rfl
    · split at e
      · cases e
      · cases e
        exact Or.inl rfl
      · cases e
        exact Or.inl rfl

/-- **A block of the kind «frame» of the seat stands behind the links or at piece 0, 1, 13 or 15.** -/
theorem frame_piece {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S Cl} (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.frame) :
    b.place.link = none ∨ b.place.piece = 0 ∨ b.place.piece = 1 ∨ b.place.piece = 13 ∨
      b.place.piece = 15 := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · have hb' : x ∈ P1L20.blocksOf Z := hx
      unfold P1L20.blocksOf at hb'
      split at hb'
      · rename_i fs hfs
        obtain ⟨f, hf, h⟩ := List.mem_flatMap.1 hb'
        unfold ProofFile.frameBlocks at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rcases frames_last hfs f hf with e | e
          · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
      · obtain rfl := List.mem_singleton.1 hb'
        exact Or.inr (Or.inl rfl)
    · exact nomatch hb
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
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · obtain rfl := List.mem_singleton.1 hx
      exact Or.inl rfl
    · exact nomatch hb
  · rw [kind_K6 Z G b hb] at hk; cases hk
  · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk

/-- **No frame's block is joined behind a place of a kind other than K9 | K10 whose piece is 2 to 9.** -/
theorem no_behind {Z : ProofFile.Pub} {B : ProofFile.PureBase} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    {sp : ProofFile.Spot} (hsp : sp ∈ B.spots) (hk9 : sp.place.kind ≠ KindName.K9)
    (hk10 : sp.place.kind ≠ KindName.K10) (hn : 2 ≤ sp.place.piece ∧ sp.place.piece ≤ 9)
    {x : ProofFile.FrameRole × Block S Cl} (hx : x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames) {l : ℕ}
    {m : String} (hr : x.1 = .behind l m) : sp.name ≠ m := by
  obtain ⟨hs, hsh, -, hall⟩ := base_made hB
  obtain ⟨L, hL, b, hb, hkf, er, -⟩ := frames_from_lots hall hx
  obtain ⟨e, he, rfl, hke, hpe, hlk⟩ := role_behind (er.symm.trans hr)
  obtain ⟨p, hp, en, ep⟩ := shape_spot hs hsh he hke
  have hpc : b.place.piece = 0 ∨ b.place.piece = 1 ∨ b.place.piece = 13 ∨ b.place.piece = 15 := by
    rcases frame_piece hL hb hkf with h | h
    · rw [hlk] at h; cases h
    · exact h
  unfold ProofFile.spotsOf at hs
  obtain ⟨h1, n1, q1⟩ := spot_name _ _ _ _ _ hs sp hsp
  obtain ⟨h2, n2, q2⟩ := spot_name _ _ _ _ _ hs p hp
  rcases q1 with ⟨e1, q1⟩ | ⟨q1, -⟩
  · have c1 : (sp.place.kind == KindName.K10) = false := by simpa using hk10
    rw [c1] at q1
    simp only [Bool.false_eq_true, if_false] at q1
    rw [← en, e1]
    rw [q1] at hn
    rcases q2 with ⟨e2, q2⟩ | ⟨-, e2 | e2⟩
    · rw [e2]
      refine name_ne h1 h2 hn ?_
      rw [ep, hpe] at q2
      by_cases c2 : (e.2.kind == KindName.K10) = true
      · rw [if_pos c2] at q2
        omega
      · rw [if_neg c2] at q2
        omega
    · rw [e2]
      exact name_ne_eq h1 h2 hn
    · rw [e2]
      exact name_ne_shut h1 h2 hn
  · exact absurd q1 hk9

/-! ## 5 The join, alone -/

/-- **A block in front of the batching at a piece 2 to 9, of a kind other than K9 | K10, is a lot's block ALONE**, at onlineDescription's seat. -/
theorem chain_hear_alone {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) (hk9 : k ≠ KindName.K9) (hk10 : k ≠ KindName.K10)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      ∃ sp ∈ B.spots, ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks B.G₀,
        sp.place = { chain := 1, link := some l, piece := i + 1, kind := k } ∧
        b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } ∧
        LaidAlone ProofFile.sameReply b b' sp.name
          { chain := 1, link := some l, piece := i + 1, kind := k } := by
  obtain ⟨-, -, -, hall⟩ := base_made hB
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, harm⟩ :=
    chain_hear hall (makers_K9 Z B.G₀) hb hc l sub hl i k hk hk9
  refine ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, ?_⟩
  rcases harm with ⟨h, -⟩ | ⟨x, hx, hr, -⟩
  · exact h
  · exact absurd rfl (no_behind hB hsp (by rw [es]; exact hk9) (by rw [es]; exact hk10)
      (by rw [es]; exact hi) hx hr)

end IM

#print axioms IM.name_ne
#print axioms IM.spot_name
#print axioms IM.chainC_flat
#print axioms IM.frame_piece
#print axioms IM.no_behind
#print axioms IM.chain_hear_alone
