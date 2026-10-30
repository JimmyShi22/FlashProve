-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/CloseSeat.lean: chain_close's second arm names the link itself (x.1 = .behind l b0.name); linkAt_close is proved over linkAt_shape.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: THE CLOSING's THREE BLOCKS (K9's one
equation · K10's closing · K9's «shut») at their places in every link of onlineDescription's first chain;
AND, ON THE WAY: A ROLE
«behind l m» BEARS THE NAME OF LINK l's FIRST PLACE, so that nothing is joined behind any place of piece 2 to 15.
OBJECT. THE SEATED CONSTANTS, each carried over by Block.retype: the members of VerifiableInference.Desc.K9.closeOf p Q (Johnson/Desc/First/Batch/Place.lean) := [{ oneEquation atS p with planOk := fits p Q }, closing Q, shut p (Q.piece + 1)], p given by
ProofFile.k9Where (ProofFile.k9Stretches Z) l = some p, Q by ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q (Johnson/Desc/ProofFile/Lot/K9.lean), as they stand at F.first.links[l].close[0 | 1 | 2], l < 25.
USER. K9's and K10's laws at the seated blocks. LETTERS. As in Johnson/IMR/K6Seat.lean; p · Q · x: each by the equation that makes it.
Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are still owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  linkPlaces_link · link_frame_pieces · link_first_piece · flat_in_link   the driver's table, link by link: a place of the table in link l is one of linkPlaces l sub; there the pieces 0 and n + 6 are the frame's; piece 1 is of a kind, neither K9's nor K10's.
  frames_row        a row of framesOf: its link is a link of the list; its «last» is 15 at a link of kind 2, else 13.
  HeadIsTwo Z       a premise in words of the public part: a link that the driver takes for the head has kind 2 (so that the frames' «last» is the driver's n + 6). PAID IN SCOPE: head_is_two.
  behind_first      under HeadIsTwo: BY PLACES: a member of the parts' frames with the role «behind l m»: m is the name of a spot at link l, piece 1, of a kind other than K9 | K10.
  name_ne_one · no_behind_wide   a name ‹head›:‹q›, q = 2 … 15, or one that ends in «.equation» | «.shut», is no name ‹head'›:1: so no frame's block is joined behind a place of piece 2 to 15 (K10's: 4 to 15). (Johnson/IMR/LaidFirst.lean's no_behind reaches 2 to 9, kinds but K9 | K10, with no premise.)
  cAt · closeAddresses_at · linkAt_close · chain_close   (general in the seat) closing block number j of link l stems from an entry (sp, ok b0) of the list of places that bears the driver's address (1, some l, n + 3 + j, k).
  close_alone       (NO PREMISE ON SCOPE; AT EVERY o; under HeadIsTwo Z) at a link l of the row of links, of the sort sub: the same three, each ALONE, at cAt l sub j k. close_of is its corollary.
  close_of          in scope, at every l < 25: for j = 0, 1, 2: Lk.close[j]? = some b · (K9.closeOf p Q)[j]? = some x · b IS seatedAs sameReply x.retype b.name (cAt l (subAt l) j k): ALONE.

WHO PAYS THE PREMISES: as in Johnson/IMR/K6Seat.lean.
What is not claimed. That Lk.close has no fourth block. The closing blocks' numbers in the blocksInOrder list
(Johnson/IMR/FlatScope.lean's link_at_flat gives them to whoever reads Link.blocksInOrder). Nothing on what
the three decide; fits p Q = true is not shown (where it is false the first block's test on the plan
says no).
behind_first DOES NOT SHARPEN A LINK's FIRST PLACE: it gives that the joined block's role names A spot at (l', 1) of the same name, hence (head_cancel) of the same head: that l' is the link itself still hangs on «no head comes twice». Lk.lay | clear: no seat. The names. No soundness.
-/
import Johnson.IMR.LinkSeat
import Johnson.IMR.K2Seat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt blockAt kindsBeforeBatching addresses hearsReply
  flatPlacesOf linkPlaces closeAddresses closeKinds backKinds frameAt)
open ProofFile (Cl)

/-! ## 1 The driver's table, link by link -/

theorem linkPlaces_link (l : ℕ) (sub : ModelPart) : ∀ a ∈ linkPlaces l sub, a.link = some l := by
  cases sub <;> cases hb : (l == 0) <;>
    simp [linkPlaces, kindsBeforeBatching, addresses, closeAddresses, closeKinds, frameAt,
      VerifiableInference.Desc.First.kindOfModelPart, hb]

/-- In a link's places the pieces 0 and n + 6 are the frame's. -/
theorem link_frame_pieces (l : ℕ) (sub : ModelPart) : ∀ a ∈ linkPlaces l sub,
    (a.piece = 0 ∨ a.piece = (kindsBeforeBatching sub (l == 0)).length + 6) → a.kind = KindName.frame := by
  cases sub <;> cases hb : (l == 0) <;>
    simp [linkPlaces, kindsBeforeBatching, addresses, closeAddresses, closeKinds, frameAt,
      VerifiableInference.Desc.First.kindOfModelPart, hb]

/-- A place of the driver's table that stands in link l is one of that link's. -/
theorem flat_in_link {links : List ModelPart} {several : Bool} {a : Place} {l : ℕ}
    (h : a ∈ flatPlacesOf links several) (hl : a.link = some l) :
    ∃ sub, links[l]? = some sub ∧ a ∈ linkPlaces l sub := by
  unfold flatPlacesOf at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · cases hl
      · obtain ⟨x, hx, h⟩ := List.mem_flatMap.1 h
        obtain ⟨sub, l'⟩ := x
        have hx' : links[l']? = some sub := by simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hx)
        obtain rfl : l' = l := Option.some.inj ((linkPlaces_link l' sub a h).symm.trans hl)
        exact ⟨sub, hx', h⟩
    · unfold addresses at h
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 h
      cases hl
  · obtain rfl := List.mem_singleton.1 h
    cases hl

/-- In a link's places piece 1 is of a kind, and neither K9's nor K10's. -/
theorem link_first_piece (l : ℕ) (sub : ModelPart) : ∀ a ∈ linkPlaces l sub, a.piece = 1 →
    a.kind ≠ KindName.K9 ∧ a.kind ≠ KindName.K10 := by
  cases sub <;> cases hb : (l == 0) <;>
    simp [linkPlaces, kindsBeforeBatching, addresses, closeAddresses, closeKinds, frameAt,
      VerifiableInference.Desc.First.kindOfModelPart, hb]

/-! ## 2 The frames' rows -/

/-- A row of framesOf: its link is a link of the list; its «last» is 15 at a link of kind 2, else 13. -/
theorem frames_row {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) :
    ∀ f ∈ fs, ∃ X, built[f.link]? = some X ∧ f.last = if X.kind == 2 then 15 else 13 := by
  intro f hf
  unfold Johnson.Desc.First.Walk.Seat.framesOf at h
  obtain ⟨l, hl, e⟩ := OnBytes.Road.L5.mapM_mem _ _ _ h f hf
  have hlt : l < built.size := List.mem_range.1 hl
  obtain ⟨X, hX⟩ : ∃ X, built[l]? = some X := ⟨_, Array.getElem?_eq_getElem hlt⟩
  dsimp only at e
  rw [hX] at e
  simp only [Option.map_some, Option.getD_some] at e
  split at e
  · rename_i hk
    cases e
    exact ⟨X, hX, by rw [if_pos hk]; rfl⟩
  · rename_i hk
    split at e
    · rename_i h0
      obtain rfl : l = 0 := by simpa using h0
      split at e
      · cases e
      · cases e
        exact ⟨X, hX, by rw [if_neg hk]⟩
    · split at e
      · cases e
      · cases e
        exact ⟨X, hX, by rw [if_neg hk]⟩
      · cases e
        exact ⟨X, hX, by rw [if_neg hk]⟩

/-- The links' kinds are such that the driver's «head» is the frames' «kind 2». -/
def HeadIsTwo (Z : ProofFile.Pub) : Prop :=
  ∀ (l : ℕ) (X : OnBytes.Model.Stages.LinkH), Z.p.built.links[l]? = some X →
    ProofFile.subOf X.kind = ModelPart.head → X.kind = 2

/-- **A ROLE «behind l m» BEARS THE NAME OF LINK l's FIRST PLACE**: BY PLACES: the frames' lot's blocks stand at the pieces 0, 1 and «last»; 0 and «last» are the frame's own places in the driver's table. -/
theorem behind_first {Z : ProofFile.Pub} {B : ProofFile.PureBase} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hk : HeadIsTwo Z) {x : ProofFile.FrameRole × Block S Cl}
    (hx : x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames) {l : ℕ} {m : String}
    (hr : x.1 = .behind l m) :
    ∃ p ∈ B.spots, p.name = m ∧ p.place.link = some l ∧ p.place.piece = 1 ∧
      p.place.kind ≠ KindName.K9 ∧ p.place.kind ≠ KindName.K10 := by
  obtain ⟨hs, hsh, -, hall⟩ := base_made hB
  obtain ⟨L, hL, fb', hfb', hkf, er, -⟩ := frames_from_lots hall hx
  obtain ⟨e, he, rfl, hke, hpe, hle, hlk⟩ := role_behind_link (er.symm.trans hr)
  obtain ⟨fb, hfb, rfl⟩ := frame_from hL hfb' hkf hlk
  obtain ⟨p, hp, en, ep⟩ := shape_spot hs hsh he hke
  obtain ⟨several, hpls⟩ := shape_places hsh
  have hmem : e.2 ∈ flatPlacesOf (ProofFile.subsOf Z) several := by
    rw [← hpls]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨sub, hsub, hin⟩ := flat_in_link hmem hle
  have hpl : (fb.retype : Block S Cl).place = fb.place := rfl
  rw [hpl] at hpe hlk
  have h1 : e.2.piece = 1 := by
    unfold P1L20.blocksOf at hfb
    split at hfb
    · rename_i fs hfs
      obtain ⟨f, hf, h⟩ := List.mem_flatMap.1 hfb
      obtain ⟨X, hX, hlast⟩ := frames_row hfs f hf
      unfold ProofFile.frameBlocks at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact absurd (link_frame_pieces l sub e.2 hin (Or.inl hpe)) hke
      · exact hpe
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
  obtain ⟨k9, k10⟩ := link_first_piece l sub e.2 hin h1
  exact ⟨p, hp, en, by rw [ep]; exact hle, by rw [ep]; exact h1, by rw [ep]; exact k9,
    by rw [ep]; exact k10⟩

/-! ## 3 Nothing is joined but behind a link's first place -/

/-- A name ‹head›:‹q› with q = 2 … 15 is no name ‹head'›:1. -/
theorem name_ne_one (h h' : String) {q : ℕ} (hq : 2 ≤ q ∧ q ≤ 15) : s!"{h}:{q}" ≠ s!"{h'}:{1}" := by
  intro e
  have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
  dsimp only at e2
  have t1 : (s!"{h'}:{1}").toList.reverse.take 2 = ['1', ':'] := tail_one h' _ '1' rfl
  rw [t1] at e2
  obtain ⟨h1, h2⟩ := hq
  have : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨
      q = 13 ∨ q = 14 ∨ q = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e3 := (tail_one h _ '2' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '3' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '4' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '5' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '6' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '7' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '8' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_one h _ '9' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_two h _ '0' '1' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_two h _ '1' '1' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_two h _ '2' '1' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_two h _ '3' '1' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_two h _ '4' '1' rfl).symm.trans e2; simp at e3
  · have e3 := (tail_two h _ '5' '1' rfl).symm.trans e2; simp at e3

/-- **No frame's block is joined behind a place whose piece is 2 to 15** (K10's: 4 to 15). -/
theorem no_behind_wide {Z : ProofFile.Pub} {B : ProofFile.PureBase}
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B) (hk : HeadIsTwo Z) {sp : ProofFile.Spot}
    (hsp : sp ∈ B.spots) (hn : 2 ≤ sp.place.piece ∧ sp.place.piece ≤ 15)
    (h10 : sp.place.kind = KindName.K10 → 4 ≤ sp.place.piece)
    {x : ProofFile.FrameRole × Block S Cl} (hx : x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames) {l : ℕ}
    {m : String} (hr : x.1 = .behind l m) : sp.name ≠ m := by
  obtain ⟨p, hp, rfl, -, hp1, k9, k10⟩ := behind_first hB hk hx hr
  obtain ⟨hs, -, -, -⟩ := base_made hB
  unfold ProofFile.spotsOf at hs
  obtain ⟨h1, n1, q1⟩ := spot_head _ _ _ _ _ hs sp hsp
  obtain ⟨h2, n2, q2⟩ := spot_head _ _ _ _ _ hs p hp
  rcases q2 with ⟨f1, c2, -, -⟩ | ⟨q2, -⟩
  · have kk : (p.place.kind == KindName.K10) = false := by simpa using k10
    rw [kk, hp1] at c2
    simp only [Bool.false_eq_true, if_false] at c2
    subst c2
    rw [f1]
    rcases q1 with ⟨e1, c1, -, -⟩ | ⟨-, e1 | e1⟩
    · rw [e1]
      refine name_ne_one h1 h2 ?_
      by_cases c : (sp.place.kind == KindName.K10) = true
      · rw [if_pos c] at c1
        have := h10 (by simpa using c)
        omega
      · rw [if_neg c] at c1
        omega
    · rw [e1]
      intro e
      have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
      dsimp only at e2
      have e3 := (tail_eq _).symm.trans (e2.trans (tail_one h2 _ '1' rfl))
      simp at e3
    · rw [e1]
      intro e
      have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
      dsimp only at e2
      have e3 := (tail_shut _).symm.trans (e2.trans (tail_one h2 _ '1' rfl))
      simp at e3
  · exact absurd q2 k9

/-! ## 4 The closing's blocks, by index -/

theorem closeAddresses_at (l n j : ℕ) (k : KindName) (h : closeKinds[j]? = some k) :
    (closeAddresses l n)[j]? = some { chain := 1, link := some l, piece := n + 3 + j, kind := k } := by
  unfold closeAddresses
  rw [List.getElem?_map, List.getElem?_zipIdx, h]
  simp

/-- The address of closing block number j of link l. -/
abbrev cAt (l : ℕ) (sub : ModelPart) (j : ℕ) (k : KindName) : Place :=
  { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 3 + j, kind := k }

/-- A link's closing block is the socket's at the driver's address. -/
theorem linkAt_close {σ C : Type} {H : Blocks σ C} {l : ℕ} {sub : ModelPart} {Lk : Link σ C}
    (h : linkAt H l sub = some Lk) (j : ℕ) (k : KindName) (hk : closeKinds[j]? = some k) :
    ∃ b, H.block (cAt l sub j k) = some b ∧ Lk.close[j]? = some { b with place := cAt l sub j k } := by
  have hc := congrArg (·[j]?) (VerifiableInference.Desc.Shape.linkAt_shape h).2.2.2.1
  simp only [List.getElem?_map, closeAddresses_at l _ j k hk, Option.map_some] at hc
  obtain ⟨c, e, hc'⟩ := Option.map_eq_some_iff.1 hc
  unfold blockAt at hc'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hc'.symm
  exact ⟨b, hb, e⟩

/-- **THE JOIN AT THE CLOSING, BY INDEX**: closing block number j of link l stems from an entry (sp, ok b0) of the list of places that bears the driver's address: alone, or with a member of the parts' frames joined whose role is
«behind l' ‹b0's name›». General in the seat. -/
theorem chain_close {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hb : (ProofFile.partsAt T B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) (l : ℕ)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (j : ℕ) (k : KindName)
    (hk : closeKinds[j]? = some k) :
    ∃ Lk b sp b0, c.links[l]? = some Lk ∧ Lk.close[j]? = some b ∧
      (sp, Except.ok b0) ∈ (ProofFile.partsAt T B).places ∧
      b0.place = cAt l sub j k ∧
      (b = Block.guarded T.same hearsReply { b0 with place := cAt l sub j k } ∨
        ∃ x ∈ (ProofFile.partsAt T B).frames, x.1 = ProofFile.FrameRole.behind l b0.name) := by
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
        obtain ⟨b, hbk, eb⟩ := linkAt_close hLk j k hk
        have hm := List.mem_of_find?_eq_some hbk
        have hpl : b.place = cAt l sub j k := by simpa using List.find?_some hbk
        obtain ⟨b0, hb0, ej⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hm)
        obtain ⟨x, hx, ex⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hb b0 hb0
        obtain ⟨sp, y⟩ := x
        obtain rfl : y = .ok b0 := ex
        refine ⟨_, _, sp, b0, eLk, (by
          show (Lk.close.map _)[j]? = _
          rw [List.getElem?_map, eb]
          rfl), hx, (by split at ej <;> subst ej <;> exact hpl), ?_⟩
        split at ej
        · rename_i w hw
          refine Or.inr ⟨w, List.mem_of_find?_eq_some hw, ?_⟩
          have hpred := List.find?_some hw
          obtain ⟨r, q⟩ := w
          cases r with
          | behind l' m =>
            have em : b0.name = m ∧ b0.place.link = some l' := by simpa using hpred
            obtain ⟨rfl, el⟩ := em
            have e0 : b0.place = cAt l sub j k := by
              subst ej
              exact hpl
            rw [e0] at el
            obtain rfl : l = l' := Option.some.inj el
            rfl
          | front => cases hpred
          | lay _ => cases hpred
          | clear _ => cases hpred
          | common => cases hpred
          | stray => cases hpred
        · subst ej
          exact Or.inl rfl

/-! ## 5 The closing's three blocks, in the goals' scope -/

theorem hear_len (sub : ModelPart) (f : Bool) : (kindsBeforeBatching sub f).length = 7 ∨ (kindsBeforeBatching sub f).length = 9 := by
  cases sub <;> cases f <;> simp [kindsBeforeBatching, VerifiableInference.Desc.First.kindOfModelPart]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- In scope the driver's «head» is the frames' «kind 2». -/
theorem head_is_two (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : HeadIsTwo Z := by
  intro l X hX hh
  have hsub : (ProofFile.subsOf Z)[l]? = some (ProofFile.subOf X.kind) := by
    unfold ProofFile.subsOf
    rw [List.getElem?_map, Array.getElem?_toList, hX]
    rfl
  obtain ⟨Lk, e, -⟩ := (link_flat_places O.chain).2 l _ hsub
  have hl : l < 25 := by
    rw [← links_25 hS hR O]
    exact (List.getElem?_eq_some_iff.1 e).1
  have es := Option.some.inj ((subs_scope hS hR O l hl).symm.trans hsub)
  rw [hh] at es
  have h24 : l = 24 := by
    unfold subAt at es
    by_contra hne
    rw [if_neg hne] at es
    split at es <;> cases es
  subst h24
  obtain ⟨-, m, fm, km, -⟩ := ground_named hS hR O.pub O.blank
  obtain ⟨ls, -, -, eB, -⟩ := blank_ground O.blank
  rw [eB] at fm
  obtain ⟨b, hb, kb⟩ := zipped_kind fm
  obtain rfl : b = X := Option.some.inj (hb.symm.trans hX)
  rw [kb, km]

/-- **THE CLOSING's THREE BLOCKS AT A LINK OF THE ROW OF LINKS, WITH NO PREMISE ON SCOPE, AT EVERY o: K9's FILES' closeOf p Q, MEMBER BY MEMBER, EACH ALONE**, under HeadIsTwo Z. (So that the row can be had at another size by two evaluations.) -/
theorem close_alone {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) (l : ℕ) (sub : ModelPart)
    (hsub : (ProofFile.subsOf Z)[l]? = some sub) :
    ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where)
        (Q : VerifiableInference.Desc.First.Close.Par), c.links[l]? = some Lk ∧
      k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
      ∀ j k, closeKinds[j]? = some k → ∃ (b : Block S Cl) (x : Block S Unit),
        Lk.close[j]? = some b ∧
        (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x ∧
        LaidAlone ProofFile.sameReply b x.retype b.name (cAt l sub j k) := by
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨Lk, p, e1, hp, hpc, f1, f2, f3, -⟩ := k9_alone O l sub hsub
  have hn := hear_len sub (l == 0)
  -- one closing block, with the numbers at which it is made
  have one : ∀ j k, closeKinds[j]? = some k → ∃ (b : Block S Cl) (x : Block S Unit)
      (Q : VerifiableInference.Desc.First.Close.Par), Lk.close[j]? = some b ∧
      ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x ∧
      LaidAlone ProofFile.sameReply b x.retype b.name (cAt l sub j k) := by
    intro j k hk
    have hj : (j = 0 ∧ k = KindName.K9) ∨ (j = 1 ∧ k = KindName.K10) ∨ (j = 2 ∧ k = KindName.K9) := by
      unfold closeKinds at hk
      rcases j with _ | _ | _ | j
      · exact Or.inl ⟨rfl, (Option.some.inj hk).symm⟩
      · exact Or.inr (Or.inl ⟨rfl, (Option.some.inj hk).symm⟩)
      · exact Or.inr (Or.inr ⟨rfl, (Option.some.inj hk).symm⟩)
      · cases hk
    obtain ⟨Lk', b, sp, b0, e1', e2, hx, hpl, harm⟩ :=
      chain_close O.places O.chain l sub hsub j k hk
    obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
    obtain ⟨hsp, harm2⟩ := places_from_lots hall sp b0 hx
    rcases harm2 with ⟨mk', hmk', rfl⟩ | ⟨-, L, hL, b', hb', ep, rfl⟩
    · -- a maker's face at a closing's address: K9's numbers were others than they are
      exfalso
      obtain ⟨mk0, h0, hm⟩ := road_batch_some hmk'
      obtain ⟨l'', p', -, -, k3, -, rfl⟩ := k9_batch_some h0
      obtain ⟨nm, enm⟩ := hm (fun s => .ok ([], s))
      rw [enm] at hpl
      obtain ⟨-, g2, -⟩ := k9Where_fields k3
      have hpl' : (⟨p'.chain, some p'.link, p'.piece, KindName.K9⟩ : Place) = cAt l sub j k := hpl
      have e3 : (some p'.link : Option ℕ) = some l := congrArg Place.link hpl'
      have e4 : p'.piece = (kindsBeforeBatching sub (l == 0)).length + 3 + j := congrArg Place.piece hpl'
      obtain rfl : l'' = l := g2.symm.trans (Option.some.inj e3)
      obtain rfl : p' = p := Option.some.inj (k3.symm.trans hp)
      omega
    · have hpl' : b'.place = cAt l sub j k := hpl
      have hkk : b'.place.kind = KindName.K9 ∨ b'.place.kind = KindName.K10 := by
        rw [hpl']
        rcases hj with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
      obtain rfl := lot_K9 hL hb' hkk
      have hla : LaidAlone ProofFile.sameReply b b' sp.name (cAt l sub j k) := by
        rcases harm with h | ⟨w, hw, hr⟩
        · exact h
        · exfalso
          have hsp' : sp.place = cAt l sub j k := ep.symm.trans hpl'
          have hpp : sp.place.piece = (kindsBeforeBatching sub (l == 0)).length + 3 + j := by rw [hsp']
          refine no_behind_wide O.made hk2 hsp ?_ (fun _ => by omega) hw hr rfl
          rcases hj with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
      rcases blocks_mem hb' with ⟨x, hx', rfl⟩ | h
      · have hplx : x.place = cAt l sub j k := hpl'
        rcases k9_own_mem hx' with ⟨l', p', Q, hp', hQ, hxc, -⟩ | ⟨l', e⟩
        · obtain ⟨-, g2, g3⟩ := k9Where_fields hp'
          obtain ⟨q1, q2⟩ := k10Par_fields hQ
          have hlink : p'.link = l := by
            unfold VerifiableInference.Desc.K9.closeOf at hxc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hxc
            rcases hxc with rfl | rfl | rfl
            · have e3 : (some p'.link : Option ℕ) = some l := congrArg Place.link hplx
              exact Option.some.inj e3
            · have e3 : (some Q.link : Option ℕ) = some l := congrArg Place.link hplx
              exact q1.symm.trans (Option.some.inj e3)
            · have e3 : (some p'.link : Option ℕ) = some l := congrArg Place.link hplx
              exact Option.some.inj e3
          obtain rfl : l' = l := g2.symm.trans hlink
          obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
          refine ⟨b, x, Q, e2, hQ, ?_, by rw [alone_name hla]; exact hla⟩
          unfold VerifiableInference.Desc.K9.closeOf at hxc ⊢
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hxc
          rcases hxc with rfl | rfl | rfl
          · have e4 : p'.pieceEq = (kindsBeforeBatching sub (l' == 0)).length + 3 + j :=
              congrArg Place.piece hplx
            obtain rfl : j = 0 := by omega
            rfl
          · have e5 : KindName.K10 = k := congrArg Place.kind hplx
            rcases hj with ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
            · cases e5
            · rfl
            · cases e5
          · have e4 : Q.piece + 1 = (kindsBeforeBatching sub (l' == 0)).length + 3 + j :=
              congrArg Place.piece hplx
            obtain rfl : j = 2 := by omega
            rfl
        · exfalso
          rw [e] at hplx
          have e4 : 0 = (kindsBeforeBatching sub (l == 0)).length + 3 + j := congrArg Place.piece hplx
          omega
      · exact nomatch h
  obtain ⟨-, -, Q, -, hQ, -, -⟩ := one 0 .K9 rfl
  refine ⟨Lk, p, Q, e1, hp, hQ, fun j k hk => ?_⟩
  obtain ⟨b, x, Q', h1, hQ', h2, h3⟩ := one j k hk
  obtain rfl : Q' = Q := Option.some.inj (hQ'.symm.trans hQ)
  exact ⟨b, x, h1, h2, h3⟩

/-- **THE CLOSING's THREE BLOCKS AT EVERY LINK, IN SCOPE: closeOf p Q, MEMBER BY MEMBER, EACH ALONE.** (close_alone at the scope's row of links.) -/
theorem close_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where)
        (Q : VerifiableInference.Desc.First.Close.Par), c.links[l]? = some Lk ∧
      k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
      ∀ j k, closeKinds[j]? = some k → ∃ (b : Block S Cl) (x : Block S Unit),
        Lk.close[j]? = some b ∧
        (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x ∧
        LaidAlone ProofFile.sameReply b x.retype b.name (cAt l (subAt l) j k) :=
  fun l hl => close_alone O (head_is_two hS hR O) l (subAt l) (subs_scope hS hR O l hl)

end

end IM

#print axioms IM.head_is_two
#print axioms IM.close_alone
#print axioms IM.close_of
#print axioms IM.no_behind_wide
#print axioms IM.chain_close
#print axioms IM.frames_row
#print axioms IM.behind_first
#print axioms IM.link_frame_pieces
#print axioms IM.flat_in_link
