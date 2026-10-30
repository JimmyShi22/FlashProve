-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FirstSeats.lean: A LAW ABOUT ProofFile.pureSeat, NO PART OF IT: THE SEATS AT THE LINKS' FIRST
PLACES, IN THE FORM «Joined» (Johnson/IMR/SameSpot.lean's opened_joined), IN THE
GOALS' SCOPE: K7's «H:1» · K1's first place · K2's at the links 1 to 23; A LAW AT THE STEP FOR THAT FORM; and the closing's three by their numbers in the flat list.
first_sits is joined_at at the scope's sorts; ITS STATEMENT HAS «piece := 1». Joined.same | .step_same (at a place that is not K7's a yes gives sameReply s t = true) · Joined.rounds | .planOk. AT l = 24 THE FRAME DOES NOT OPEN THE LINK: the record enters it in K2.headFrontQ (the first half of k7Block) and it is opened in K2.headOpenQ at «H:2» (Johnson/Top/H0/Tw/K2C/Head.lean).
OBJECT. c.links[l].hear[0]; c.links[l].close[j]. USER. The rows «K07_sits» · «K02_sits» (names of rows, not of declarations; K02_sits: Johnson/P1K2R/SitsLaw.lean) · frames_sit (Johnson/IMR/FrameYes.lean) · K9's | K10's files (the numbers) · other files of Johnson/IMR/. LETTERS. As in Johnson/IMR/K6Seat.lean and Johnson/IMR/FrameSeat.lean.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).
CALLED, NOT TYPED: step_andThen_inv (Johnson/Desc/Sound/LawsCompose.lean) · step_ok_iff (RunIsDecide.lean) · roundsFit_len (Gather.lean) · step_under (SeatGuardChain.lean) · Fo.Pub.mapM_at.

  Joined Z l b b' a   (Johnson/IMR/SameSpot.lean) ∃ fs f, framesOf Z.p.built.links Z.first Z.p.X =
                      ok fs ∧ fs[l]? = some f ∧ b = seatedWith sameReply b' (guardMark (openedOf
                      f).retype) b.name a.
  Joined.framed     the older, weaker LaidFramed follows: so k7_of | k1_first_of | k2_link_of keep their statements and their callers.
  Joined.yes        a yes of b: b''s yes at the front of the rounds and groups, no mark behind it; then f.opened's yes from that record on, no mark, the reply as it was.
  Joined.step       THE LIKE AT THE STEP: b.step ft s rs cols = ok (t, n) → ∃ m, b'.step ft s rs
                    cols = ok (m, n) ∧ m.failed = none ∧ f.opened m = ok t ∧ t.failed = none ∧
                    sameReply m t = true. ONE WAY.
  first_sits        in scope, at each l < 25: hear[0] is Joined of a lot's block at (1, some l, 1, k).
  frames_head · k7_sits · k7_sits_yes   «H:1»: Joined Z 24 b (k7Block G₀.W 24).retype k7Place; THE HEAD's ROW's «opened» HANDS THE RECORD ON AS IT IS (f.opened = fun s => ok s): so a yes at «H:1» is k7Block's yes with the same record behind it.
  k1_first_sits · k2_link_sits   the like at link 0 (K1.firstSegmentOpening …) and at the links 1 to 23 (x ∈ P1K2.pureTable …, with K2Is).
  close_in_flat · close_numbers   closing block number j of link l is number 14 l + Lk.hear.length + 4 + j of the chain's flat list, in scope.

The three tops identify b' by the same steps as k7_of | k1_first_of | k2_link_of (K7Seat.lean · K1Seat.lean · K2Seat.lean): some twenty lines stand twice.
What is not claimed. K2 at a link: that x is no mute; which of K2Is' arms holds. The way back at the step (from b''s step and f.opened's yes to b's: it wants the marks' and the reply's tests). At K7's place the driver's guard leaves the decision free: nothing on «sameReply s t» there. The head's
row's test on the plan (v5: planFlag X 2) is not spoken of. Nothing in scope at an o other than secondHashFunction. No soundness.
-/
import Johnson.IMR.SameSpot
import Johnson.IMR.K7Seat
import Johnson.IMR.K1Seat
import Johnson.Desc.Sound.LawsCompose

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching hearsReply)
open ProofFile (Cl)

/-! ## 1 The form at a link's first place -/

/-- The older, weaker form follows. -/
theorem Joined.framed {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a) :
    LaidFramed Z b b' b.name a := by
  obtain ⟨fs, f, hfs, hf, e⟩ := h
  refine Or.inr ⟨openedOf f, ?_, e⟩
  unfold P1L20.blocksOf
  rw [hfs]
  refine List.mem_flatMap.2 ⟨f, List.mem_of_getElem? hf, ?_⟩
  unfold ProofFile.frameBlocks openedOf
  simp

/-- **A yes of the joined form**: the lot's block's yes at the front of the rounds and groups, no mark behind it; then the row's «opened» says yes from that record on, no mark behind it, the reply as it was. -/
theorem Joined.yes {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : b.decide s rs gs = .ok t) :
    ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
        (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S),
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧
      b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok m ∧ m.failed = none ∧
      f.opened m = .ok t ∧ t.failed = none ∧ ProofFile.sameReply m t = true := by
  obtain ⟨fs, f, hfs, hf, e⟩ := h
  obtain ⟨m, h1, h2, h3, h4⟩ := yes_with e hy
  obtain ⟨h5, h6⟩ := (guardMark_yes _ m t _ _).1 h3
  exact ⟨fs, f, m, hfs, hf, h1, h2, h5, h6, h4⟩

/-- **A LAW AT THE STEP FOR THE JOINED FORM**: a yes of the seated block's step is a yes of THE LOT's BLOCK's STEP at the same rounds and columns, with as many columns taken, no mark behind it; then the row's «opened» from that record on. (Over
step_andThen_inv, Johnson/Desc/Sound/LawsCompose.lean, and step_under, Johnson/Desc/Sound/SeatGuardChain.lean.) -/
theorem Joined.step {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a)
    {ft : ℕ} {s t : S} {n : ℕ} {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hy : b.step ft s rs cols = .ok (t, n)) :
    ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
        (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S),
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ b'.step ft s rs cols = .ok (m, n) ∧ m.failed = none ∧
      f.opened m = .ok t ∧ t.failed = none ∧ ProofFile.sameReply m t = true := by
  obtain ⟨fs, f, hfs, hf, e⟩ := h
  -- the driver's guard and the written address off
  have hU : b.UnderR ((marked b' b.name).andThen b.name
      ((ProofFile.guardMark (openedOf f).retype : Block S Cl).guarded ProofFile.sameReply fun _ => false)) := by
    rw [e]
    exact ⟨rfl, fun s rs gs t hy => VerifiableInference.Desc.guarded_under ProofFile.sameReply hearsReply
      { (marked b' _).andThen _ ((ProofFile.guardMark (openedOf f).retype : Block S Cl).guarded
        ProofFile.sameReply fun _ => false) with place := a } s rs gs t hy⟩
  have h1 := VerifiableInference.Desc.step_under hU hy
  -- all the rounds are the first half's
  have hlen : rs.length = (marked b' b.name).rounds.length := by
    obtain ⟨hf1, -⟩ := (VerifiableInference.Desc.Sound.step_ok_iff ft _ s t rs cols n).1 h1
    have := VerifiableInference.Desc.Sound.roundsFit_len _ _ hf1
    rw [this]
    show ((marked b' b.name).rounds ++ []).length = _
    rw [List.append_nil]
  rw [← List.append_nil rs] at h1
  obtain ⟨m, k₁, k₂, p1, p2, ek⟩ :=
    VerifiableInference.Desc.Sound.step_andThen_inv ft _ _ _ s t rs [] cols n hlen h1
  -- the second half has no round: it takes no column
  obtain ⟨-, -, hk2, d2⟩ := (VerifiableInference.Desc.Sound.step_ok_iff ft _ m t [] _ k₂).1 p2
  have hk0 : k₂ = 0 := hk2
  obtain ⟨d3, d4⟩ := (VerifiableInference.Desc.guarded_yes ProofFile.sameReply (fun _ => false) _ rfl m _ _ t).1 d2
  obtain ⟨d5, d6⟩ := (guardMark_yes _ m t _ _).1 d3
  -- the mark's test off the first half
  have p1' : b'.step ft s rs cols = .ok (m, k₁) ∧ m.failed = none :=
    (step_iff (c := marked b' b.name) (d := b') (Q := fun _ t => t.failed = none) rfl
      (fun s rs gs t => guardMark_yes b' s t rs gs) ft s m k₁ rs cols).1 p1
  refine ⟨fs, f, m, hfs, hf, ?_, p1'.2, d5, d6, d4⟩
  rw [ek, hk0, Nat.add_zero]
  exact p1'.1

/-- **At a place that is not K7's the driver's own guard stands around the whole**: a yes leaves the reply as it was in front of the lot's block. -/
theorem Joined.same {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a)
    (hk : a.kind ≠ KindName.K7) {s t : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : b.decide s rs gs = .ok t) : ProofFile.sameReply s t = true := by
  obtain ⟨fs, f, -, -, e⟩ := h
  rw [e] at hy
  have hp : hearsReply ({ (marked b' b.name).andThen b.name
      ((ProofFile.guardMark (openedOf f).retype : Block S Cl).guarded ProofFile.sameReply fun _ => false) with
      place := a } : Block S Cl).place = false := by
    show (a.kind == KindName.K7) = false
    simpa using hk
  exact ((VerifiableInference.Desc.guarded_yes ProofFile.sameReply hearsReply _ hp s rs gs t).1 hy).2

/-- The like at the step. -/
theorem Joined.step_same {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place}
    (h : Joined Z l b b' a) (hk : a.kind ≠ KindName.K7) {ft : ℕ} {s t : S} {n : ℕ}
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hy : b.step ft s rs cols = .ok (t, n)) : ProofFile.sameReply s t = true :=
  h.same hk ((VerifiableInference.Desc.Sound.step_ok_iff ft b s t rs cols n).1 hy).2.2.2

/-- The joined form's rounds are the lot's block's. -/
theorem Joined.rounds {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a) :
    b.rounds = b'.rounds := by
  obtain ⟨fs, f, -, -, e⟩ := h
  rw [e]
  show b'.rounds ++ [] = b'.rounds
  rw [List.append_nil]

/-- Its test on the plan is the lot's block's and the row's. -/
theorem Joined.planOk {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a) :
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ b.planOk = (b'.planOk && f.plan) := by
  obtain ⟨fs, f, hfs, hf, e⟩ := h
  refine ⟨fs, f, hfs, hf, ?_⟩
  rw [with_planOk _ e]
  show (b'.planOk && (f.plan && true)) = _
  rw [Bool.and_true]

/-! ## 2 In the goals' scope -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **AT EACH OF THE 25 LINKS' FIRST PLACES: THE LOT's BLOCK WITH THE LINK's OWN ROW's «opened» JOINED.** -/
theorem first_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∀ k, (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k →
      ∃ Lk b, c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
        ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks Bs.G₀,
          b'.place = { chain := 1, link := some l, piece := 1, kind := k } ∧
          Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := k } :=
  fun l hl _ hk => joined_at O (subs_scope hS hR O l hl) hk

/-- The row of framesOf at a link of kind 2 is the head's frame. -/
theorem frames_head {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) {i : ℕ}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} (hi : fs[i]? = some f)
    {X : OnBytes.Model.Stages.LinkH} (hX : built[i]? = some X) (hk : X.kind = 2) :
    f = Johnson.Desc.First.Walk.Seat.headFrame (Johnson.Desc.First.Walk.Seat.pubOf X) i first W := by
  unfold Johnson.Desc.First.Walk.Seat.framesOf at h
  obtain ⟨a, ha, e⟩ := Fo.Pub.mapM_at _ _ _ h i f hi
  obtain rfl : i = a := by
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 ha
    simpa using h2
  dsimp only at e
  rw [hX] at e
  simp only [Option.map_some, Option.getD_some, hk, beq_self_eq_true, if_true] at e
  exact (Except.ok.inj e).symm

/-- **K7's PLACE «H:1»: K7's PLACE's OWN BLOCK WITH THE HEAD's FRAME's «opened» JOINED, WHICH HANDS THE RECORD ON AS IT IS.** -/
theorem k7_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[24]? = some Lk ∧ Lk.hear[0]? = some b ∧
      Joined Z 24 b (k7Block Bs.G₀.W 24).retype k7Place ∧
      ∀ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
        fs[24]? = some f → f.opened = (fun s => .ok s) := by
  obtain ⟨sz, -⟩ := ground_gets hS hR O.pub O.blank
  have hk : (kindsBeforeBatching (subAt 24) (24 == 0))[0]? = some KindName.K7 := rfl
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hj⟩ := first_sits hS hR O 24 (by decide) .K7 hk
  obtain ⟨x, hm, rfl⟩ := lot_K7 hL hb' (by rw [ep])
  unfold ProofFile.h1Own at hm
  rw [sz] at hm
  obtain rfl := List.mem_singleton.1 hm
  refine ⟨Lk, b, e1, e2, hj, fun fs f hfs hf => ?_⟩
  have hsub := subs_head hS hR O.pub O.blank
  unfold ProofFile.subsOf at hsub
  rw [List.getElem?_map, Array.getElem?_toList] at hsub
  obtain ⟨X, hX, eX⟩ := Option.map_eq_some_iff.1 hsub
  rw [frames_head hfs hf hX (head_is_two hS hR O 24 X hX eX)]
  rfl

/-- **So a yes at «H:1» is K7's place's own block's yes, with the same record behind it.** -/
theorem k7_sits_yes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hj : Joined Z 24 b (k7Block Bs.G₀.W 24).retype k7Place) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    (k7Block Bs.G₀.W 24).decide s (rs.take (k7Block Bs.G₀.W 24).rounds.length)
      (gs.take (k7Block Bs.G₀.W 24).openings) = .ok t ∧ t.failed = none := by
  obtain ⟨-, -, -, -, -, hid⟩ := k7_sits hS hR O
  obtain ⟨fs, f, m, hfs, hf, h1, h2, h3, -, -⟩ := hj.yes hy
  rw [hid fs f hfs hf] at h3
  obtain rfl : m = t := Except.ok.inj h3
  exact ⟨h1, h2⟩

/-- **K1's FIRST PLACE, AT LINK 0.** -/
theorem k1_first_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[0]? = some Lk ∧ Lk.hear[0]? = some b ∧
      Joined Z 0 b
        (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z) :
          Block S Unit).retype k1Place0 := by
  have hk : (kindsBeforeBatching (subAt 0) (0 == 0))[0]? = some KindName.K1 := rfl
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hj⟩ := first_sits hS hR O 0 (by decide) .K1 hk
  obtain ⟨x, hx, rfl⟩ := lot_K1 hL hb' (by rw [ep]) (l := 0) (by rw [ep])
  rcases k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · exact ⟨Lk, b, e1, e2, hj⟩
  · exfalso
    have epc : pr = 1 := congrArg Place.piece ep
    rcases numbers_pieces hn with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · exfalso
    have epc : pd = 1 := congrArg Place.piece ep
    rcases numbers_pieces hn with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

/-- **K2's PLACE AT THE LINKS 1 TO 23.** -/
theorem k2_link_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l, 1 ≤ l → l < 24 → ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Block S Unit),
      c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
      x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀ ∧
      Joined Z l b x.retype { chain := 1, link := some l, piece := 1, kind := .K2 } ∧
      K2Is Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x := by
  intro l h1 h24
  have hk : (kindsBeforeBatching (subAt l) (l == 0))[0]? = some KindName.K2 := by
    have hl0 : (l == 0) = false := by simpa using (by omega : l ≠ 0)
    rw [hl0]
    unfold subAt
    rw [if_neg (by omega)]
    split <;> rfl
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hj⟩ := first_sits hS hR O l (by omega) .K2 hk
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [ep])
  have epx : x.place = { chain := 1, link := some l, piece := 1, kind := .K2 } := ep
  have his := k2_mem hx
  rw [epx] at his
  exact ⟨Lk, b, x, e1, e2, hx, hj, his⟩

/-! ## 3 The closing's three, by their numbers in the flat list -/

/-- By Block.lean's text: closing block number j stands in a link's flat list behind «laid», the hearing blocks, the batching and the frame's block behind it. General in the link. -/
theorem close_in_flat {σ C : Type} {Lk : Link σ C} {j : ℕ} {b : Block σ C}
    (h : Lk.close[j]? = some b) : Lk.blocksInOrder[Lk.hear.length + 3 + j]? = some b := by
  unfold Link.blocksInOrder
  refine getElem?_append_some ?_ _
  have e : Lk.hear.length + 3 = ((({ roundlessBlock (Lk.name ++ ": laid") Lk.chain (some Lk.number) 0 Lk.lay with
      planOk := VerifiableInference.Desc.orderOk Lk.hear Lk.order &&
        VerifiableInference.Desc.orderAfterOk Lk.hear Lk.orderAfter && Lk.close.all Block.hasNoClaimsAndNothingAfter &&
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)).hasNoClaimsAndNothingAfter } :
      Block σ C) :: Lk.hear) ++ [Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order),
      roundlessBlock (Lk.name ++ ": behind the batching") Lk.chain (some Lk.number) (Lk.hear.length + 2)
        Lk.runBehind]).length := by
    rw [List.length_append, List.length_cons]
    rfl
  rw [e, getElem?_append_add]
  exact h

/-- **In scope: closing block number j of link l is number 14 l + ‹the hearing blocks› + 4 + j of the chain's flat list.** -/
theorem close_numbers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Cl} (e1 : c.links[l]? = some Lk) {j : ℕ} {b : Block S Cl}
    (h : Lk.close[j]? = some b) : c.blocksInOrder[14 * l + Lk.hear.length + 4 + j]? = some b := by
  have hix := flatIx_scope hS hR O (l := l) (by omega) 0
  unfold flatIx at hix
  have h2 := link_at_flat e1 (close_in_flat h)
  rw [show (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length +
    (Lk.hear.length + 3 + j)) = 14 * l + Lk.hear.length + 4 + j by omega] at h2
  exact h2

end

end IM

#print axioms IM.close_in_flat
#print axioms IM.close_numbers
#print axioms IM.Joined.framed
#print axioms IM.Joined.yes
#print axioms IM.Joined.step
#print axioms IM.Joined.same
#print axioms IM.Joined.step_same
#print axioms IM.Joined.rounds
#print axioms IM.Joined.planOk
#print axioms IM.first_sits
#print axioms IM.frames_head
#print axioms IM.k7_sits
#print axioms IM.k7_sits_yes
#print axioms IM.k1_first_sits
#print axioms IM.k2_link_sits
