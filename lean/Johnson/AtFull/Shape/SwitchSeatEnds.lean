-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchSeatEnds.lean: THE CODE SWITCH's LAST TWO PLACES IN THE PROOF FILE's OWN
FIRST CHAIN (kind K2): THE SECOND PLACE OF THE HEAD's LINK ("H:2", member 339 of the flat list) AND
THE FIRST PLACE BEHIND THE LINKS ("F:1", member 353): WHICH DRESS STANDS THERE, AND THE SEATS THE
WAY BACK: from the returns of the pieces to the return of the seated member. Under the head
`P5J.AtMgA`; general in the three public files (in the goals' scope); a joining of laws; nothing is
evaluated.

Main names.
* `head_arm`: GENERAL: where every place with numbers of the lot stands in the dress that its link
  asks (K2Caller.dressOf 25): a block of the lot's table that passes its test on the plan and stands
  in a link l with l + 1 = 25 is the switch in the head's dress with "opened" behind it, at the
  plan's numbers and letters for l. (The twin of `link_arm`, Johnson/AtFull/Shape/SwitchDress.lean.
  At the first place behind the links the library's own `IM.k2_finish_of` says the dress.)
* `k2_openings`, `k2_two`: the switch's block states two rounds and reads as many groups of columns
  as its place reads trees.
* `headPlace_returns`: GENERAL: as many groups of columns come as the place reads trees; the
  decision in the head's dress returns m, and K2.headOpenQ returns t at m: the two as one return t.
* `finishPlace_returns`: GENERAL: as many groups of columns come as the place reads trees;
  K2.finishFrontQ, the decision at the finish and K2.finishBehindQ return one behind the other:
  K2.finishPlace returns what the last returns.
* `headOpen_unmarked`, `finish_unmarked`: behind them no mark stands.
* `switch_head_seat`: under the head: the plan's letters; the member b at number 14 · 24 + 1 + 2;
  its declared rounds are the switch's; and where the decision in the head's dress returns m and
  "opened" returns t behind it, b returns t.
* `switch_finish_seat`: the like at number 353 + 0, from the three returns in a row.

What pays what at the seat. The lot's block stands alone there (`IM.k2_head_of`, `IM.k2_finish_of`);
its seat asks no mark behind and the reply as it was (`IM.yes_alone`, read from right to left): the
first by the two laws above, the second by `placeH2LeavesReply` and `placeF1LeavesReply`
(Johnson/Top/H0/Tw/K2C/LeavesOut.lean). That as many groups of columns come as the place reads trees
is read off the decision's own yes (`head_inv`, `finish_inv`).

Limits. THE SEATS ALONE: THAT THE PIECES RETURN IS ASKED, NOT SHOWN: the quiet steps' returns are in
Johnson/Desc/First/Shape/SwitchEndsReturns.lean; the decision's are not here. Neither `Carries` nor
`Returns` is stated: these two members do not count as paid by this file. THE NUMBERS STAND AT THE
EMPTY NAME (k2P … "" …), while the member's own bear the block's name: no loss, since the decision
and the rounds do not read the name (the proofs pass the one for the other by definition); the place
in the statements is the block's own; but codeSwitchKind (k2P … "" …) is not the block that stands there. h25 :
l + 1 = 25 is l = 24, in the form of SwitchDress.lean's link_arm. That the head has a member is
shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SwitchReturns
import Johnson.Desc.K12.FrameLaws
import Johnson.Top.H0.Tw.K2C.LeavesOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened decideWith finishFrontQ
  finishBehindQ headOpenQ HeadPar)
open VerifiableInference.Desc.First.K2Caller (dressOf)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (k2P under k2PlaceF)
open P5J (AtMgA)

/-! ## 1 The dress at the head's place -/

/-- **GENERAL: the head's dress.** -/
theorem head_arm {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit}
    (h : x ∈ P1K2.pureTable (fun _ _ => some none) Z G) (hp : x.planOk = true)
    (hst : ∀ y ∈ P1K2.pureSpots Z G, y.2.stands = dressOf 25 y.1.place.link) {l : Nat}
    (hl : x.place.link = some l) (h25 : l + 1 = 25) :
    ∃ P n HP, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters G l = some HP ∧
      x = under x.name x.place ((codeSwitchKind (k2P Z x.place x.name .head n) : Block S Unit).andThen x.name
        (headOpened x.name x.place HP)) := by
  unfold P1K2.pureTable at h
  obtain ⟨sp, -, hx⟩ := List.mem_map.1 h
  cases hy : (P1K2.pureSpots Z G).find? (fun x => x.1.name == sp.name) with
  | none =>
    simp only [hy] at hx
    subst hx
    cases hp
  | some y =>
    simp only [hy] at hx
    have hm := List.mem_of_find?_eq_some hy
    have hs := hst y hm
    cases hpa : P1K2.pureAt (fun _ _ => some none) G y with
    | none =>
      rw [hpa] at hx
      subst hx
      cases hp
    | some c =>
      rw [hpa] at hx
      obtain rfl : c = x := hx
      unfold P1K2.pureSpots at hm
      cases hsp : ProofFile.spotsOf Z.cuts with
      | none => rw [hsp] at hm; cases hm
      | some sps =>
        rw [hsp] at hm
        have hm' : y ∈ P1K2.p2All Z G sps := hm
        unfold P1K2.p2All at hm'
        split at hm'
        · cases hm'
        · rename_i P hP
          obtain ⟨sp', -, e⟩ := List.mem_filterMap.1 hm'
          obtain ⟨p, hpw, rfl⟩ := Option.map_eq_some_iff.1 e
          unfold P1K2.p2With at hpw
          obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hpw
          unfold P1K2.pureAt at hpa
          dsimp only at hpa hs
          split at hpa
          · rename_i hst'
            obtain rfl := Option.some.inj hpa
            have hl' : sp'.place.link = some l := hl
            rw [hst', hl'] at hs
            unfold dressOf at hs
            dsimp only at hs
            rw [if_pos (by simpa using h25)] at hs
            cases hs
          · rename_i hst'
            obtain ⟨HP, hHP, rfl⟩ := Option.map_eq_some_iff.1 hpa
            have hl' : sp'.place.link = some l := hl
            rw [hl'] at hHP
            refine ⟨P, n, HP, hP, by rw [← hl']; exact hn, hHP, ?_⟩
            show _ = under sp'.name sp'.place
              ((codeSwitchKind (k2P Z sp'.place sp'.name .head n) : Block S Unit).andThen sp'.name
                (headOpened sp'.name sp'.place HP))
            unfold k2P
            rw [← hst']
            rfl
          · rename_i hst'
            obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hpa
            obtain ⟨l', hl', ho⟩ := Option.bind_eq_some_iff.1 ho
            obtain rfl : none = o := Option.some.inj ho
            have hl'' : sp'.place.link = some l := hl
            rw [hst', hl''] at hs
            unfold dressOf at hs
            dsimp only at hs
            rw [if_pos (by simpa using h25)] at hs
            cases hs

/-! ## 2 The two places' own blocks: the way back -/

/-- The switch's block reads as many groups of columns as its place reads trees. -/
theorem k2_openings (p : P2) : (codeSwitchKind p : Block S Unit).openings = p.read.length := by
  simp [Block.openings, codeSwitchKind, VerifiableInference.Desc.First.K2.rounds]

/-- The switch's block states two rounds. -/
theorem k2_two (p : P2) : (codeSwitchKind p : Block S Unit).rounds.length = 2 := by
  simp [codeSwitchKind, VerifiableInference.Desc.First.K2.rounds]

/-- **"H:2": the switch in the head's dress, then "opened".** -/
theorem headPlace_returns {p : P2} {nm : String} {a : Place} {HP : HeadPar} {s m t : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hg : gs.length = p.read.length)
    (h1 : decideWith _root_.Tw.K2.sendByL8 p s [r₁, r₂] gs = .ok m)
    (h2 : headOpenQ HP m = .ok t) :
    ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm a HP)).decide s [r₁, r₂] gs = .ok t := by
  refine (VerifiableInference.Desc.K12.andThen_ok nm _ _ s t _ gs).2 ⟨m, ?_, h2⟩
  rw [k2_two, k2_openings, ← hg, List.take_length]
  exact h1

/-- **"F:1": the quiet front, the switch at the finish, the quiet step behind.** -/
theorem finishPlace_returns {p : P2} {s m₁ m₂ t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hg : gs.length = p.read.length)
    (h0 : finishFrontQ s = .ok m₁)
    (h1 : decideWith _root_.Tw.K2.sendByL8 p m₁ [r₁, r₂] gs = .ok m₂)
    (h2 : finishBehindQ m₂ = .ok t) :
    (finishPlace p : Block S Unit).decide s [r₁, r₂] gs = .ok t := by
  refine (VerifiableInference.Desc.K12.andThen_ok p.name _ _ s t _ gs).2 ⟨m₂, ?_, h2⟩
  refine (VerifiableInference.Desc.K12.andThen_ok p.name _ _ s m₂ _ _).2 ⟨m₁, h0, ?_⟩
  have e1 : ((VerifiableInference.Desc.roundlessBlock (p.name ++ ": front") p.place.chain p.place.link
      p.place.piece finishFrontQ : Block S Unit).andThen p.name (codeSwitchKind p)).rounds.length = 2 := by
    simp [Block.andThen, VerifiableInference.Desc.roundlessBlock, codeSwitchKind,
      VerifiableInference.Desc.First.K2.rounds]
  have e2 : ((VerifiableInference.Desc.roundlessBlock (p.name ++ ": front") p.place.chain p.place.link
      p.place.piece finishFrontQ : Block S Unit).andThen p.name (codeSwitchKind p)).openings =
      p.read.length := by
    simp [Block.andThen, Block.openings, VerifiableInference.Desc.roundlessBlock, codeSwitchKind,
      VerifiableInference.Desc.First.K2.rounds]
  rw [e1, e2, ← hg, List.take_length]
  exact h1

/-! ## 3 No mark, and the reply as it was -/

/-- Behind "opened" at the head's link no mark stands. -/
theorem headOpen_unmarked {HP : HeadPar} {m t : S} (h : headOpenQ HP m = .ok t) :
    t.failed = none := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, A⟩ :=
    (VerifiableInference.Desc.First.K2.headOpenQ_iff HP m t).1 h
  have h1 := ((S.unmarked_ok _ _).1 A.opens).2
  rw [A.out']
  exact h1

/-- Behind the three steps of "F:1" no mark stands. -/
theorem finish_unmarked {p : P2} {s m₁ m₂ t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .finish)
    (h0 : finishFrontQ s = .ok m₁)
    (h1 : decideWith _root_.Tw.K2.sendByL8 p m₁ rs gs = .ok m₂)
    (h2 : finishBehindQ m₂ = .ok t) : t.failed = none := by
  obtain ⟨G, x, s₁, a, A⟩ := (VerifiableInference.Desc.First.K2.finishFrontQ_iff s m₁).1 h0
  obtain ⟨r₁, r₂, a', G', w, roots, -, R⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h1
  obtain ⟨a'', m, -, -, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff m₂ t).1 h2
  have e1 := ((S.unmarked_ok _ _).1 A.enters).2
  show m₂.failed = none
  rw [R.hOut]
  show m₁.failed = none
  rw [A.out]
  exact e1

/-! ## 4 The seats, under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SECOND PLACE OF THE HEAD's LINK, THE WAY BACK**: the letters, the member, its declared
rounds; and: where the decision in the head's dress returns m and "opened" returns t behind it, the
member returns t. -/
theorem switch_head_seat (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧ cF.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧
      b.rounds = VerifiableInference.Desc.First.K2.rounds
        (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n) ∧
      ∀ (s m t : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        decideWith _root_.Tw.K2.sendByL8
          (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n) s [r₁, r₂]
          gs = .ok m →
        headOpenQ HP m = .ok t → b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, hy, hla, his⟩ := IM.k2_head_of h.scope h.reads O
  have hb : b.planOk = true := plans_at h b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  have hyp : y.planOk = true := by
    rw [IM.alone_planOk hla] at hb
    exact (IM.retype_planOk y hb).1
  have hpl : y.place = { chain := 1, link := some 24, piece := 2, kind := .K2 } := by
    obtain ⟨P0, n0, _, _, harm⟩ := his.live hyp
    rcases harm with ⟨_, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, e⟩ <;> exact congrArg Block.place e
  obtain ⟨P, n, HP, hP, hn, hHP, ey⟩ := head_arm hy hyp (stands_at h O.made) (l := 24)
    (by rw [hpl]) rfl
  rw [hpl] at ey
  have q := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 24 ≤ 24) 1] at q
  refine ⟨Bs, P, n, HP, b, O.made, hP, hn, hHP, q, ?_, fun s m t r₁ r₂ gs h1 h2 => ?_⟩
  · rw [hla, ey]
    show VerifiableInference.Desc.First.K2.rounds _ ++ [] = _
    rw [List.append_nil]
    rfl
  · have h1' : decideWith _root_.Tw.K2.sendByL8
        (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } y.name .head n) s
        [r₁, r₂] gs = .ok m := h1
    obtain ⟨_, _, _, _, _, _, -, R⟩ := VerifiableInference.Desc.First.K2.head_inv
      (rfl : (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } y.name .head
        n).stands = .head) h1'
    have hd : y.decide s [r₁, r₂] gs = .ok t := by
      rw [ey]
      exact headPlace_returns R.hTaken.2 h1' h2
    refine (IM.yes_alone hla (by simp) s t _ gs).2 ⟨hd, headOpen_unmarked h2, ?_⟩
    have e := VerifiableInference.Desc.First.K2.placeH2LeavesReply
      (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } y.name .head n) y.name HP
      s [r₁, r₂] gs t (headPlace_returns R.hTaken.2 h1' h2)
    have e' : t.out.reply = s.out.reply := e
    unfold ProofFile.sameReply
    rw [e']
    exact beq_self_eq_true _

/-- **THE FIRST PLACE BEHIND THE LINKS, THE WAY BACK.** -/
theorem switch_finish_seat (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P none = some n ∧
      cF.blocksInOrder[353 + 0]? = some b ∧
      b.rounds = VerifiableInference.Desc.First.K2.rounds (k2P Zp k2PlaceF "" .finish n) ∧
      ∀ (s m₁ m₂ t : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        finishFrontQ s = .ok m₁ →
        decideWith _root_.Tw.K2.sendByL8 (k2P Zp k2PlaceF "" .finish n) m₁ [r₁, r₂] gs = .ok m₂ →
        finishBehindQ m₂ = .ok t → b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, y, e1, -, -, hla, harm⟩ := IM.k2_finish_of O
  have hm : b ∈ cF.back := List.mem_of_getElem? e1
  have hmem : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) ∈ cF.blocksInOrder := by
    unfold Chain.blocksInOrder
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, hm, rfl⟩)))
  have hp : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := plans_at h _ hmem
  rw [Bool.and_eq_true] at hp
  have q := (IM.back_numbers h.scope h.reads O).1 0 b e1
  rcases harm with ⟨h0, -⟩ | ⟨P, n, hP, hn, ex⟩
  · exfalso
    have e := hp.1
    rw [IM.alone_planOk hla] at e
    have := (IM.retype_planOk y e).1
    rw [h0] at this
    exact nomatch this
  · refine ⟨Bs, P, n, _, O.made, hP, hn, q, ?_, fun s m₁ m₂ t r₁ r₂ gs h0 h1 h2 => ?_⟩
    · show b.rounds = _
      rw [hla, ex]
      show ([] ++ VerifiableInference.Desc.First.K2.rounds _) ++ [] = _
      rw [List.append_nil, List.nil_append]
      rfl
    · show b.decide s [r₁, r₂] gs = .ok t
      have h1' : decideWith _root_.Tw.K2.sendByL8 (k2P Zp k2PlaceF y.name .finish n) m₁ [r₁, r₂]
        gs = .ok m₂ := h1
      obtain ⟨_, _, _, _, _, _, -, R⟩ := VerifiableInference.Desc.First.K2.finish_inv
        (rfl : (k2P Zp k2PlaceF y.name .finish n).stands = .finish) h1'
      have hF := finishPlace_returns R.hTaken.2 h0 h1' h2
      have hd : y.decide s [r₁, r₂] gs = .ok t := by
        rw [ex]
        exact hF
      refine (IM.yes_alone hla (by simp) s t _ gs).2
        ⟨hd, finish_unmarked rfl h0 h1' h2, ?_⟩
      have e : t.out.reply = s.out.reply :=
        VerifiableInference.Desc.First.K2.placeF1LeavesReply _ s [r₁, r₂] gs t hF
      unfold ProofFile.sameReply
      rw [e]
      exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.headOpen_unmarked
#print axioms Johnson.AtFull.Shape.finish_unmarked
#print axioms Johnson.AtFull.Shape.switch_head_seat
#print axioms Johnson.AtFull.Shape.switch_finish_seat
#print axioms Johnson.AtFull.Shape.head_arm
#print axioms Johnson.AtFull.Shape.k2_openings
#print axioms Johnson.AtFull.Shape.k2_two
#print axioms Johnson.AtFull.Shape.headPlace_returns
#print axioms Johnson.AtFull.Shape.finishPlace_returns
