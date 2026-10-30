-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K2Seat.lean: nothing can be joined behind the links; k2_finish_of spends chain_back alone. k2_link_of's LaidFramed IS WEAKER THAN Johnson/IMR/FirstSeats.lean's k2_link_sits.

Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K2's blocks (the code switch) at their
places in onlineDescription's first chain: «F:1», the first block behind the links · the first place of the
links 1 … 23 ·
the head's link's second place.
OBJECT. THE SEATED CONSTANTS, each carried over by Block.retype: a member x of the table P1K2.pureTable (fun _ _ => some none) Z G₀ (Johnson/Desc/ProofFile/Lot/K2.lean · K2OfPlan.lean) that stands at the driver's address a; WHAT x IS (K2Is): a mute (its test on the plan
says no; its decision refuses always), or K2's kind's block K2.codeSwitchKind p (Johnson/Top/H0/Tw/K2C/Kind.lean) at p := IM.k2P Z a x.name ‹stands› n, n given by P1K2.prepOf Z G₀ = some P · P1K2.numsAt P a.link = some n, IN ONE OF THREE DRESSES: K2.finishPlace p (a.link = none) ·
(codeSwitchKind p).andThen … (K2.headOpened … HP) · codeSwitchKind p alone (a.link = some l).
USER. This folder's files that state their laws in the goals' scope (the fold's walk wants «the first block behind the links asks finishFrontQ»; K2's tie at a link) · K2's files.
LETTERS. As in Johnson/IMR/K6Seat.lean. x: by its membership in the lot's table and its place; P ·
n: each by the equation that makes it; the name: x's own.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  spot_head         (Johnson/Desc/ProofFile/Places.lean: spotsFrom's text) a spot's name is ‹head›:‹count›; its piece the count (K10: two more); IT STANDS BEHIND THE LINKS JUST IF ITS HEAD IS «F» | «M» | «seal»; P1K2.standsOf goes by that head; or it is one of K9's two places without a round.
  stands_finish     a spot of the kind K2 at which standsOf says «finish» stands behind the links.
  k2P · under · K2Is · k2_mem · lot_K2   K2's lot's text, opened: every member x of the table is K2Is Z G x.place x.name x. BEHIND THE LINKS THE DRESSES «head» AND «link» CANNOT BE MADE (pureAt asks the place's link): so there: a mute, or finishPlace.
  role_behind_link   a role «behind l m» bears the name of a place IN link l.
  K2Is.live · K2Is.live_alone   THE MUTE's ARM FALLS WHERE THE BLOCK PASSES ITS TEST ON THE PLAN.
  k2_finish_of      (no premise on scope) c.back[0]? = some b · LaidAlone sameReply b x.retype b.name ⟨1, none, 1, K2⟩ · x a mute, or x = under x.name … (finishPlace (k2P Z … x.name .finish n)).
  k2_finish_under   ∃ b p2, c.back[0]? = some b ∧ p2.stands = .finish ∧ b.Under (finishPlace p2) (Block.Under: Johnson/Desc/Sound/HearsOnce.lean).
  k2_link_of        in scope, 1 ≤ l < 24: c.links[l].hear[0] is LaidFramed
                    (Johnson/IMR/FirstPlace.lean) of x.retype, K2Is … x.
  k2_head_of        in scope: c.links[24].hear[1] is x.retype ALONE, K2Is … x.

WHO PAYS THE PREMISES: as in K6Seat.lean.
What is not claimed. THAT x IS NO MUTE (a yes of the seated block, or its test on the plan, shuts the mute out: both are in K2Is's first arm). IN A LINK: WHICH OF THE TWO DRESSES «head» | «link»: standsOf goes by the spelling of the plan's looks («H»), which I do not read; K2.decideWith
matches p.stands against the record's «here», so a yes tells it: that lemma is K2's files' to show. At the links' first places: which arm of LaidFramed, and which block of the frames' lot (Johnson/IMR/FirstPlace.lean's head). In Chain.blocksInOrder a block behind the links stands as
{ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }. If two members of the table stood at one place, x were either. No soundness.
-/
import Johnson.IMR.BackPlace
import Johnson.IMR.Subs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching backKinds)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened)
open ProofFile (Cl)

/-! ## 1 The spots: head, link, «stands» -/

/-- A spot: its name is ‹head›:‹count›; its piece is the count, at K10 two more; it stands behind the links just if its head is one of «F» «M» «seal»; the word «stands» that K2's files have for it (P1K2.standsOf, Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) goes by that head. Or it is one of K9's two
places without a round. -/
theorem spot_head : ∀ (gs : List (List VerifiableInference.Desc.First.Cut)) (link piece : ℕ)
    (last : String) (l : List ProofFile.Spot), ProofFile.spotsFrom gs link piece last = some l →
    ∀ p ∈ l, ∃ (h : String) (n : ℕ), (p.name = s!"{h}:{n}" ∧
      (p.place.piece = if p.place.kind == KindName.K10 then n + 2 else n) ∧
      (p.place.link = none ↔ ProofFile.behindLinks h = true) ∧
      P1K2.standsOf p = (if h == "F" then At.finish else if h == "H" then At.head else At.link)) ∨
      (p.place.kind = KindName.K9 ∧ (p.name = s!"{h}:{n}.equation" ∨ p.name = s!"{h}:{n}.shut"))
  | [], _, _, _, l, h, p, hp => by
    unfold ProofFile.spotsFrom at h
    obtain rfl := Option.some.inj h
    cases hp
  | [] :: gs, link, piece, last, l, h, p, hp => by
    unfold ProofFile.spotsFrom at h
    exact spot_head gs link piece last l h p hp
  | (c :: g) :: gs, link, piece, last, l, h, p, hp => by
    unfold ProofFile.spotsFrom at h
    dsimp only at h
    obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.1 h
    split at hp
    · rename_i hk10
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | rfl | hp
      · exact ⟨_, _, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      · refine ⟨_, _, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
        · dsimp only
          rw [if_pos hk10]
        · dsimp only
          cases hb : ProofFile.behindLinks (ProofFile.headOf c.look) <;> simp
        · unfold P1K2.standsOf
          dsimp only
          simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some]
          split <;> rfl
      · exact ⟨_, _, Or.inr ⟨rfl, Or.inr rfl⟩⟩
      · exact spot_head gs _ _ _ l' hl' p hp
    · rename_i hk10
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨_, _, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
        · dsimp only
          rw [if_neg hk10]
        · dsimp only
          cases hb : ProofFile.behindLinks (ProofFile.headOf c.look) <;> simp
        · unfold P1K2.standsOf
          dsimp only
          simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some]
          split <;> rfl
      · exact spot_head gs _ _ _ l' hl' p hp

/-- A spot of the kind K2 at which P1K2.standsOf says «finish» stands behind the links. -/
theorem stands_finish {cs : List VerifiableInference.Desc.First.Cut} {spots : List ProofFile.Spot}
    (hs : ProofFile.spotsOf cs = some spots) {sp : ProofFile.Spot} (hsp : sp ∈ spots)
    (hk : sp.place.kind = KindName.K2) (hst : P1K2.standsOf sp = At.finish) :
    sp.place.link = none := by
  unfold ProofFile.spotsOf at hs
  obtain ⟨h, n, ⟨-, -, hl, est⟩ | ⟨h9, -⟩⟩ := spot_head _ _ _ _ _ hs sp hsp
  · rw [hst] at est
    by_cases hF : (h == "F") = true
    · refine hl.2 ?_
      unfold ProofFile.behindLinks
      rw [hF]
      rfl
    · rw [if_neg hF] at est
      split at est <;> cases est
  · rw [hk] at h9
    cases h9

/-! ## 2 K2's lot -/

/-- A place's numbers, as K2's lot makes them (`p2With`), at a place, a name and a word «stands». -/
def k2P (Z : ProofFile.Pub) (a : Place) (nm : String) (st : At) (n : P1K2.Nums) : P2 :=
  { name := nm, place := a, stands := st, grp := n.grp, firstTree := Z.P.firstTree, samples := n.samples,
    work₁ := n.work₁, roots := n.roots, seeds := n.seeds, nonZero := n.nonZero,
    work₂ := n.work₂, answers := n.answers, positions := n.positions, logN := n.logN,
    sent := P1K2.oraclesAt n.grp n.codes n.sent, read := n.read }

/-- A block under a name and a place (`pureAt`'s «under»). -/
def under (nm : String) (a : Place) (b : Block S Unit) : Block S Unit := { b with name := nm, place := a }

/-- **What a block of K2's lot is**, at its own place a and name nm: a mute, or K2's kind's block at the plan's numbers for a.link, in one of three dresses. -/
def K2Is (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (x : Block S Unit) : Prop :=
  (x.planOk = false ∧ ∀ s rs gs, ∃ e, x.decide s rs gs = .error e) ∨
    ∃ P n, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P a.link = some n ∧
      ((a.link = none ∧ x = under nm a (finishPlace (k2P Z a nm .finish n))) ∨
        (∃ l HP, a.link = some l ∧ P1K2.pureLetters G l = some HP ∧
          x = under nm a ((codeSwitchKind (k2P Z a nm .head n) : Block S Unit).andThen nm (headOpened nm a HP))) ∨
        (∃ l, a.link = some l ∧ x = under nm a (codeSwitchKind (k2P Z a nm .link n))))

/-- **The mute's arm falls where the block passes its test on the plan.** -/
theorem K2Is.live {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : K2Is Z G a nm x) (hp : x.planOk = true) :
    ∃ P n, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P a.link = some n ∧
      ((a.link = none ∧ x = under nm a (finishPlace (k2P Z a nm .finish n))) ∨
        (∃ l HP, a.link = some l ∧ P1K2.pureLetters G l = some HP ∧
          x = under nm a ((codeSwitchKind (k2P Z a nm .head n) : Block S Unit).andThen nm (headOpened nm a HP))) ∨
        (∃ l, a.link = some l ∧ x = under nm a (codeSwitchKind (k2P Z a nm .link n)))) := by
  rcases h with ⟨h0, -⟩ | h
  · rw [h0] at hp
    cases hp
  · exact h

/-- The like from the seated block's test, where the lot's block stands alone. -/
theorem K2Is.live_alone {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : K2Is Z G a nm x) {b : Block S Cl} {name : String} {a' : Place}
    (hla : LaidAlone ProofFile.sameReply b x.retype name a') (hp : b.planOk = true) :
    ∃ P n, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P a.link = some n ∧
      ((a.link = none ∧ x = under nm a (finishPlace (k2P Z a nm .finish n))) ∨
        (∃ l HP, a.link = some l ∧ P1K2.pureLetters G l = some HP ∧
          x = under nm a ((codeSwitchKind (k2P Z a nm .head n) : Block S Unit).andThen nm (headOpened nm a HP))) ∨
        (∃ l, a.link = some l ∧ x = under nm a (codeSwitchKind (k2P Z a nm .link n)))) := by
  rw [alone_planOk hla] at hp
  exact h.live (retype_planOk x hp).1

theorem k2_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit}
    (h : x ∈ P1K2.pureTable (fun _ _ => some none) Z G) : K2Is Z G x.place x.name x := by
  unfold P1K2.pureTable at h
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 h
  split
  · exact Or.inl ⟨rfl, fun _ _ _ => ⟨_, rfl⟩⟩
  · rename_i y hy
    cases hp : P1K2.pureAt (fun _ _ => some none) G y with
    | none => exact Or.inl ⟨rfl, fun _ _ _ => ⟨_, rfl⟩⟩
    | some c =>
      show K2Is Z G c.place c.name c
      have hm := List.mem_of_find?_eq_some hy
      unfold P1K2.pureSpots at hm
      cases hs : ProofFile.spotsOf Z.cuts with
      | none => rw [hs] at hm; cases hm
      | some sps =>
        rw [hs] at hm
        have hm' : y ∈ P1K2.p2All Z G sps := hm
        unfold P1K2.p2All at hm'
        split at hm'
        · cases hm'
        · rename_i P hP
          obtain ⟨sp', hs', e⟩ := List.mem_filterMap.1 hm'
          obtain ⟨p, hpw, rfl⟩ := Option.map_eq_some_iff.1 e
          obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs'
          have hk2 : sp'.place.kind = KindName.K2 := by simpa using hs2
          unfold P1K2.p2With at hpw
          obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hpw
          refine Or.inr ⟨P, n, hP, ?_⟩
          unfold P1K2.pureAt at hp
          dsimp only at hp
          split at hp
          · rename_i hst
            obtain rfl := Option.some.inj hp
            refine ⟨hn, Or.inl ⟨stands_finish hs hs1 hk2 hst, ?_⟩⟩
            show _ = under sp'.name sp'.place (finishPlace (k2P Z sp'.place sp'.name .finish n))
            unfold k2P
            rw [← hst]
            rfl
          · rename_i hst
            obtain ⟨HP, hHP, rfl⟩ := Option.map_eq_some_iff.1 hp
            obtain ⟨l, hl, hHP⟩ := Option.bind_eq_some_iff.1 hHP
            refine ⟨hn, Or.inr (Or.inl ⟨l, HP, hl, hHP, ?_⟩)⟩
            show _ = under sp'.name sp'.place ((codeSwitchKind (k2P Z sp'.place sp'.name .head n) : Block S Unit).andThen
              sp'.name (headOpened sp'.name sp'.place HP))
            unfold k2P
            rw [← hst]
            rfl
          · rename_i hst
            obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hp
            obtain ⟨l, hl, ho⟩ := Option.bind_eq_some_iff.1 ho
            obtain rfl : none = o := Option.some.inj ho
            refine ⟨hn, Or.inr (Or.inr ⟨l, hl, ?_⟩)⟩
            show _ = under sp'.name sp'.place (codeSwitchKind (k2P Z sp'.place sp'.name .link n))
            unfold k2P
            rw [← hst]
            rfl

/-- A block of kind K2 of the seat is one of K2's lot's table, carried over. -/
theorem lot_K2 {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) {b : Block S Cl}
    (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.K2) :
    ∃ x ∈ P1K2.pureTable (fun _ _ => some none) Z G, b = x.retype := by
  obtain rfl : L = ProofFile.k2Pure Z := lot_of_kind hL hb (by rw [hk]; rfl)
  rcases blocks_mem hb with ⟨x, hx, rfl⟩ | h
  · exact ⟨x, hx, rfl⟩
  · exact nomatch h

/-! ## 3 «F:1»: nothing is joined behind it -/

/-- What the role «behind» says, with the link. -/
theorem role_behind_link {shape : List (String × Place)} {p : Place} {l : ℕ} {m : String}
    (h : ProofFile.roleOf shape p = .behind l m) :
    ∃ e ∈ shape, e.1 = m ∧ e.2.kind ≠ KindName.frame ∧ e.2.piece = p.piece ∧ e.2.link = some l ∧
      p.link = some l := by
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
      exact ⟨e, List.mem_of_find?_eq_some hf, rfl, by simpa using hk, hp.2, hp.1.2.trans hl, hl⟩
    · split at h
      · cases h
      · split at h <;> cases h

/-! ## 4 K2's places -/

/-- «F:1»'s address. -/
abbrev k2PlaceF : Place := { chain := 1, link := none, piece := 1, kind := .K2 }

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **«F:1»: THE FIRST BLOCK BEHIND THE LINKS IS K2's LOT's, ALONE: A MUTE, OR K2.finishPlace AT THE PLAN's NUMBERS.** No premise on scope. -/
theorem k2_finish_of (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ (b : Block S Cl) (x : Block S Unit), c.back[0]? = some b ∧
      x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀ ∧ x.place = k2PlaceF ∧
      LaidAlone ProofFile.sameReply b x.retype b.name k2PlaceF ∧
      ((x.planOk = false ∧ ∀ s rs gs, ∃ e, x.decide s rs gs = .error e) ∨
        ∃ P n, P1K2.prepOf Z Bs.G₀ = some P ∧ P1K2.numsAt P none = some n ∧
          x = under x.name k2PlaceF (finishPlace (k2P Z k2PlaceF x.name .finish n))) := by
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨b, e1, sp, hsp, L, hL, b', hb', es, ep, harm⟩ :=
    chain_back hall (makers_K9 Z Bs.G₀) O.places O.chain 0 .K2 (fun sv => by cases sv <;> rfl)
      (by decide)
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [ep])
  have hla : LaidAlone ProofFile.sameReply b x.retype sp.name k2PlaceF := harm
  have epx : x.place = k2PlaceF := ep
  refine ⟨b, x, e1, hx, epx, by rw [alone_name hla]; exact hla, ?_⟩
  have his := k2_mem hx
  rw [epx] at his
  rcases his with h | ⟨P, n, hP, hn, h | ⟨l, _, hl, -⟩ | ⟨l, hl, -⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨P, n, hP, hn, h.2⟩
  · cases hl
  · cases hl

/-- Numbers that say nothing, with «stands» = finish: for the mute's arm, at which the seated block never says yes. -/
def idleP2 : P2 where
  name := ""
  place := k2PlaceF
  stands := .finish
  grp := 0
  firstTree := 0
  samples := 0
  work₁ := 0
  roots := 0
  seeds := 0
  nonZero := 0
  work₂ := 0
  answers := 0
  positions := 0
  logN := 0
  sent := []
  read := []

/-- **In the form that a fold's walker spends**: where «F:1»'s seated block says yes, K2.finishPlace (Johnson/Top/H0/Tw/K2C/Finish.lean) says the same yes, at numbers p2 with p2.stands = finish. p2 STANDS UNDER «there is», TIED BY «stands» ALONE: for a caller who
spends no other field. WHICH NUMBERS: k2_finish_of: k2P Z k2PlaceF x.name .finish n at prepOf's and numsAt's values; at the mute's arm (the seated block never says yes) idle numbers. -/
theorem k2_finish_under (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ (b : Block S Cl) (p2 : P2), c.back[0]? = some b ∧ p2.stands = .finish ∧
      b.Under (finishPlace p2 : Block S Unit) := by
  obtain ⟨b, x, e1, -, -, hla, harm⟩ := k2_finish_of O
  have hu := (alone_underR hla).2
  rcases harm with ⟨-, hm⟩ | ⟨P, n, -, -, ex⟩
  · refine ⟨b, idleP2, e1, rfl, fun t rs gs s' hy => ?_⟩
    have h1 : x.decide t rs gs = .ok s' := hu t rs gs s' hy
    obtain ⟨e, he⟩ := hm t rs gs
    rw [he] at h1
    cases h1
  · refine ⟨b, k2P Z k2PlaceF x.name .finish n, e1, rfl, fun t rs gs s' hy => ?_⟩
    have h1 : x.decide t rs gs = .ok s' := hu t rs gs s' hy
    rw [ex] at h1
    exact h1

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K2 AT THE FIRST PLACE OF THE LINKS 1 … 23.** -/
theorem k2_link_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l, 1 ≤ l → l < 24 → ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Block S Unit),
      c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
      x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀ ∧
      LaidFramed Z b x.retype b.name { chain := 1, link := some l, piece := 1, kind := .K2 } ∧
      K2Is Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x := by
  intro l h1 h24
  have hl0 : (l == 0) = false := by simpa using (by omega : l ≠ 0)
  have key : ∀ sub : ModelPart, sub ≠ .head → (ProofFile.subsOf Z)[l]? = some sub →
      ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Block S Unit),
        c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
        x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀ ∧
        LaidFramed Z b x.retype b.name { chain := 1, link := some l, piece := 1, kind := .K2 } ∧
        K2Is Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x := by
    intro sub hsub hs
    have hk : (kindsBeforeBatching sub (l == 0))[0]? = some KindName.K2 := by
      rw [hl0]
      cases sub
      · rfl
      · rfl
      · exact absurd rfl hsub
    obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hla⟩ :=
      chain_hear_first O.made O.places O.chain l sub hs 0 .K2 hk (by decide)
    obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [ep])
    have epx : x.place = { chain := 1, link := some l, piece := 1, kind := .K2 } := ep
    have his := k2_mem hx
    rw [epx] at his
    exact ⟨Lk, b, x, e1, e2, hx, hla, his⟩
  by_cases he : l % 2 = 0
  · have h := subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
    rw [show 2 * (l / 2) = l by omega] at h
    exact key .layers (by decide) h
  · have h := subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
    rw [show 2 * (l / 2) + 1 = l by omega] at h
    exact key .attention (by decide) h

/-- **K2 AT THE HEAD's LINK: ITS SECOND PLACE: ALONE.** -/
theorem k2_head_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Block S Unit),
      c.links[24]? = some Lk ∧ Lk.hear[1]? = some b ∧
      x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀ ∧
      LaidAlone ProofFile.sameReply b x.retype b.name { chain := 1, link := some 24, piece := 2, kind := .K2 } ∧
      K2Is Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x := by
  have hk : (kindsBeforeBatching .head (24 == 0))[1]? = some KindName.K2 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain 24 .head (subs_head hS hR O.pub O.blank) 1 .K2 hk
      (by decide) (by decide) (by decide)
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [ep])
  have epx : x.place = { chain := 1, link := some 24, piece := 2, kind := .K2 } := ep
  have his := k2_mem hx
  rw [epx] at his
  exact ⟨Lk, b, x, e1, e2, hx, by rw [alone_name hla]; exact hla, his⟩

end

end IM

#print axioms IM.k2_finish_of
#print axioms IM.k2_finish_under
#print axioms IM.k2_link_of
#print axioms IM.k2_head_of
#print axioms IM.spot_head
#print axioms IM.stands_finish
#print axioms IM.K2Is.live
#print axioms IM.K2Is.live_alone
#print axioms IM.k2_mem
