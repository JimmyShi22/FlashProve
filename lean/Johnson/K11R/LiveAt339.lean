-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/LiveAt339.lean: THE IDLE CASES IN THE OUTPUT HEAD's SEGMENT IN FRONT OF THE MERGE OF THE CLAIMS ON THE COMMITTED TABLE (number 346 of the first chain's flat list): WHICH CASE HOLDS AT NUMBER 339 (the code switch) AND AT NUMBER 342 (the sending of the reads). Johnson/K11R/MaskSeat.lean says in its Limits: «Which case holds is said by no file.» Here it is said, at 342 outright, at 339 UNDER ONE TEST WITH CODE ON THE PUBLIC PART.
  AT 342, FROM SCOPE, AN OPENING's LETTERS AND F.planOk = true ALONE (live_at_342): the public files name arrays for the reads (reads = some ts) AND give a quiet step behind them (ProofFile.readsQuietAt … = some q): both idle cases fail the sub-protocol's own test on the plan: K1.commitOwn's planOk asks arrays.isSome; ProofFile.refuser has planOk := false; Block.andThen's planOk is the two's «and».
  AT 339 (live_at_339): (1) THE SUB-PROTOCOL THAT ALWAYS REJECTS FALLS by F.planOk = true · (2) «finish» FALLS: the place's link is some 24 · (3) A FIND: «THE CODE SWITCH ALONE» DOES NOT FALL BY SCOPE AND planOk, AS FAR AS THE TEXTS SEARCHED GO: the lot's maker P1K2.pureAt goes by x.2.stands := P1K2.standsOf sp (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean:230-232): «H» | «F» | else: THE SPELLING, UP TO ITS FIRST DOT, OF THE FIRST STEP's NAME IN THE PLAN's TABLE OF STEPS Z.cuts (:= cutOf first.given.rounds, Johnson/Desc/ProofFile/Pub.lean). ProofFile.kindName does not read the head for the kind K2 («sendLoc»); no test inside planOk tells the two dresses apart (headOpened has no round); no law on the looks' spelling in scope was found in Johnson/IMR, in Johnson/Desc/Ok or in Johnson/P5T (searched: «spotsOf», «.cuts»). SO IT IS ASKED AS A TEST: standsHeadB Z: every place of the plan's list at the address (1, some 24, 2, K2) stands as «head». ITS PAYER, NOT IN THIS FILE: an evaluation at the release's values, or a law on the planner's names of rounds.
  k2_mem_spot: IM.k2_mem (Johnson/IMR/K2Seat.lean) AGAIN, arm for arm, KEEPING WHAT THAT THEOREM DROPS: the place sp of the plan's list of which the sub-protocol is made, and P1K2.standsOf sp beside each dress.
LIMITS. At OnBytes.secondHashFunction alone. standsHeadB is evaluated nowhere here. That a step at 339 or 342 ACCEPTS at some state is not shown: only that the sub-protocols there are the live ones. No soundness. Nothing on hiding.
-/
import Johnson.IMR.K2Seat
import Johnson.IMR.K1Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11Live

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName blocksOk)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened)
open IM (k2P under LaidAlone)
open ProofFile (Cl)

/-- The code switch's address in the output head's link. -/
abbrev a339 : Place := { chain := 1, link := some 24, piece := 2, kind := .K2 }

/-- **A TEST WITH CODE ON THE PUBLIC PART**: every place of the plan's list at the code switch's
address in the output head's link "stands" as the head's (`P1K2.standsOf`: the part of its first
step's name in front of the first dot is "H"). -/
def standsHeadB (Z : ProofFile.Pub) : Bool :=
  ((ProofFile.spotsOf Z.cuts).getD []).all fun sp => !(sp.place == a339) || P1K2.standsOf sp == At.head

/-- **A sub-protocol of the code switch's lot that passes its test on the plan: the place of the
plan's list of which it is made, and its dress BY THAT PLACE's WORD "stands".** -/
theorem k2_mem_spot {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit}
    (h : x ∈ P1K2.pureTable (fun _ _ => some none) Z G) (hp : x.planOk = true) :
    ∃ sps sp, ProofFile.spotsOf Z.cuts = some sps ∧ sp ∈ sps ∧ x.name = sp.name ∧ x.place = sp.place ∧
      ∃ P n, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P sp.place.link = some n ∧
        ((P1K2.standsOf sp = At.finish ∧
            x = under sp.name sp.place (finishPlace (k2P Z sp.place sp.name .finish n))) ∨
          (P1K2.standsOf sp = At.head ∧ ∃ l HP, sp.place.link = some l ∧
            P1K2.pureLetters G l = some HP ∧
            x = under sp.name sp.place ((codeSwitchKind (k2P Z sp.place sp.name .head n) : Block S Unit).andThen
              sp.name (headOpened sp.name sp.place HP))) ∨
          (P1K2.standsOf sp = At.link ∧
            x = under sp.name sp.place (codeSwitchKind (k2P Z sp.place sp.name .link n)))) := by
  unfold P1K2.pureTable at h
  obtain ⟨sp0, _, ex⟩ := List.mem_map.1 h
  cases hy : (P1K2.pureSpots Z G).find? (fun x => x.1.name == sp0.name) with
  | none =>
    rw [hy] at ex
    subst ex
    exact nomatch hp
  | some y =>
    rw [hy] at ex
    dsimp only at ex
    cases hpa : P1K2.pureAt (fun _ _ => some none) G y with
    | none =>
      rw [hpa] at ex
      subst ex
      exact nomatch hp
    | some c =>
      rw [hpa] at ex
      obtain rfl : c = x := ex
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
          obtain ⟨hs1, _⟩ := List.mem_filter.1 hs'
          unfold P1K2.p2With at hpw
          obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hpw
          unfold P1K2.pureAt at hpa
          dsimp only at hpa
          split at hpa
          · rename_i hst
            obtain rfl := Option.some.inj hpa
            refine ⟨sps, sp', rfl, hs1, rfl, rfl, P, n, hP, hn, Or.inl ⟨hst, ?_⟩⟩
            show _ = under sp'.name sp'.place (finishPlace (k2P Z sp'.place sp'.name .finish n))
            unfold k2P
            rw [← hst]
            rfl
          · rename_i hst
            obtain ⟨HP, hHP, rfl⟩ := Option.map_eq_some_iff.1 hpa
            obtain ⟨l, hl, hHP⟩ := Option.bind_eq_some_iff.1 hHP
            refine ⟨sps, sp', rfl, hs1, rfl, rfl, P, n, hP, hn,
              Or.inr (Or.inl ⟨hst, l, HP, hl, hHP, ?_⟩)⟩
            show _ = under sp'.name sp'.place
              ((codeSwitchKind (k2P Z sp'.place sp'.name .head n) : Block S Unit).andThen
                sp'.name (headOpened sp'.name sp'.place HP))
            unfold k2P
            rw [← hst]
            rfl
          · rename_i hst
            obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hpa
            obtain ⟨l, _, ho⟩ := Option.bind_eq_some_iff.1 ho
            obtain rfl : none = o := Option.some.inj ho
            refine ⟨sps, sp', rfl, hs1, rfl, rfl, P, n, hP, hn, Or.inr (Or.inr ⟨hst, ?_⟩)⟩
            show _ = under sp'.name sp'.place (codeSwitchKind (k2P Z sp'.place sp'.name .link n))
            unfold k2P
            rw [← hst]
            rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **NUMBER 339 OF THE FIRST CHAIN's FLAT LIST IS THE CODE SWITCH IN THE HEAD's DRESS.** -/
theorem live_at_339 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hst : standsHeadB Z = true) :
    ∃ (b : Block S Cl) (x : Block S Unit) (Pr : P1K2.Prep) (n : P1K2.Nums)
        (HP : VerifiableInference.Desc.First.K2.HeadPar),
      c.blocksInOrder[339]? = some b ∧ LaidAlone ProofFile.sameReply b x.retype b.name a339 ∧
      P1K2.prepOf Z Bs.G₀ = some Pr ∧ P1K2.numsAt Pr (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      x = under x.name a339 ((codeSwitchKind (k2P Z a339 x.name .head n) : Block S Unit).andThen x.name
        (headOpened x.name a339 HP)) := by
  have hd := O.desc
  subst hd
  obtain ⟨Lk, b, x, e1, e2, hx, hla, his⟩ := IM.k2_head_of hS hR O
  have e339 : c.blocksInOrder[339]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (Nat.le_refl 24) 1] at h
  have hb : blocksOk c.blocksInOrder = true := by
    cases hb : blocksOk (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
        (ProofFile.startS Z) c).first.blocksInOrder with
    | true => exact hb
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hOk
  have hbp : b.planOk = true := by
    have h1 := List.all_eq_true.1 hb b (List.mem_of_getElem? e339)
    simp only [Bool.and_eq_true] at h1
    exact h1.1
  have hxp : x.planOk = true := by
    rw [IM.alone_planOk hla] at hbp
    exact (IM.retype_planOk x hbp).1
  have hxa : x.place = a339 := by
    obtain ⟨_, _, _, _, ⟨_, ex⟩ | ⟨_, _, _, _, ex⟩ | ⟨_, _, ex⟩⟩ := his.live hxp
    · exact (congrArg Block.place ex).trans rfl
    · exact (congrArg Block.place ex).trans rfl
    · exact (congrArg Block.place ex).trans rfl
  obtain ⟨sps, sp, hs, hsp, en, ep, Pr, n, hP, hn, harm⟩ := k2_mem_spot hx hxp
  have hh : P1K2.standsOf sp = At.head := by
    unfold standsHeadB at hst
    rw [hs] at hst
    have h1 := List.all_eq_true.1 hst sp hsp
    rw [← ep, hxa] at h1
    simpa using h1
  rw [← ep, hxa] at hn
  rw [← ep, ← en, hxa] at harm
  rcases harm with ⟨h0, _⟩ | ⟨_, l, HP, hl, hHP, ex⟩ | ⟨h0, _⟩
  · rw [hh] at h0
    cases h0
  · obtain rfl : 24 = l := Option.some.inj hl
    exact ⟨b, x, Pr, n, HP, e339, hla, hP, hn, hHP, ex⟩
  · rw [hh] at h0
    cases h0

/-- The reads' sending's address in the output head's link. -/
abbrev a342 : Place := { chain := 1, link := some 24, piece := 5, kind := .K1 }

/-- **NUMBER 342 OF THE FIRST CHAIN's FLAT LIST IS THE SENDING OF THE READS, WITH ARRAYS NAMED AND A
QUIET STEP BEHIND IT.** -/
theorem live_at_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ (b : Block S Cl) (X : OnBytes.Model.Stages.LinkH) (pd : ℕ) (ts : List ℕ)
        (digits : Option (List ℕ)) (q : Block S Unit),
      c.blocksInOrder[342]? = some b ∧ Bs.G₀.built[24]? = some X ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ X = some (5, pd, some ts, digits) ∧
      ProofFile.readsQuietAt Bs.G₀ 24 X (if X.kind == 0 || X.kind == 1 then 4 else 5) = some q ∧
      LaidAlone ProofFile.sameReply b (IM.k1Reads Z Bs.G₀ 24 X 5 (some ts)).retype b.name a342 := by
  have hd := O.desc
  subst hd
  have hk : (VerifiableInference.Desc.First.kindsBeforeBatching .head (24 == 0))[4]? = some KindName.K1 := by
    unfold VerifiableInference.Desc.First.kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, X, pr, pd, reads, digits, e1, e2, hX, hn, harm⟩ :=
    IM.k1_later O 24 .head (IM.subs_head hS hR O.pub O.blank) 4 hk (by decide)
  have e342 : c.blocksInOrder[342]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (Nat.le_refl 24) 4] at h
  have hb : blocksOk c.blocksInOrder = true := by
    cases hb : blocksOk (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
        (ProofFile.startS Z) c).first.blocksInOrder with
    | true => exact hb
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hOk
  have hbp : b.planOk = true := by
    have h1 := List.all_eq_true.1 hb b (List.mem_of_getElem? e342)
    simp only [Bool.and_eq_true] at h1
    exact h1.1
  rcases harm with ⟨e, hla⟩ | ⟨e, _⟩
  · subst e
    have hxp : (IM.k1Reads Z Bs.G₀ 24 X (4 + 1) reads).planOk = true := by
      rw [IM.alone_planOk hla] at hbp
      exact (IM.retype_planOk _ hbp).1
    have h2 : ((VerifiableInference.Desc.K1.laterAt Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z)
        24 (4 + 1) 1 reads : Block S Unit).planOk && (IM.k1Quiet Bs.G₀ 24 X).planOk) = true := hxp
    rw [Bool.and_eq_true] at h2
    obtain ⟨ha, hq⟩ := h2
    cases reads with
    | none =>
      have ha' : (VerifiableInference.Desc.K1.planOkOwn (VerifiableInference.Desc.K1.parLater
        Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z) 24 (4 + 1) 1) &&
          (none : Option (List ℕ)).isSome) = true := ha
      simp at ha'
    | some ts =>
      cases hr : ProofFile.readsQuietAt Bs.G₀ 24 X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
      | none =>
        unfold IM.k1Quiet at hq
        dsimp only at hq
        rw [hr] at hq
        exact nomatch hq
      | some q => exact ⟨b, X, pd, ts, digits, q, e342, hX, hn, hr, hla⟩
  · exfalso
    rcases IM.numbers_pieces hn with ⟨_, h'⟩ | ⟨_, h'⟩ <;> omega

end

end K11Live

#print axioms K11Live.k2_mem_spot
#print axioms K11Live.live_at_339
#print axioms K11Live.live_at_342
