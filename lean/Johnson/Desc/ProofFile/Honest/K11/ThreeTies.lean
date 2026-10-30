-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ThreeTies.lean: the proofs of `ThreeTiesAlongFold` and
`HeadClaimIsOfKeys` (Honest/K11/ThreeTiesStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. A sentence on the state (`TiesAt`) is carried along the fold, border by border, by the rule
`foldStepsAt` (Johnson/Desc/K13/Honest/FoldCut.lean). It is laid by the output head's own
sub-protocol, number 341: behind any yes of that member from a well-laid ledger the state holds,
field by field, what the rounds drew (`logits_at_yes`,
Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean); that the member is the output head's as the
description seats it: `IM.k6_of`, `IM.k6_at_341`; that the ledger in front is well laid:
`P4.wellLaid_341` (Johnson/P4R/FreeAt341N.lean). It stays over the numbers 342 to 345:
`P4.kept_342`, `kept_343`, `kept_344`, `digits_345` (Johnson/P4R/WaK6At346.lean). At the end the
request is the one that the instance's words spell (the library's fact on the request at reached
states, as in ClaimAtHead.lean of this folder) and the token is the asked one. The second lemma:
`headClaimIsAtHead` (ClaimIs.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesStatement
import Johnson.Desc.ProofFile.Honest.K11.ClaimIs
import Johnson.Desc.ProofFile.Honest.K6.HeardAtYes
import Johnson.P4R.WaK6At346
import Johnson.P4SR.K6BackAtSeat
import Johnson.Desc.Kinds.Law.AtZLaw
import Johnson.ToldDescR.OwnSitsLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open OnBytes.PscRun (Sized)
open OnBytes.Desc.Reply (tokOf)
open VerifiableInference.Desc (Block Chain foldBlocks)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.Sound (below below_yes step_ok_iff)
open VerifiableInference.Desc.Kinds (Head.Par)
open VerifiableInference.Desc.Kinds.Head (parOf requestOf seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf KeptW requestOf_congr sized_of_wellLaid
  blockAt_later)
open VerifiableInference.Desc.K13.Law (LFull laid_in_scope)
open VerifiableInference.Desc.K13.Honest (roundsAhead roundsAhead_zero roundsAhead_take
  roundsAhead_succ take_take_le foldStepsAt)
open VerifiableInference.Desc.Kinds.Head.AtZ (rq_of_req)
open Johnson.Desc.First.Walk.Tied (RchAt Reach reach_of_fold reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open ProofFile.Honest.K6 (headTHr headRs headWin logits_at_yes)
open P5J (F0T)

/-- The sentence that is carried: the state stands in the head's link; what the head heard is laid,
with the two lists of challenges; the checked tokens are those of the state's own request and of
the token that its reply holds; the ledger has its sizes. -/
def TiesAt (p : Head.Par) (n : Nat) (heard : List Fmt.Drawn) (s : S) : Prop :=
  ∃ (a : HeadOwn) (hx : OnBytes.Model.Head.Heard) (y : Nat), s.here = .head a ∧ a.x = some hx ∧
    Sized a.F ∧ hx.tH.r = headTHr p n heard ∧ hx.rs = headRs p n heard ∧
    hx.win = headWin p (requestOf s) y ∧ s.out.reply.map tokOf = some y

/-- It stays where the sub-protocol between keeps what the library's sentence reads. -/
theorem TiesAt.kept {p : Head.Par} {n : Nat} {heard : List Fmt.Drawn} {s t : S}
    (h : TiesAt p n heard s) (K : KeptW s t) : TiesAt p n heard t := by
  obtain ⟨a, hx, y, ha, hax, hz, e1, e2, e3, e4⟩ := h
  obtain ⟨o, o', ho, ho', ex, _, _, _, er, eq, hL⟩ := K
  obtain rfl : a = o := Here.head.inj (ha.symm.trans ho)
  exact ⟨o', hx, y, ho', ex.trans hax, hL.sized hz, e1, e2, by rw [requestOf_congr eq]; exact e3,
    by rw [er]; exact e4⟩

/-- The wrapped sub-protocol's decision, off its step. -/
theorem decide_of_below {Cl : Type} {B : Block S Cl} {s t : S} {R : List Fmt.RoundView}
    {c : List VerifiableInference.Desc.OpenedColumn} {n : Nat}
    (h : (below B).step 0 s R c = .ok (t, n)) : ∃ rs gs, B.decide s rs gs = .ok t :=
  ⟨_, _, (below_yes B _ _ _ _ ((step_ok_iff 0 (below B) s t R c n).1 h).2.2.2).2⟩

/-- The member of the list with the test, cut at 346, is the test in front of the chain's own. -/
theorem member_of_take {Cl : Type} {l : List (Block S Cl)} {k : Nat} {b : Block S Cl}
    (h : ((l.map below).take 346)[k]? = some b) : k < 346 ∧ ∃ B, l[k]? = some B ∧ b = below B := by
  rw [List.getElem?_take] at h
  by_cases hk : k < 346
  · rw [if_pos hk, List.getElem?_map] at h
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨hk, B, hB, rfl⟩
  · rw [if_neg hk] at h
    cases h

set_option maxRecDepth 100000 in
/-- **Three of the four ties, along the fold.** -/
theorem threeTiesAlongFold : ThreeTiesAlongFold := by
  intro Z D r Zp Np cF xP Bs h hB x rs cols sj c hfold hf hrep a hx ha hax
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  have hb : 346 ≤ (cF.blocksInOrder.map below).length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF xP h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    rw [List.length_map]
    omega
  have hlen : ((cF.blocksInOrder.map below).take 346).length = 346 := by
    rw [List.length_take]
    omega
  have key := foldStepsAt 0 ((cF.blocksInOrder.map below).take 346)
    (fun k s => roundsAhead ((cF.blocksInOrder.map below).take 346) k ≤ rs.length ∧
      (342 ≤ k → TiesAt (parOf Bs'.G₀.W.hS (workOf Bs'.G₀.W))
        (roundsAhead (cF.blocksInOrder.map below) 341)
        ((rs.take (roundsAhead (cF.blocksInOrder.map below) 346)).map (·.drawn)) s))
    (ProofFile.startS Zp x.pub) rs cols _ ?_ hfold
    ⟨by rw [roundsAhead_zero]; omega, fun h0 => absurd h0 (by omega)⟩
  · rw [hlen] at key
    obtain ⟨a', hx', y, ha', hax', _, e1, e2, e3, e4⟩ := key.2 (by omega)
    obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
    obtain rfl : hx' = hx := Option.some.inj (hax'.symm.trans hax)
    have hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 346 ((x.pub, sj), ()) :=
      reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 346 hb sj rs _ cols c hfold
    have hp := (P5J.pins_of_laid h.scope h.laid).1
    have FF := P5J.foldFacts_at_head' h.toAtMg (Str := Unit)
      (fun b a => RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b a) (fun _ _ ha => ha)
      (L := LFull) (laid_in_scope h.scope h.laid.pub hp) (P5J.startB_at_head h.toAtMg)
      (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
    have hreq : sj.req = OnBytes.Model.Verify.words32 x.pub.request :=
      FF.reqIs 346 ((x.pub, sj), ()) hr hf
    rw [hrep] at e4
    obtain rfl : tokOf x.asked = y := Option.some.inj e4
    rw [rq_of_req Zp x.pub sj hreq] at e3
    exact ⟨e1, e2, e3⟩
  · intro k b hbk s c₀ t n hpre hsl hstep hI
    refine ⟨?_, fun h342 => ?_⟩
    · have h1 := hI.1
      have h2 := hsl
      rw [List.length_take, List.length_drop] at h2
      rw [roundsAhead_succ hbk]
      omega
    obtain ⟨hk, B, hBk, rfl⟩ := member_of_take hbk
    obtain ⟨rs', gs', hd⟩ := decide_of_below hstep
    by_cases h341 : k = 341
    · subst h341
      rw [take_take_le _ (by omega), roundsAhead_take _ (by omega)] at hpre
      rw [roundsAhead_take _ (by omega)] at hsl hstep
      have hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (x.pub, s) :=
        reach_raw (reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 341 (by omega) s rs _ cols c₀
          hpre)
      have hW := P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hR Bs'.G₀.W.hS
        (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)
      obtain ⟨Lk, b1, b', ms, e1, e2, _, hsc, hla, _, _, _⟩ := IM.k6_of h.scope h.reads O
      obtain rfl : b1 = B :=
        Option.some.inj ((IM.k6_at_341 h.scope h.reads O e1 e2).1.symm.trans hBk)
      have hn : roundsAhead (cF.blocksInOrder.map below) 341 + (below b1).rounds.length ≤
          roundsAhead (cF.blocksInOrder.map below) 346 := by
        have e342 : roundsAhead (cF.blocksInOrder.map below) 342 =
            roundsAhead (cF.blocksInOrder.map below) 341 + (below b1).rounds.length :=
          roundsAhead_succ (by rw [List.getElem?_map, hBk]; rfl)
        rw [← e342]
        unfold roundsAhead
        have : (cF.blocksInOrder.map below).take 346 =
            (cF.blocksInOrder.map below).take 342 ++ ((cF.blocksInOrder.map below).drop 342).take 4 :=
          List.take_add (i := 342) (j := 4)
        rw [this, List.flatMap_append, List.length_append]
        omega
      obtain ⟨d, hd346⟩ := Nat.exists_eq_add_of_le hn
      have hcut : rs.take (roundsAhead (cF.blocksInOrder.map below) 346) =
          rs.take (roundsAhead (cF.blocksInOrder.map below) 341) ++
            (((rs.drop (roundsAhead (cF.blocksInOrder.map below) 341)).take (below b1).rounds.length) ++
              (((rs.drop (roundsAhead (cF.blocksInOrder.map below) 341)).drop
                (below b1).rounds.length).take d)) := by
        rw [hd346, Nat.add_assoc, List.take_add, List.take_add]
      have hfront : ((rs.take (roundsAhead (cF.blocksInOrder.map below) 341)).map (·.drawn)).length =
          roundsAhead (cF.blocksInOrder.map below) 341 := by
        have h1 := hI.1
        rw [roundsAhead_take _ (by omega)] at h1
        rw [List.length_map, List.length_take]
        omega
      obtain ⟨o, X, y, ho, hoX, hy, t1, t2, t3⟩ := logits_at_yes (W := Bs'.G₀.W) (l := 24)
        (same := ProofFile.sameReply) (a := IM.k6Place) (b := b1) ⟨ms, b', b1.name, hsc, hla⟩ (by decide)
        (fun _ _ e => P4.same_of_eq e) (ToldDesc.step_of_below hstep) hW
        ((rs.take (roundsAhead (cF.blocksInOrder.map below) 341)).map (·.drawn))
        ((((rs.drop (roundsAhead (cF.blocksInOrder.map below) 341)).drop
          (below b1).rounds.length).take d).map (·.drawn))
      rw [hfront, ← List.map_append, ← List.map_append, ← hcut] at t1 t2
      have c1 := P4.yes_341 h.scope h.reads O hBk hd
      obtain ⟨a0, F1, X0, Q, _, hop, _, e⟩ :=
        VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ c1
      have ho2 : t.here = .head { a0 with F := F1, x := some X0, squaresP := some Q } := by rw [e]
      have eL : (seatAt Bs'.G₀.W.hS
          (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)).ledger t = F1 := by
        rw [e]
        show (S.fork? _).getD {} = F1
        simp [S.fork?, hop]
      have hz2 : Sized ({ a0 with F := F1, x := some X0, squaresP := some Q } : HeadOwn).F := by
        have hL := blockAt_later _ _ _ _ s t rs' gs' c1
        rw [eL] at hL
        exact hL.sized (sized_of_wellLaid hW)
      obtain rfl : o = { a0 with F := F1, x := some X0, squaresP := some Q } :=
        Here.head.inj (ho.symm.trans ho2)
      have ereq : t.req = s.req := by rw [e]
      have erep : t.out.reply = s.out.reply := by rw [e]
      exact ⟨_, X, y, ho, hoX, hz2, t1, t2, by rw [requestOf_congr ereq]; exact t3,
        by rw [erep]; exact hy⟩
    · have hT := hI.2 (by omega)
      have ⟨a1, _, _, ha1, _, hz1, _⟩ := hT
      have hcases : k = 342 ∨ k = 343 ∨ k = 344 ∨ k = 345 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · exact hT.kept (P4.kept_342 h.scope h.reads O hBk hd ha1)
      · exact hT.kept (P4.kept_343 h.scope h.reads O hBk hd ha1)
      · exact hT.kept (P4.kept_344 h.scope h.reads O hBk hd ha1)
      · exact hT.kept (P4.digits_345 h.scope h.reads O h.laid.planOk hBk hd ha1 hz1).1

/-- **The law on the head's claim from the one tie that is left.** -/
theorem headClaimIsOfKeys : HeadClaimIsOfKeys := by
  intro keys Z D r Zp Np cF xP Bs link claims h hB hcl hkeys
  refine headClaimIsAtHead _ Z D r Zp Np cF xP Bs link claims h hB hcl ?_
  intro x rs cols sj c hfold hf hrep a hx ha hax
  obtain ⟨e1, e2, e3⟩ :=
    threeTiesAlongFold Z D r Zp Np cF xP Bs h hB x rs cols sj c hfold hf hrep a hx ha hax
  exact ⟨hkeys x rs cols sj c hfold hf hrep a hx ha hax, e1, e2, e3⟩

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.TiesAt.kept
#print axioms ProofFile.Honest.K11.decide_of_below
#print axioms ProofFile.Honest.K11.member_of_take
#print axioms ProofFile.Honest.K11.threeTiesAlongFold
#print axioms ProofFile.Honest.K11.headClaimIsOfKeys
#print axioms ProofFile.Honest.K11.TiesAt
