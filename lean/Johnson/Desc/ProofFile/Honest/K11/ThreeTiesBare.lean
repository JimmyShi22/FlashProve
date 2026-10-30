-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ThreeTiesBare.lean: the proofs of `ThreeTiesAlongBareFold` and
`HeadClaimIsOfKeysBare` (Honest/K11/ThreeTiesBareStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The lines of ThreeTies.lean of this folder, made by program: the bare list for the list with
the test; so no test is taken off a step; the request's words at the end by `Meaning.K2.req_at_open`
(Johnson/LTPileR/AtGate.lean), which speaks of what the sub-protocols' own steps reach. The carried
sentence `TiesAt` and `TiesAt.kept` are that file's. The second lemma: `headClaimIsAtBare`
(ClaimBare.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesBareStatement
import Johnson.Desc.ProofFile.Honest.K11.ThreeTies
import Johnson.Desc.ProofFile.Honest.K11.ClaimBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open OnBytes.PscRun (Sized)
open OnBytes.Desc.Reply (tokOf)
open VerifiableInference.Desc (Block Chain foldBlocks)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.Sound (step_ok_iff)
open VerifiableInference.Desc.Kinds.Head (parOf requestOf seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf KeptW requestOf_congr sized_of_wellLaid
  blockAt_later)
open VerifiableInference.Desc.K13.Honest (roundsAhead roundsAhead_zero roundsAhead_take
  roundsAhead_succ take_take_le foldStepsAt)
open VerifiableInference.Desc.Kinds.Head.AtZ (rq_of_req)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open ProofFile.Honest.K6 (headTHr headRs headWin logits_at_yes)

/-- The member of the list cut at 346 is the chain's own. -/
theorem member_of_bare {Cl : Type} {l : List (Block S Cl)} {k : Nat} {b : Block S Cl}
    (h : (l.take 346)[k]? = some b) : k < 346 ∧ l[k]? = some b := by
  rw [List.getElem?_take] at h
  by_cases hk : k < 346
  · rw [if_pos hk] at h
    exact ⟨hk, h⟩
  · rw [if_neg hk] at h
    cases h

set_option maxRecDepth 100000 in
/-- **Three of the four ties, along the fold over the list that runs.** -/
theorem threeTiesAlongBareFold : ThreeTiesAlongBareFold := by
  intro Z D r Zp Np cF xP Bs h hB x rs cols sj c hfold hf hrep a hx ha hax
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF xP h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hlen : (cF.blocksInOrder.take 346).length = 346 := by
    rw [List.length_take]
    omega
  have key := foldStepsAt 0 (cF.blocksInOrder.take 346)
    (fun k s => roundsAhead (cF.blocksInOrder.take 346) k ≤ rs.length ∧
      (342 ≤ k → TiesAt (parOf Bs'.G₀.W.hS (workOf Bs'.G₀.W))
        (roundsAhead cF.blocksInOrder 341)
        ((rs.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn)) s))
    (ProofFile.startS Zp x.pub) rs cols _ ?_ hfold
    ⟨by rw [roundsAhead_zero]; omega, fun h0 => absurd h0 (by omega)⟩
  · rw [hlen] at key
    obtain ⟨a', hx', y, ha', hax', _, e1, e2, e3, e4⟩ := key.2 (by omega)
    obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
    obtain rfl : hx' = hx := Option.some.inj (hax'.symm.trans hax)
    have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (x.pub, sj) :=
      reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 346 hb sj rs _ cols c hfold
    have hreq : sj.req = OnBytes.Model.Verify.words32 x.pub.request :=
      Meaning.K2.req_at_open O (P5J.flat_ok h.toAtMg) 0 346 (x.pub, sj) hr hf
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
    obtain ⟨hk, hBk⟩ := member_of_bare hbk
    obtain ⟨rs', gs', hd⟩ : ∃ rs' gs', b.decide s rs' gs' = .ok t :=
      ⟨_, _, ((step_ok_iff 0 b s t _ c₀ n).1 hstep).2.2.2⟩
    by_cases h341 : k = 341
    · subst h341
      rw [take_take_le _ (by omega), roundsAhead_take _ (by omega)] at hpre
      rw [roundsAhead_take _ (by omega)] at hsl hstep
      have hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (x.pub, s) :=
        reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 341 (by omega) s rs _ cols c₀ hpre
      have hW := P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hR Bs'.G₀.W.hS
        (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs'.G₀.W)
      obtain ⟨Lk, b1, b', ms, e1, e2, _, hsc, hla, _, _, _⟩ := IM.k6_of h.scope h.reads O
      obtain rfl : b1 = b :=
        Option.some.inj ((IM.k6_at_341 h.scope h.reads O e1 e2).1.symm.trans hBk)
      have hn : roundsAhead cF.blocksInOrder 341 + b1.rounds.length ≤
          roundsAhead cF.blocksInOrder 346 := by
        have e342 : roundsAhead cF.blocksInOrder 342 =
            roundsAhead cF.blocksInOrder 341 + b1.rounds.length :=
          roundsAhead_succ hBk
        rw [← e342]
        unfold roundsAhead
        have : cF.blocksInOrder.take 346 =
            cF.blocksInOrder.take 342 ++ (cF.blocksInOrder.drop 342).take 4 :=
          List.take_add (i := 342) (j := 4)
        rw [this, List.flatMap_append, List.length_append]
        omega
      obtain ⟨d, hd346⟩ := Nat.exists_eq_add_of_le hn
      have hcut : rs.take (roundsAhead cF.blocksInOrder 346) =
          rs.take (roundsAhead cF.blocksInOrder 341) ++
            (((rs.drop (roundsAhead cF.blocksInOrder 341)).take b1.rounds.length) ++
              (((rs.drop (roundsAhead cF.blocksInOrder 341)).drop
                b1.rounds.length).take d)) := by
        rw [hd346, Nat.add_assoc, List.take_add, List.take_add]
      have hfront : ((rs.take (roundsAhead cF.blocksInOrder 341)).map (·.drawn)).length =
          roundsAhead cF.blocksInOrder 341 := by
        have h1 := hI.1
        rw [roundsAhead_take _ (by omega)] at h1
        rw [List.length_map, List.length_take]
        omega
      obtain ⟨o, X, y, ho, hoX, hy, t1, t2, t3⟩ := logits_at_yes (W := Bs'.G₀.W) (l := 24)
        (same := ProofFile.sameReply) (a := IM.k6Place) (b := b1) ⟨ms, b', b1.name, hsc, hla⟩ (by decide)
        (fun _ _ e => P4.same_of_eq e) hstep hW
        ((rs.take (roundsAhead cF.blocksInOrder 341)).map (·.drawn))
        ((((rs.drop (roundsAhead cF.blocksInOrder 341)).drop
          b1.rounds.length).take d).map (·.drawn))
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

/-- **The law on the head's claim, at the list that runs, from the one tie that is left.** -/
theorem headClaimIsOfKeysBare : HeadClaimIsOfKeysBare := by
  intro keys Z D r Zp Np cF xP Bs link claims h hB hcl hkeys
  refine headClaimIsAtBare _ Z D r Zp Np cF xP Bs link claims h hB hcl ?_
  intro x rs cols sj c hfold hf hrep a hx ha hax
  obtain ⟨e1, e2, e3⟩ :=
    threeTiesAlongBareFold Z D r Zp Np cF xP Bs h hB x rs cols sj c hfold hf hrep a hx ha hax
  exact ⟨hkeys x rs cols sj c hfold hf hrep a hx ha hax, e1, e2, e3⟩

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.member_of_bare
#print axioms ProofFile.Honest.K11.threeTiesAlongBareFold
#print axioms ProofFile.Honest.K11.headClaimIsOfKeysBare
