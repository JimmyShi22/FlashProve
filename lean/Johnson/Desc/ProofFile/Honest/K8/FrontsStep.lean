-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontsStep.lean: THE STATE THAT `frontsOf`
(Johnson/Desc/ProofFile/Honest/Fall.lean) LISTS BEHIND A MEMBER IS WHAT THAT MEMBER's OWN STEP
RETURNED, FROM THE STATE LISTED IN FRONT OF IT, AT THE VIEW's OWN ROUNDS; AND ALONG AN HONEST RUN
THESE ROUNDS' CHALLENGES ARE THE LIST's OWN. Statements and proofs. General in the description, the
book and the prover: no kind and no plan is named. LEMMAS; NONE OF THE LIBRARY's GOALS.

  `frontsOf_zero`   entry 0 holds the state that is handed in
  **`frontsOf_step`**   where there is an entry n + 1: there is an entry n; member n's step said yes
      from its state, at that member's own rounds of the view, and returned entry n + 1's state
  `walk_drawn`   a walk lays each round with the challenge that it is handed
  **`quiet_in_event`**   a file's first chain, a member K with one round, a run that returns and
      whose view has an entry K + 1: `frontAt` (Honest/K8/FrontsAgree.lean) says a state at K;
      member K's step said yes from it, at one round whose challenge is the list's own at that
      round's number, and returned entry K + 1's state
By: heard_laid (Honest/Law/WalkOn.lean) · walk_cons_ok, runC_parts (Law/Rule/WalkLaw.lean) ·
start_tied (Law/WalkFold.lean) · seal_back (Honest/Law/Run.lean).
Limits. The first chain alone. Nothing on whether a run returns.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc

variable {S Cl Xi W Y W₀ Rc Ky Tr X₀ X : Type}

/-- Entry 0 holds the state that is handed in. -/
theorem frontsOf_zero (ft : Nat) (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (e : Place × S × List Fmt.Drawn)
    (he : (frontsOf ft bs s rs cols)[0]? = some e) : e.2.1 = s := by
  cases bs with
  | nil => simp [frontsOf] at he
  | cons b l =>
    unfold frontsOf at he
    simp only at he
    split at he
    · simp at he
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      rfl

/-- **An entry behind member n.** -/
theorem frontsOf_step (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (e' : Place × S × List Fmt.Drawn),
    (frontsOf ft bs s rs cols)[n + 1]? = some e' →
    ∃ (e : Place × S × List Fmt.Drawn) (b : Block S Cl) (cols' : List OpenedColumn) (m : Nat),
      (frontsOf ft bs s rs cols)[n]? = some e ∧ bs[n]? = some b ∧
      ((rs.drop (rnds (bs.take n))).take b.rounds.length).length = b.rounds.length ∧
      b.step ft e.2.1 ((rs.drop (rnds (bs.take n))).take b.rounds.length) cols' = .ok (e'.2.1, m)
  | [], _, _, _, _, _, he => by
    simp [frontsOf] at he
  | b :: l, s, rs, cols, n, e', he => by
    have hu : frontsOf ft (b :: l) s rs cols =
        if (rs.take b.rounds.length).length != b.rounds.length then [] else
        (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
          match b.step ft s (rs.take b.rounds.length) cols with
          | .error _ => []
          | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
      conv_lhs => unfold frontsOf
      rfl
    rw [hu] at he ⊢
    split at he
    · simp at he
    · rename_i hg
      rw [if_neg hg]
      have hlen : (rs.take b.rounds.length).length = b.rounds.length := by simpa using hg
      rw [List.getElem?_cons_succ] at he
      cases hst : b.step ft s (rs.take b.rounds.length) cols with
      | error x =>
        rw [hst] at he
        simp at he
      | ok y =>
        obtain ⟨s', k⟩ := y
        rw [hst] at he
        simp only at he ⊢
        cases n with
        | zero =>
          have h0 := frontsOf_zero ft l s' _ _ e' he
          refine ⟨_, b, cols, k, rfl, rfl, ?_, ?_⟩
          · simpa [rnds] using hlen
          · rw [h0]
            simpa [rnds] using hst
        | succ n =>
          obtain ⟨e, b₁, cols', m, g1, g2, g3, g4⟩ := frontsOf_step ft l s' _ _ n e' he
          have hd : rs.drop (rnds ((b :: l).take (n + 1))) =
              (rs.drop b.rounds.length).drop (rnds (l.take n)) := by
            rw [List.take_succ_cons, show b :: l.take n = [b] ++ l.take n from rfl, rnds_append,
              List.drop_drop]
            simp [rnds]
          refine ⟨e, b₁, cols', m, ?_, ?_, ?_, ?_⟩
          · rw [List.getElem?_cons_succ]
            exact g1
          · rw [List.getElem?_cons_succ]
            exact g2
          · rw [hd]
            exact g3
          · rw [hd]
            exact g4

/-- A walk lays each round with the challenge that it is handed. -/
theorem walk_drawn (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' →
    z'.laid.map (·.drawn) = z.laid.map (·.drawn) ++ ds
  | [], [], z, z', h => by
    simp only [walk] at h
    cases h
    rw [List.append_nil]
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | s :: ss, d :: ds, z, z', h => by
    obtain ⟨x, z₁, -, hz, hw⟩ := walk_cons_ok h
    rw [walk_drawn L ss ds z₁ z' hw, heard_laid hz, List.map_append, List.append_assoc]
    rfl

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B}

/-- **The state in front of the member behind K is what member K's step returned.** -/
theorem quiet_in_event {ρ : Draws} {r : RunC F} (h : runC F B H w₀ rc x c ρ = .ok r) {K : Nat}
    {b : Block F.S₁ F.Cl} (hb : F.first.blocksInOrder[K]? = some b) (h1 : b.rounds.length = 1)
    {e' : Place × F.S₁ × List Fmt.Drawn}
    (he' : (frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      (withEmptySealRound r.run.views.1).opened)[K + 1]? = some e') :
    ∃ (zs : F.XiPub × F.S₁) (r₀ : Fmt.RoundView) (cols : List OpenedColumn) (m : Nat),
      frontAt F B H w₀ rc x c K ρ = some zs ∧
      ρ.first[rnds (F.first.blocksInOrder.take K)]? = some r₀.drawn ∧
      b.step 0 zs.2 [r₀] cols = .ok (e'.2.1, m) := by
  obtain ⟨e, b', cols, m, g1, g2, g3, g4⟩ := frontsOf_step 0 _ _ _ _ K e' he'
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans g2)
  rw [h1] at g3 g4
  obtain ⟨r₀, hr₀⟩ := List.length_eq_one_iff.1 g3
  rw [hr₀] at g4
  have hat : (withEmptySealRound r.run.views.1).rounds[rnds (F.first.blocksInOrder.take K)]? = some r₀ := by
    have e0 := congrArg (fun t => t[0]?) hr₀
    simpa [List.getElem?_take, List.getElem?_drop] using e0
  have hdr : (withEmptySealRound r.run.views.1).rounds.map (·.drawn) = ρ.first := by
    obtain ⟨R, a₁, z₁, _, _, _, _, -, ha₁, hz₁, hq, -, -, -, -, rfl⟩ := runC_parts h
    obtain ⟨-, -, t3⟩ := start_tied _ _ _ _ ha₁
    have w := walk_drawn _ _ _ _ _ hz₁
    rw [t3, List.map_nil, List.nil_append] at w
    show ((roundsOf z₁.laid).dropLast ++ ([⟨[], ⟨[], [], [], none⟩⟩] : List Fmt.RoundView)).map
      (·.drawn) = ρ.first
    rw [seal_back hq, ← w]
    unfold roundsOf
    rw [List.map_map]
    rfl
  refine ⟨(F.pub x, e.2.1), r₀, cols, m, ?_, ?_, g4⟩
  · unfold frontAt
    rw [h]
    show ((frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      (withEmptySealRound r.run.views.1).opened)[K]?).map (fun e => (F.pub x, e.2.1)) = _
    rw [g1]
    rfl
  · rw [← hdr, List.getElem?_map, hat]
    rfl

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.frontsOf_step
#print axioms ProofFile.Honest.K8.walk_drawn
#print axioms ProofFile.Honest.K8.quiet_in_event
#print axioms ProofFile.Honest.K8.frontsOf_zero
