-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunC.lean: for a whole file, the verdict that `runC`
(Honest/Walk.lean) reaches on what it has produced is the verifier's `foldBlocks` on the views.
Where `runC` returns, the three states that it holds at the chains' ends are the results of the
verifier's own `foldBlocks` (Johnson/Desc/Block.lean) at the run's three views, the first with its
sealing round put back; a state is `none` exactly where `foldBlocks`, or the second chain's start,
rejects (`runC_ends`). So the description accepts these views if and only if its tests on the plan,
the instance and the words pass, none of the three ends is `none`, and the last test accepts them
(`runC_yes_iff`). The lemmas are general in the description, the book and the prover.

  1  `settle_both`, `heard_both`, `walk_both`, `start_both`   the prover's run and the verifier's
     state are there together, or neither is
  2  `fold_some`   the result of `foldBlocks`, with nothing left over
  3  `ChainEnd`, `chain_end`   one chain
  4  `runC_ends`, `runC_yes_iff`   the file

Limits.
  * Nothing is said on whether `runC` returns.
  * The lemmas on `ChainProgress.start` are general in its fifth argument `front`, the earlier chains'
    columns that this chain's parts are handed; no end reads it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.WalkFold
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi W Y W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 Together, or neither -/

theorem settle_both (L : Lay) : ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y),
    z.mid.isSome = z.ver.isSome → ChainProgress.settle L todo z = .ok z' → z'.mid.isSome = z'.ver.isSome
  | [], z, z', h, hs => by
    simp only [ChainProgress.settle] at hs
    cases hs
    exact h
  | b :: t, z, z', h, hs => by
    by_cases hlt : z.own.length < b.rounds.length
    · rw [settle_wait L b t z hlt] at hs
      cases hs
      exact h
    · obtain ⟨cols, -, hs'⟩ := settle_ask_ok hlt hs
      refine settle_both L t _ z' ?_ hs'
      show (if (z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols).isSome
        then z.mid.map (·.took cols) else none).isSome =
          (z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols).isSome
      cases hv : z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols with
      | none => rfl
      | some e =>
        show (z.mid.map (·.took cols)).isSome = true
        rw [Option.isSome_map, h]
        cases hz : z.ver with
        | none =>
          rw [hz] at hv
          cases hv
        | some _ => rfl

theorem heard_both (L : Lay) {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    (h : z.mid.isSome = z.ver.isSome) (hz : z.heard L s x d = .ok z') :
    z'.mid.isSome = z'.ver.isSome := by
  obtain ⟨m', hm, hs⟩ := heard_ok hz
  refine settle_both L z.todo _ z' ?_ hs
  show m'.isSome = z.ver.isSome
  rw [← h]
  cases hmid : z.mid with
  | none =>
    rw [hmid] at hm
    cases hm
    rfl
  | some a =>
    rw [hmid] at hm
    obtain ⟨y, -, rfl⟩ := exMap_ok hm
    rfl

theorem walk_both (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), z.mid.isSome = z.ver.isSome → walk L ss ds z = .ok z' →
    z'.mid.isSome = z'.ver.isSome
  | [], [], z, z', h, hw => by
    rw [walk_nil_ok hw]
    exact h
  | [], _ :: _, _, _, _, hw => by simp [walk] at hw
  | _ :: _, [], _, _, _, hw => by simp [walk] at hw
  | s :: ss, d :: ds, z, z', h, hw => by
    obtain ⟨x, z₁, -, h1, h2⟩ := walk_cons_ok hw
    exact walk_both L ss ds z₁ z' (heard_both L h h1) h2

theorem start_both (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a : ChainProgress S Cl W Y} {front : List OpenedColumn} (h : ChainProgress.start L bs m v front = .ok a)
    : a.mid.isSome = a.ver.isSome := by
  unfold ChainProgress.start at h
  refine settle_both L bs _ a ?_ h
  show (if v.isSome then m.map ({ · with opened := some front }) else none).isSome =
    (if m.isSome then v else none).isSome
  cases m <;> cases v <;> rfl

/-! ## 2 The result of `foldBlocks` -/

/-- Over exactly its own rounds and the columns that they read: the result of `foldBlocks` is e if
and only if `foldBlocks` accepts there with nothing left over. -/
theorem fold_some (ft : Nat) (l : List (Block S Cl)) (s e : S) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (hR : R.length = (l.flatMap (·.rounds)).length) (hC : C.length = owed ft l R) :
    (foldBlocks ft l s R C).toOption.map (·.1) = some e ↔
      foldBlocks ft l s R C = .ok (e, [], []) := by
  constructor
  · intro h
    cases hf : foldBlocks ft l s R C with
    | error w =>
      rw [hf] at h
      cases h
    | ok z =>
      rw [hf] at h
      have h1 : z.1 = e := Option.some.inj h
      obtain ⟨h2, h3⟩ := fold_exact ft l s R C z hf hR hC
      obtain ⟨a, b, c⟩ := z
      cases h1
      cases h2
      cases h3
      rfl
  · intro h
    rw [h]
    rfl

/-! ## 3 One chain -/

/-- What holds at the end of a chain's walk. `v`: the verifier's state at the chain's start, or
`none`. -/
def ChainEnd (ft : Nat) (bs : List (Block S Cl)) (v : Option S) (z : ChainProgress S Cl W Y) : Prop :=
  (roundsOf z.laid).length = (bs.flatMap (·.rounds)).length ∧
    z.cols.length = owed ft bs (roundsOf z.laid) ∧ z.mid.isSome = z.ver.isSome ∧
    z.ver = v.bind fun s => (foldBlocks ft bs s (roundsOf z.laid) z.cols).toOption.map (·.1)

theorem chain_end (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hl : ss.map (·.decl) = bs.flatMap (·.rounds)) (hm : v.isSome = true → m.isSome = true) :
    ChainEnd L.firstTree bs v z := by
  have hl' : ss.length = (bs.flatMap (·.rounds)).length := by
    rw [← hl, List.length_map]
  obtain ⟨-, -, h3, h4, h5⟩ := walk_fold L bs m v ha hz hl'
  refine ⟨by rw [roundsOf_length, h3, hl'], h4, walk_both L ss ds a z (start_both L bs m v ha) hz,
    ?_⟩
  rw [h5]
  cases hv : v with
  | none => cases m <;> rfl
  | some s =>
    have h6 := hm (by rw [hv]; rfl)
    rw [h6]
    rfl

/-! ## 4 The file -/

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F}

/-- **The verdict of `runC` on what it has produced is the verifier's `foldBlocks` on the views.**
With the counts by which `foldBlocks` leaves nothing over. -/
theorem runC_ends (h : runC F B H w₀ rc x c ρ = .ok r) :
    ((withEmptySealRound r.run.views.1).rounds.length = (F.first.blocksInOrder.flatMap (·.rounds)).length ∧
      r.run.views.1.opened.length = owed 0 F.first.blocksInOrder (withEmptySealRound r.run.views.1).rounds ∧
      r.ends.1 = (foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
        r.run.views.1.opened).toOption.map (·.1)) ∧
    (r.run.views.2.1.rounds.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length ∧
      r.run.views.2.1.opened.length = owed 0 F.shared.blocksInOrder r.run.views.2.1.rounds ∧
      r.ends.2.1 = (foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1.rounds
        r.run.views.2.1.opened).toOption.map (·.1)) ∧
    (r.run.views.2.2.rounds.length = (F.second.blocksInOrder.flatMap (·.rounds)).length ∧
      r.run.views.2.2.opened.length = owed F.lastChainFirstTreeNumber F.second.blocksInOrder r.run.views.2.2.rounds ∧
      r.ends.2.2 = (door₃ F x r.ends.1 r.ends.2.1).bind fun s₃ =>
        (foldBlocks F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ r.run.views.2.2.rounds
          r.run.views.2.2.opened).toOption.map (·.1)) := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts h
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3, p4⟩ := chain_end _ F.first.blocksInOrder _ _ ha₁ hz₁ (steps_decl s1) fun _ => rfl
  obtain ⟨q1, q2, q3, q4⟩ := chain_end _ F.shared.blocksInOrder _ _ ha₂ hz₂ (steps_decl s2) fun _ => rfl
  obtain ⟨t1, t2, -, t4⟩ := chain_end _ F.second.blocksInOrder _ _ ha₃ hz₃ (steps_decl s3) (by
             intro hd
             cases hv₁ : z₁.ver with
             | none =>
               rw [hv₁] at hd
               cases hd
             | some e₁ =>
               cases hv₂ : z₂.ver with
               | none =>
                 rw [hv₁, hv₂] at hd
                 cases hd
               | some e₂ =>
                 rw [hv₁] at p3
                 rw [hv₂] at q3
                 obtain ⟨m₁, hm₁⟩ := Option.isSome_iff_exists.1 p3
                 obtain ⟨m₂, hm₂⟩ := Option.isSome_iff_exists.1 q3
                 rw [hm₁, hm₂]
                 rfl)
  have hs := seal_back hq
  refine ⟨⟨?_, ?_, ?_⟩, ⟨q1, q2, q4⟩, ⟨t1, t2, t4⟩⟩
  · show ((roundsOf z₁.laid).dropLast ++ ([⟨[], ⟨[], [], [], none⟩⟩] : List Fmt.RoundView)).length = _
    rw [hs]
    exact p1
  · show z₁.cols.length = owed 0 F.first.blocksInOrder
      ((roundsOf z₁.laid).dropLast ++ ([⟨[], ⟨[], [], [], none⟩⟩] : List Fmt.RoundView))
    rw [hs]
    exact p2
  · show z₁.ver = (foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x))
      ((roundsOf z₁.laid).dropLast ++ ([⟨[], ⟨[], [], [], none⟩⟩] : List Fmt.RoundView))
      z₁.cols).toOption.map (·.1)
    rw [hs]
    exact p4

/-- **What the description's acceptance of the views of `runC` consists of.** -/
theorem runC_yes_iff (h : runC F B H w₀ rc x c ρ = .ok r) :
    F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true ↔
      F.planOk = true ∧ F.okStart x = true ∧ viewWordsBelowPrime r.run.views.1 = true ∧
        viewWordsBelowPrime r.run.views.2.1 = true ∧ viewWordsBelowPrime r.run.views.2.2 = true ∧
        ∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃) ∧ F.fin x e₁ e₂ e₃ = true := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := runC_ends h
  rw [FileDescription.run_ok]
  constructor
  · rintro ⟨e₁, e₂, e₃, hp, ho, w1, w2, w3, k1, k2, ⟨s₃, hs, k3⟩, hf⟩
    have f1 := (fold_some 0 _ _ e₁ _ _ a1 a2).2 (chainAt_ok.1 k1).2
    have f2 := (fold_some 0 _ _ e₂ _ _ b1 b2).2 (chainAt_ok.1 k2).2
    have f3 := (fold_some _ _ s₃ e₃ _ _ c1 c2).2 (chainAt_ok.1 k3).2
    rw [← a3] at f1
    rw [← b3] at f2
    have hd : door₃ F x r.ends.1 r.ends.2.1 = some s₃ := by
      rw [f1, f2]
      show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
      rw [hs]
      rfl
    rw [hd] at c3
    have f3' : r.ends.2.2 = some e₃ := c3.trans f3
    exact ⟨hp, ho, w1, w2, w3, e₁, e₂, e₃, Prod.ext f1 (Prod.ext f2 f3'), hf⟩
  · rintro ⟨hp, ho, w1, w2, w3, e₁, e₂, e₃, he, hf⟩
    have f1 : r.ends.1 = some e₁ := congrArg (·.1) he
    have f2 : r.ends.2.1 = some e₂ := congrArg (·.2.1) he
    have f3 : r.ends.2.2 = some e₃ := congrArg (·.2.2) he
    rw [f1] at a3
    rw [f2] at b3
    rw [f1, f2, f3] at c3
    cases hs : F.start₃ (F.pub x) e₁ e₂ with
    | error w =>
      have hd : door₃ F x (some e₁) (some e₂) = none := by
        show (F.start₃ (F.pub x) e₁ e₂).toOption = none
        rw [hs]
        rfl
      rw [hd] at c3
      cases c3
    | ok s₃ =>
      have hd : door₃ F x (some e₁) (some e₂) = some s₃ := by
        show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
        rw [hs]
        rfl
      rw [hd] at c3
      exact ⟨e₁, e₂, e₃, hp, ho, w1, w2, w3,
        chainAt_ok.2 ⟨flat_isEmpty _, (fold_some 0 _ _ e₁ _ _ a1 a2).1 a3.symm⟩,
        chainAt_ok.2 ⟨flat_isEmpty _, (fold_some 0 _ _ e₂ _ _ b1 b2).1 b3.symm⟩,
        ⟨s₃, hs, chainAt_ok.2 ⟨flat_isEmpty _, (fold_some _ _ s₃ e₃ _ _ c1 c2).1 c3.symm⟩⟩, hf⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.settle_both
#print axioms ProofFile.Honest.heard_both
#print axioms ProofFile.Honest.walk_both
#print axioms ProofFile.Honest.start_both
#print axioms ProofFile.Honest.fold_some
#print axioms ProofFile.Honest.chain_end
#print axioms ProofFile.Honest.runC_ends
#print axioms ProofFile.Honest.runC_yes_iff
#print axioms ProofFile.Honest.ChainEnd
