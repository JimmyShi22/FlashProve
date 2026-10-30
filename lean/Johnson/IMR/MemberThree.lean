-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberThree.lean: ALL THREE CHAINS' STATES AT EVERY BORDER, AND THE
SECOND CHAIN's START AT THE TWO CHAINS' LAST STATES, WHEREVER THE RUN ACCEPTS:
the like of Johnson/IMR/MemberFold.lean for the shared and the second chain. THAT start₃ RETURNS
IS
SHOWN ALREADY: FileDescription.run_ok (Johnson/Desc/RunLaws.lean), an "if and only if", has it with
chainAt; start3_of_run says it with the three folds.

  start3_of_run    general in the description: where F.run accepts at x, v₁, v₂, v₃: the words of v₂
                   and v₃ pass the test; there are e₁, e₂, s₃, e₃: the first chain's fold at v₁
                   (with the seal's empty round behind) returns e₁, the shared chain's fold at v₂
                   returns e₂, each with nothing left over; F.start₃ (F.pub x) e₁ e₂ returns s₃;
                   the second chain's fold from s₃ at v₃ returns e₃ with nothing left over; the
                   last test passes at e₁, e₂, e₃.
  chain_states     general: a fold that returns with nothing left over, at words that pass: its
                   state at every border, by the fold over the first k entries (over the
                   sub-protocols and over the wrapped ones alike); each entry steps, wrapped, to
                   the next state; each state is reached at its border in the narrower sense.
  three_of_run     general in the description: where F.run accepts: three lists of states st₁, st₂,
                   st₃, each its chain's fold's states at its own view; start₃ at the first two
                   chains' last states returns st₃ 0; each state is reached at its border, IN THE
                   LETTERS OF THE THREE FAMILIES as far as Reach goes (see below).
  fileOf           the description written out at an opening's letters (Open.desc's term).
  member_three     from the goals' scope test at the public files and the proof file's decision
                   behind its gate: an opening, the run st of Johnson/IMR/MemberRun.lean for the
                     first
                   chain, and st₂, st₃ for the shared and the second chain at the description
                   written out at the opening's letters, WITH THE FIRST CHAIN's LAST STATE NAMED:
                   st 358.

AGAINST THE FAMILIES (Johnson/Top/H0/Walk/ReachThree.lean; NOT IMPORTED: over
files not in this file's build), BY READING: EndAt₁ F (p, s₁) is the first chain's
clause at its last border · RchAt₂ F k (((p, s₁), s₂), y) is the shared chain's clause at k with
EndAt₁: to the letter, by unfolding · RchAt₃ speaks through ReachR, "reached with the first state as
a relation" (fun p s => F.start₃ p.1 p.2.1 p.2.2 = .ok s): here the second chain's clause is Reach
at the constant first state st₃ 0, with the equation F.start₃ … = .ok (st₃ 0) beside it: THE STEP
FROM THESE TWO TO ReachR IS NOT TYPED HERE (an induction of some six lines where ReachR can be
imported).

WHAT IS NOT SAID. That the two tests say yes anywhere. "No mark", or anything else, of the shared or
the second chain's states. What these chains decide. How many entries their flat lists have. All
that Johnson/IMR/MemberFold.lean does not say. No soundness.
-/
import Johnson.IMR.MemberRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-- **Where a description's run accepts**: the three folds return with nothing left over, and the
second chain's start returns at the first two chains' last states. -/
theorem start3_of_run {Xi : Type} {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) :
    viewWordsBelowPrime v₁ = true ∧ viewWordsBelowPrime v₂ = true ∧ viewWordsBelowPrime v₃ = true ∧
    ∃ (e₁ : F.S₁) (e₂ : F.S₂) (s₃ e₃ : F.S₃),
      foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v₁).rounds
        (withEmptySealRound v₁).opened = .ok (e₁, [], []) ∧
      foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) v₂.rounds v₂.opened = .ok (e₂, [], []) ∧
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
      foldBlocks F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ v₃.rounds v₃.opened = .ok (e₃, [], []) ∧
      F.fin x e₁ e₂ e₃ = true := by
  obtain ⟨e₁, e₂, e₃, -, -, w₁, w₂, w₃, j₁, j₂, ⟨s₃, j₀, j₃⟩, jf⟩ := (F.run_ok x v₁ v₂ v₃).1 h
  exact ⟨w₁, w₂, w₃, e₁, e₂, s₃, e₃, Keeps.chainAt_fold _ _ _ _ _ _ j₁,
    Keeps.chainAt_fold _ _ _ _ _ _ j₂, j₀, Keeps.chainAt_fold _ _ _ _ _ _ j₃, jf⟩

/-- **A fold that returns with nothing left over, at words that pass the test: its state at every
border.** -/
theorem chain_states {T C Q : Type} {ft : ℕ} {bs : List (Block T C)} {start : Q → T} {z : Q}
    {rs : List Fmt.RoundView} {cs : List OpenedColumn} {e : T} (hw : viewWordsBelowPrime ⟨rs, cs⟩ = true)
    (h : foldBlocks ft bs (start z) rs cs = .ok (e, [], [])) :
    ∃ st : ℕ → T, st 0 = start z ∧ st bs.length = e ∧
      (∀ k ≤ bs.length, ∃ r q, foldBlocks ft (bs.take k) (start z) rs cs = .ok (st k, r, q) ∧
        foldBlocks ft ((bs.map Sound.below).take k) (start z) rs cs = .ok (st k, r, q)) ∧
      (∀ k < bs.length, ∃ b, bs[k]? = some b ∧ StepYes ft (Sound.below b) (st k) (st (k + 1))) ∧
      ∀ k ≤ bs.length, Reach ft (bs.map Sound.below) start k (z, st k) := by
  have hf := fold_below_of hw h
  have hpre := fold_prefix hf
  have hlenB : (bs.map Sound.below).length = bs.length := List.length_map _
  have h0 : stateAt ft (bs.map Sound.below) (start z) rs cs 0 = start z := by
    refine stateAt_ok (r := rs) (c := cs) ?_
    rw [List.take_zero]
    unfold foldBlocks
    rfl
  have hend : stateAt ft (bs.map Sound.below) (start z) rs cs bs.length = e := by
    refine stateAt_ok (r := []) (c := []) ?_
    rw [List.take_of_length_le (Nat.le_of_eq hlenB)]
    exact hf
  have hsB : ∀ k < bs.length, ∃ b', (bs.map Sound.below)[k]? = some b' ∧ StepYes ft b'
      (stateAt ft (bs.map Sound.below) (start z) rs cs k)
      (stateAt ft (bs.map Sound.below) (start z) rs cs (k + 1)) := by
    intro k hk
    obtain ⟨r, q, g0⟩ := hpre k
    obtain ⟨r', q', g1⟩ := hpre (k + 1)
    have hb : (bs.map Sound.below)[k]? = some (bs.map Sound.below)[k] :=
      List.getElem?_eq_getElem (by rw [hlenB]; exact hk)
    exact ⟨_, hb, fold_step hb g0 g1⟩
  refine ⟨_, h0, hend, ?_, ?_, reach_of_path h0 hsB⟩
  · intro k _
    obtain ⟨r, q, g⟩ := hpre k
    refine ⟨r, q, ?_, g⟩
    rw [← List.map_take] at g
    exact fold_raw ft _ _ _ _ _ g
  · intro k hk
    obtain ⟨b', hb', hy⟩ := hsB k hk
    rw [List.getElem?_map] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
    exact ⟨b, hb, hy⟩

/-- **Where a description's run accepts: three lists of states**, each its chain's fold's states at
its own view; the second chain's start returns st₃ 0 at the first two chains' last states. -/
theorem three_of_run {Xi : Type} {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) :
    ∃ (st₁ : ℕ → F.S₁) (st₂ : ℕ → F.S₂) (st₃ : ℕ → F.S₃),
      st₁ 0 = F.start₁ (F.pub x) ∧ st₂ 0 = F.start₂ (F.pub x) ∧
      F.start₃ (F.pub x) (st₁ F.first.blocksInOrder.length) (st₂ F.shared.blocksInOrder.length) = .ok (st₃ 0) ∧
      (∀ k ≤ F.first.blocksInOrder.length,
        Reach 0 (F.first.blocksInOrder.map Sound.below) F.start₁ k (F.pub x, st₁ k) ∧
        ∃ r q, foldBlocks 0 (F.first.blocksInOrder.take k) (F.start₁ (F.pub x)) (withEmptySealRound v₁).rounds
          (withEmptySealRound v₁).opened = .ok (st₁ k, r, q)) ∧
      (∀ k ≤ F.shared.blocksInOrder.length,
        Reach 0 (F.shared.blocksInOrder.map Sound.below) (fun p : F.XiPub × F.S₁ => F.start₂ p.1) k
          ((F.pub x, st₁ F.first.blocksInOrder.length), st₂ k) ∧
        ∃ r q, foldBlocks 0 (F.shared.blocksInOrder.take k) (F.start₂ (F.pub x)) v₂.rounds v₂.opened =
          .ok (st₂ k, r, q)) ∧
      (∀ k ≤ F.second.blocksInOrder.length,
        Reach F.lastChainFirstTreeNumber (F.second.blocksInOrder.map Sound.below)
          (fun _ : F.XiPub × F.S₁ × F.S₂ => st₃ 0) k
          ((F.pub x, st₁ F.first.blocksInOrder.length, st₂ F.shared.blocksInOrder.length), st₃ k) ∧
        ∃ r q, foldBlocks F.lastChainFirstTreeNumber (F.second.blocksInOrder.take k) (st₃ 0) v₃.rounds v₃.opened =
          .ok (st₃ k, r, q)) ∧
      F.fin x (st₁ F.first.blocksInOrder.length) (st₂ F.shared.blocksInOrder.length)
        (st₃ F.second.blocksInOrder.length) = true := by
  obtain ⟨w₁, w₂, w₃, e₁, e₂, s₃, e₃, f₁, f₂, h₃, f₃, hfin⟩ := start3_of_run h
  obtain ⟨st₁, a0, a1, a2, -, a4⟩ := chain_states (start := F.start₁) (z := F.pub x)
    (okViewW_seal v₁ w₁) f₁
  obtain ⟨st₂, b0, b1, b2, -, b4⟩ := chain_states
    (start := fun p : F.XiPub × F.S₁ => F.start₂ p.1) (z := (F.pub x, e₁)) (rs := v₂.rounds)
    (cs := v₂.opened) w₂ f₂
  obtain ⟨st₃, c0, c1, c2, -, c4⟩ := chain_states
    (start := fun _ : F.XiPub × F.S₁ × F.S₂ => s₃) (z := (F.pub x, e₁, e₂)) (rs := v₃.rounds)
    (cs := v₃.opened) w₃ f₃
  have c0' : st₃ 0 = s₃ := c0
  subst a1 b1 c1
  rw [← c0'] at h₃ c2 c4
  exact ⟨st₁, st₂, st₃, a0, b0, h₃,
    fun k hk => ⟨a4 k hk, by obtain ⟨r, q, g, -⟩ := a2 k hk; exact ⟨r, q, g⟩⟩,
    fun k hk => ⟨b4 k hk, by obtain ⟨r, q, g, -⟩ := b2 k hk; exact ⟨r, q, g⟩⟩,
    fun k hk => ⟨c4 k hk, by obtain ⟨r, q, g, -⟩ := c2 k hk; exact ⟨r, q, g⟩⟩, hfin⟩

/-- The proof file's description, written out at an opening's letters (Open.desc: F is this
term). The same term as IM.descOf (TokAtReach.lean) and Meaning.Carry.fileAt
(BaseIsRoots.lean), neither of which our build held. -/
abbrev fileOf (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- **All three chains' states, from the two tests on verify()'s own road**, with the first chain's
last state named: st 358 of the run. -/
theorem member_three {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (st : ℕ → S)
      (st₂ : ℕ → (fileOf Z A B c).S₂) (st₃ : ℕ → (fileOf Z A B c).S₃),
      VerifierAndGoals.readFiles P = .ok pp ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL (fileOf Z A B c) Z Bs base c A B ∧
      RunAt Z c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st ∧
      st₂ 0 = (fileOf Z A B c).start₂ (LPFD.Full.instanceAsPlainRecord z).pub ∧
      (fileOf Z A B c).start₃ (LPFD.Full.instanceAsPlainRecord z).pub (st 358)
        (st₂ (fileOf Z A B c).shared.blocksInOrder.length) = .ok (st₃ 0) ∧
      (∀ k ≤ (fileOf Z A B c).shared.blocksInOrder.length,
        Reach 0 ((fileOf Z A B c).shared.blocksInOrder.map Sound.below)
          (fun p : (fileOf Z A B c).XiPub × (fileOf Z A B c).S₁ => (fileOf Z A B c).start₂ p.1) k
          (((LPFD.Full.instanceAsPlainRecord z).pub, st 358), st₂ k) ∧
        ∃ r q, foldBlocks 0 ((fileOf Z A B c).shared.blocksInOrder.take k)
          ((fileOf Z A B c).start₂ (LPFD.Full.instanceAsPlainRecord z).pub) v₂.rounds v₂.opened =
          .ok (st₂ k, r, q)) ∧
      (∀ k ≤ (fileOf Z A B c).second.blocksInOrder.length,
        Reach (fileOf Z A B c).lastChainFirstTreeNumber ((fileOf Z A B c).second.blocksInOrder.map Sound.below)
          (fun _ : (fileOf Z A B c).XiPub × (fileOf Z A B c).S₁ × (fileOf Z A B c).S₂ => st₃ 0) k
          (((LPFD.Full.instanceAsPlainRecord z).pub, st 358, st₂ (fileOf Z A B c).shared.blocksInOrder.length), st₃ k) ∧
        ∃ r q, foldBlocks (fileOf Z A B c).lastChainFirstTreeNumber ((fileOf Z A B c).second.blocksInOrder.take k)
          (st₃ 0) v₃.rounds v₃.opened = .ok (st₃ k, r, q)) ∧
      (fileOf Z A B c).fin (LPFD.Full.instanceAsPlainRecord z) (st 358)
        (st₂ (fileOf Z A B c).shared.blocksInOrder.length)
        (st₃ (fileOf Z A B c).second.blocksInOrder.length) = true := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, st, hR, O, hr, hp, hlen, -, h0, hw, hf, -, hall, -⟩ :=
    member_fold hS hg
  have eF := O.desc
  subst eF
  have Rn : RunAt Z c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st :=
    ⟨hp, hlen, h0, hw, fun k hk => by obtain ⟨r, q, g, -⟩ := hf k hk; exact ⟨r, q, g⟩,
      fun k hk => (hall k hk).1, fun k hk => (hall k hk).2.1, fun k hk => (hall k hk).2.2⟩
  obtain ⟨-, w₂, w₃, e₁, e₂, s₃, e₃, f₁, f₂, h₃, f₃, hfin⟩ :=
    start3_of_run (F := fileOf Z A B c) hr
  have f₁' : foldBlocks 0 c.blocksInOrder (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub) (withEmptySealRound v₁).rounds
      (withEmptySealRound v₁).opened = .ok (e₁, [], []) := f₁
  rw [hw] at f₁'
  obtain rfl : st 358 = e₁ := congrArg Prod.fst (Except.ok.inj f₁')
  obtain ⟨st₂, b0, b1, b2, -, b4⟩ := chain_states
    (start := fun p : (fileOf Z A B c).XiPub × (fileOf Z A B c).S₁ => (fileOf Z A B c).start₂ p.1)
    (z := ((LPFD.Full.instanceAsPlainRecord z).pub, st 358)) (rs := v₂.rounds) (cs := v₂.opened) w₂ f₂
  obtain ⟨st₃, c0, c1, c2, -, c4⟩ := chain_states
    (start := fun _ : (fileOf Z A B c).XiPub × (fileOf Z A B c).S₁ × (fileOf Z A B c).S₂ => s₃)
    (z := ((LPFD.Full.instanceAsPlainRecord z).pub, st 358, e₂)) (rs := v₃.rounds) (cs := v₃.opened) w₃ f₃
  have c0' : st₃ 0 = s₃ := c0
  subst b1 c1
  rw [← c0'] at h₃ c2 c4
  exact ⟨pp, Z, Bs, base, c, A, B, st, st₂, st₃, hR, O, Rn, b0, h₃,
    fun k hk => ⟨b4 k hk, by obtain ⟨r, q, g, -⟩ := b2 k hk; exact ⟨r, q, g⟩⟩,
    fun k hk => ⟨c4 k hk, by obtain ⟨r, q, g, -⟩ := c2 k hk; exact ⟨r, q, g⟩⟩, hfin⟩

#print axioms start3_of_run
#print axioms chain_states
#print axioms three_of_run
#print axioms member_three

end IM
