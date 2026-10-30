-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberFold.lean: ONE FOLD AT THE PROOF FILE's OWN VIEW, AND ITS
STATE AT EVERY BORDER: from the same two tests as Johnson/IMR/MemberOfGate.lean (the goals' scope
test at the
public files; the proof file's decision behind its gate): with R and C the list of rounds and the
opened columns of the first view v₁ (with the seal's empty round behind): there is a list st 0, …,
st 358 of values of the verifier's state such that the fold over the first k entries of the flat
list of the first chain of the IOP as written in Lean, from the first state at the instance's own
public part, AT THAT R AND C, returns st k: at every k ≤ 358, over the sub-protocols themselves and
over the wrapped ones (Sound.below) alike; each entry steps, wrapped, from st k to st (k + 1); st k
is reached at border k, narrower and wider; no st k bears a mark.

WHAT IT IS FOR. Rows that are stated at a fold, and above all rows that speak of SEVERAL borders of
ONE fold (the same R and C at each): Johnson/IMR/MemberPath.lean's list cannot serve these, for a
step there
binds its rounds and columns each apart. HERE THE STATES ARE THOSE OF ONE FOLD AT THE GATE's OWN
FIRST VIEW v₁: the description's run accepts at z, v₁, v₂, v₃ (a clause), the fold over the whole
flat list at v₁'s rounds and columns returns st 358 with nothing left over (a clause), and the fold
over the first k entries at the same rounds and columns returns st k (a clause).

Compiled with the whole library.



  step_raw | fold_raw   a wrapped step, a fold over the wrapped sub-protocols, that returns: the
                   sub-protocols' own returns the same (off step_below).
  stateAt          the state behind the first k entries, where the fold over them returns.
  fold_prefix      where a fold returns, the fold over the first k entries returns, at the same
                   list of rounds and columns.
  fold_step        the states behind k and k + 1 entries of one fold: entry k steps from the one to
                   the other.
  view_of_run      at an opening, at every o: where F.run accepts: the fold over the wrapped flat
                   list at the first view returns, with nothing left over, a state that passes
                   S.fin and S.finAsked. (Some twenty lines stand here a second time: end_of_run,
                   Johnson/IMR/MemberOfGate.lean, has them and hides the fold.)
  member_fold      THE TOP.

NEAREST RELATIVES, all on a wider ground, at the state's type S alone, and none imported: of
fold_prefix: fold_cut_le (Johnson/IMR/AtReach.lean) and fold_cut (Johnson/IMR/GroupRest.lean): the
fold over the first
j entries returns SOME state; of fold_step: fold_last (Johnson/IMR/SendsFold.lean): one step of the
fold, cut
off at its end. None names the state as a function of the border or goes between the wrapped list
and the raw.

OBJECT, USER: as in Johnson/IMR/MemberOfGate.lean. LETTERS: P, z, v₁, v₂, v₃: free; pp by its equation; F,
Z, Bs, base, c, A, B pinned by Open (Open.unique); st: PINNED at every k ≤ 358 by the fold's
equation, free beyond; r, q: what the fold leaves over, pinned by it too.

WHAT IS NOT SAID. All that Johnson/IMR/MemberOfGate.lean and Johnson/IMR/MemberPath.lean do not say,
but that the
states are one fold's at one list of rounds and columns: that is said here. That the view v₁ is what
a parser makes of a proof file's bytes: v₁ is a free letter, bound by the gate's accepting alone.
Nothing of v₂, v₃ but that the run accepts at them. No soundness.


-/
import Johnson.IMR.MemberPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_raw stepYes_raw fold_split step_less)

section
variable {T C : Type}

/-- A wrapped step that returns: the sub-protocol's own step returns the same. -/
theorem step_raw {ft : ℕ} {b : Block T C} {s : T} {R : List Fmt.RoundView} {c : List OpenedColumn} {x : T × ℕ}
    (h : (Sound.below b).step ft s R c = .ok x) : b.step ft s R c = .ok x := by
  have q := Sound.step_below ft b s R c
  rw [h] at q
  by_cases hw : viewWordsBelowPrime ⟨R, c.take ((b.reads ft (R.map (·.drawn))).flatMap id).length⟩ = true
  · rw [if_pos hw] at q
    exact Sound.ok_of_some _ _ q.symm
  · rw [if_neg hw] at q
    cases q

/-- **A fold over the wrapped sub-protocols that returns: the fold over the sub-protocols themselves
returns the same.** -/
theorem fold_raw (ft : ℕ) : ∀ (bs : List (Block T C)) (s : T) (rs : List Fmt.RoundView) (cs : List OpenedColumn)
    (x : T × List Fmt.RoundView × List OpenedColumn), foldBlocks ft (bs.map Sound.below) s rs cs = .ok x →
    foldBlocks ft bs s rs cs = .ok x
  | [], _, _, _, _, h => h
  | b :: l, s, rs, cs, x, h => by
    obtain ⟨s', k, hl, hs, h'⟩ :=
      foldBlocks_cons ft (Sound.below b) (l.map Sound.below) s rs cs x h
    have hl' : (rs.take b.rounds.length).length = b.rounds.length := hl
    have hs' : b.step ft s (rs.take b.rounds.length) cs = .ok (s', k) := step_raw hs
    have h'' : foldBlocks ft (l.map Sound.below) s' (rs.drop b.rounds.length) (cs.drop k) =
      .ok x := h'
    unfold foldBlocks
    simp only [List.splitAt_eq, hl', ne_eq, not_true_eq_false, if_false, hs']
    exact fold_raw ft l s' _ _ x h''

/-- The state behind the first k entries, where the fold over them returns. -/
def stateAt (ft : ℕ) (bs : List (Block T C)) (s : T) (rs : List Fmt.RoundView) (cs : List OpenedColumn) (k : ℕ) :
    T :=
  match foldBlocks ft (bs.take k) s rs cs with
  | .ok x => x.1
  | .error _ => s

theorem stateAt_ok {ft : ℕ} {bs : List (Block T C)} {s t : T} {rs r : List Fmt.RoundView}
    {cs c : List OpenedColumn} {k : ℕ} (h : foldBlocks ft (bs.take k) s rs cs = .ok (t, r, c)) :
    stateAt ft bs s rs cs k = t := by
  unfold stateAt
  rw [h]

/-- Where a fold returns, the fold over the first k entries returns, at the same list of rounds and
columns. -/
theorem fold_prefix {ft : ℕ} {bs : List (Block T C)} {s : T} {rs : List Fmt.RoundView} {cs : List OpenedColumn}
    {x : T × List Fmt.RoundView × List OpenedColumn} (h : foldBlocks ft bs s rs cs = .ok x) (k : ℕ) :
    ∃ r c, foldBlocks ft (bs.take k) s rs cs = .ok (stateAt ft bs s rs cs k, r, c) := by
  rw [← List.take_append_drop k bs] at h
  obtain ⟨t, r, c, g, -⟩ := fold_split ft _ _ _ _ _ _ h
  exact ⟨r, c, by rw [stateAt_ok g]; exact g⟩

/-- The states behind k and k + 1 entries of one fold: entry k steps from the one to the other. -/
theorem fold_step {ft k : ℕ} {bs : List (Block T C)} {b : Block T C} (hb : bs[k]? = some b)
    {s t t' : T} {rs r r' : List Fmt.RoundView} {cs c c' : List OpenedColumn}
    (h0 : foldBlocks ft (bs.take k) s rs cs = .ok (t, r, c))
    (h1 : foldBlocks ft (bs.take (k + 1)) s rs cs = .ok (t', r', c')) : StepYes ft b t t' := by
  rw [List.take_add_one, hb] at h1
  obtain ⟨u, r₁, c₁, g1, g2⟩ := fold_split ft _ _ _ _ _ _ h1
  rw [h0] at g1
  cases g1
  obtain ⟨s', n, hl, hs, h3⟩ := foldBlocks_cons ft b [] t r c _ g2
  unfold foldBlocks at h3
  injection h3 with h3
  obtain ⟨rfl, _⟩ := Prod.mk.inj h3
  exact ⟨_, _, hl, step_less hs⟩

end

/-- **Where the run accepts, at an opening, at every o**: the fold over the wrapped flat list, from
the first state at the instance's own public part, at the first view's list of rounds (with the
seal's empty round behind) and opened columns, returns with nothing left over a state that passes
S.fin and S.finAsked at the asked reply. -/
theorem view_of_run {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : Open o pol lay KL F Z Bs base c A B)
    {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ e : S, foldBlocks 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
        (withEmptySealRound v₁).opened = .ok (e, [], []) ∧
      e.fin = true ∧ e.finAsked x.asked = true := by
  obtain ⟨-, w₁, e₁, e₂, e₃, s₃, hf, h₃, hfin⟩ := parts_of_run hr
  have eF := O.desc
  subst eF
  have hf' : foldBlocks 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
      (withEmptySealRound v₁).opened = .ok (e₁, [], []) := hf
  have hE : S.fin e₁ = true := by
    have h₃' : (if !(S.fin e₁) then (.error "the first chain does not stand at its end" :
        Except String B.σ) else
      match A.ended e₂ with
      | none => .error "the shared chain has not ended"
      | some e => B.start x.pub e₁ e) = .ok s₃ := h₃
    cases hq : S.fin e₁ with
    | true => rfl
    | false => rw [hq] at h₃'; cases h₃'
  have hA : S.finAsked x.asked e₁ = true := by
    have q : (S.finAsked x.asked e₁ && S.req e₁ == OnBytes.Model.Verify.words32 x.pub.request &&
      (A.ended e₂).isSome && B.done e₃) = true := hfin
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at q
    exact q.1.1.1
  exact ⟨e₁, fold_below_of (okViewW_seal v₁ w₁) hf', hE, hA⟩

/-- **ONE FOLD AT THE PROOF FILE's OWN VIEW, ITS STATE AT EVERY BORDER, NONE WITH A MARK, FROM THE
TWO TESTS ON verify()'s OWN ROAD.** -/
theorem member_fold {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
      (st : ℕ → S),
      VerifierAndGoals.readFiles P = .ok pp ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true ∧
      (∀ b ∈ c.blocksInOrder, b.planOk = true) ∧
      c.blocksInOrder.length = 358 ∧
      ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z (LPFD.Full.instanceAsPlainRecord z) = true ∧
      st 0 = ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub ∧
      foldBlocks 0 c.blocksInOrder (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub) (withEmptySealRound v₁).rounds
        (withEmptySealRound v₁).opened = .ok (st 358, [], []) ∧
      (∀ k ≤ 358, ∃ r q,
        foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
          (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened = .ok (st k, r, q) ∧
        foldBlocks 0 ((c.blocksInOrder.map Sound.below).take k) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
          (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened = .ok (st k, r, q)) ∧
      (∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧ StepYes 0 (Sound.below b) (st k) (st (k + 1))) ∧
      (∀ k ≤ 358,
        Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, st k) ∧
        Reach 0 c.blocksInOrder (ProofFile.startS Z) k ((LPFD.Full.instanceAsPlainRecord z).pub, st k) ∧
        (st k).failed = none) ∧
      (st 358).fin = true ∧ (st 358).finAsked (LPFD.Full.instanceAsPlainRecord z).asked = true ∧
      FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true ∧
      ∃ D, LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL =
        .ok (D, (F.pull LPFD.Full.instanceAsPlainRecord).run) := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, hR, -, O, hr, hp, hlen, -, hx, -, hlive, hlaid⟩ :=
    member_of_gate_laid hS hg
  obtain ⟨e, hf, hfin, hask⟩ := view_of_run O hr
  have hpre := fold_prefix hf
  have hlenB : (c.blocksInOrder.map Sound.below).length = 358 := by rw [List.length_map, hlen]
  have h0 : stateAt 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
      (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened 0 = ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub := by
    refine stateAt_ok (r := (withEmptySealRound v₁).rounds) (c := (withEmptySealRound v₁).opened) ?_
    rw [List.take_zero]
    unfold foldBlocks
    rfl
  have hend : stateAt 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
      (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened 358 = e := by
    refine stateAt_ok (r := []) (c := []) ?_
    rw [List.take_of_length_le (Nat.le_of_eq hlenB)]
    exact hf
  have hsB : ∀ k < 358, ∃ b', (c.blocksInOrder.map Sound.below)[k]? = some b' ∧ StepYes 0 b'
      (stateAt 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
        (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened k)
      (stateAt 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
        (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened (k + 1)) := by
    intro k hk
    obtain ⟨r, q, g0⟩ := hpre k
    obtain ⟨r', q', g1⟩ := hpre (k + 1)
    have hb : (c.blocksInOrder.map Sound.below)[k]? = some (c.blocksInOrder.map Sound.below)[k] :=
      List.getElem?_eq_getElem (by rw [hlenB]; exact hk)
    exact ⟨_, hb, fold_step hb g0 g1⟩
  have hs' : ∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧ StepYes 0 (Sound.below b)
      (stateAt 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
        (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened k)
      (stateAt 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub)
        (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened (k + 1)) := by
    intro k hk
    obtain ⟨b', hb', hy⟩ := hsB k hk
    rw [List.getElem?_map] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
    exact ⟨b, hb, hy⟩
  have hm := noMark_path hS hR O (ft := 0) (st := stateAt 0 (c.blocksInOrder.map Sound.below)
    (ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened)
    fun j hj => by
      obtain ⟨b, hb, hy⟩ := hs' j hj
      exact ⟨b, hb, stepYes_raw hy⟩
  refine ⟨pp, F, Z, Bs, base, c, A, B, _, hR, O, hr, hp, hlen, hx, h0, ?_, ?_, hs', ?_, ?_, ?_,
    hlive, hlaid⟩
  · rw [hend]
    exact fold_raw 0 _ _ _ _ _ hf
  · intro k _
    obtain ⟨r, q, g⟩ := hpre k
    refine ⟨r, q, ?_, g⟩
    rw [← List.map_take] at g
    exact fold_raw 0 _ _ _ _ _ g
  · intro k hk
    have R := reach_of_path (z := (LPFD.Full.instanceAsPlainRecord z).pub) h0 hsB k hk
    exact ⟨R, reach_raw R, hm k hk⟩
  · rw [hend]; exact hfin
  · rw [hend]; exact hask

#print axioms step_raw
#print axioms fold_raw
#print axioms stateAt_ok
#print axioms fold_prefix
#print axioms fold_step
#print axioms view_of_run
#print axioms member_fold

end IM
