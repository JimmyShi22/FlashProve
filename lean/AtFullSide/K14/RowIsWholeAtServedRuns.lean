-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/RowIsWholeAtServedRuns.lean: the linear claim (kind K14): THE SILENT DEFAULTS OF THIS
KIND's SENDERS ARE NOT TAKEN AT A RUN AT A SERVED REQUEST, AS ONE PROPOSITION, in the form of the
propositions of E2E/TheHonestProverNotTaken.lean, and its proof. The senders' texts meet some cases
by a default value, with no error (the head of Johnson/Desc/ProofFile/Honest/K14/Sendings.lean).

  heard_at_shared_walk
      what the state of a run has heard in front of a part of the shared chain, as the run's own
      walk reaches it (midSharedAtW, Johnson/Desc/ProofFile/Honest/MidW.lean): the shared chain's
      challenges in front of that part's first round
  front_le
      these are at least as many as the sub-protocols declare that stand in front of the part's
      place
  heardFrom_grows
      what heardFrom returns at a number does not move when more is heard
  point_at_walk, zeta_at_walk
      under the hypothesis, where the challenges are such as the rounds can draw: in front of a part
      behind "LIN point" heardFrom at the number 0 returns [d], d of kCol elements; in front of a
      part behind "LIN zeta" heardFrom at the number 6 returns [d], d of kRow elements
  seeds_at_members
      off every list of challenges that the rounds of the description's members 2 and 5 can draw the
      two sendings' seeds are whole, at the sendings' own parameters
  seeds_at_second_move
      at the very term that a sending's second move reads, at whatever state has last heard a
      challenge that fits the member's first round: the list cut off it is the whole list of seeds
  midSharedBehindFirstW
      A DEFINITION WITH CODE: the state of a run behind the first round of the part at an address of
      the shared chain: the text of midSharedAtW with one round more walked. In the walk (walk,
      Johnson/Desc/ProofFile/Honest/Walk.lean) the part's second round is told from just that state
  heard_behind_first, apart_of_nodup, places_apart_at_head, behind_first_at_head
      that state has heard the chain's challenges up to and with that round's; under the hypothesis
      the shared chain's places are all different (off the written cut, by Lean's kernel); so the
      list heard is the challenges in front of the member, then one challenge that fits the member's
      first round
  second_move_u, second_move_omega
      at that state, and at whatever state has heard the same: the shared point is heard whole; the
      list that the sending's second move cuts off the last challenge heard is the whole list of
      seeds; no factor is 0
  K14RowIsWholeAtServedRuns
      **the proposition.** Public clauses, with no run: each tree's declared width is its columns'
      length, at all three trees of the two sendings; the two sentences on the seeds. Clauses at a
      stand of a run at a served request: in front of the parts at "send o_u", "send o_omega" and
      "SPLIT", and at every state that has heard more than that stand, the shared point is heard
      whole; the like for the challenge of "LIN zeta" in front of the part at "SPLIT"; behind the
      first round of each of the two sendings: the two sentences of second_move_u and
      second_move_omega
  k14_row_is_whole
      it holds under the library's hypothesis at the returned public part, places and first chain
  k14_row_at_return
      **it holds at the return of the maker from which the honest prover for a request is made**,
      under the library's hypothesis at these files, at some letters: the proposition's premise
      PlayedAt makes these letters the proposition's

THE STAND CLAUSES NEED NO INVARIANT: they follow from the walk's own text and from one conjunct of
StandsAtServed: that the challenges are such as the description's rounds can draw.

Limits.
  * The hypothesis P5J.AtMgA stands outside the proposition.
  * THAT A STAND EXISTS IS NOT SAID: where midSharedAtW or midSharedBehindFirstW returns no state at
    an address, the clause there says nothing. Of StandsAtServed two conjuncts are not read (that
    the request is served; that no fall speaks): so the clauses hold at every input.
  * midSharedAtW returns the state in front of a part's FIRST move; midSharedBehindFirstW the state
    behind its first round. That walk tells the part's second round from just that state, and that
    the whole walk passes through it, is read off the text of walk; no statement here says it.
  * The public sentences on the seeds (seeds_at_members, seeds_at_second_move) speak of every list,
    or of every state, of a form, and are joined to no stand. The proposition's two last clauses
    alone join them to a state of a run: the one behind a sending's first round.
  * Three defaults of the same list are not here: the default code at a message without rows of that
    sort, a message's number beyond the sending, and the empty challenge in the invariant's witness.
    That the list of defaults is complete is by reading.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheHonestProverNotTaken
import Johnson.Desc.ProofFile.Honest.K14.HeardInside
import Johnson.Desc.ProofFile.Honest.K14.WidthAllTrees
import Johnson.Desc.ProofFile.Honest.K14.DataMade
import Johnson.Desc.ProofFile.Honest.K14.PaidAt
import Johnson.Desc.ProofFile.Honest.WalkHeard
import Johnson.Desc.ProofFile.Honest.StepsFront
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.ToldDescR.PureChainOfOpen
import Johnson.Goal.Skeleton.CutIsOfLaid
import AtFullSide.K14.Sim.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain Place FileDescription)
open VerifiableInference.Desc.K1 (qAt)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.Term (OnlineReturn)
open AtPublicFiles.AtFiles.HonestTerm (PlayedAt StandsAtServed)
open P5J (AtMgA TS F0T)
open Desc.K14 (St p14Of beforePointOf)
open Desc.K14.Law (entryAt parU parO)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

section walk
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **What a run's state has heard in front of a part of the shared chain.** -/
theorem heard_at_shared_walk {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {stand : Mid (Common W₀ Rc Ky) X₀}
    (hm : midSharedAtW F B H w₀ rc x c ρ a = .ok (some stand)) :
    ∃ R, ready F B H w₀ rc x c = .ok R ∧
      stand.st.heard = ρ.shared.take (R.shared.takeWhile fun s => s.addr != a).length := by
  unfold midSharedAtW at hm
  obtain ⟨R, hR, hm⟩ := exBind_ok hm
  obtain ⟨a₂, ha₂, hm⟩ := exBind_ok hm
  unfold midInW at hm
  dsimp only at hm
  split at hm
  · cases hm
  · obtain ⟨z, hz, hzm⟩ := exMap_ok hm
    have h1 := walk_hears _ _ _ _ a₂ z (start_hears ha₂) hz stand hzm
    have h2 := walk_laid_drawn _ _ _ a₂ z hz
    rw [start_laid ha₂] at h2
    refine ⟨R, hR, ?_⟩
    rw [h1, h2]
    rfl

/-- **The state of a run behind the first round of the part at an address of the shared chain.** -/
def midSharedBehindFirstW (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (c : Coins B) (ρ : Draws) (a : Addr) :
    Except Refusal (Option (Mid (Common W₀ Rc Ky) X₀)) :=
  (ready F B H w₀ rc x c).bind fun R =>
  (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  if !R.shared.any (·.addr == a) then
    .error ⟨.unfit, "no round of the chain stands at the address"⟩
  else (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩
    (R.shared.take ((R.shared.takeWhile fun s => s.addr != a).length + 1))
    (ρ.shared.take ((R.shared.takeWhile fun s => s.addr != a).length + 1)) a₂).map (·.mid)

/-- **That state has heard the chain's challenges up to and with that round's.** -/
theorem heard_behind_first {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr} {m : Mid (Common W₀ Rc Ky) X₀}
    (hm : midSharedBehindFirstW F B H w₀ rc x c ρ a = .ok (some m)) :
    ∃ R, ready F B H w₀ rc x c = .ok R ∧ R.shared.any (·.addr == a) = true ∧
      m.st.heard = ρ.shared.take ((R.shared.takeWhile fun s => s.addr != a).length + 1) := by
  unfold midSharedBehindFirstW at hm
  obtain ⟨R, hR, hm⟩ := exBind_ok hm
  obtain ⟨a₂, ha₂, hm⟩ := exBind_ok hm
  by_cases hany : R.shared.any (·.addr == a) = true
  · simp only [hany, Bool.not_true, Bool.false_eq_true, if_false] at hm
    obtain ⟨z, hz, hzm⟩ := exMap_ok hm
    have h1 := walk_hears _ _ _ _ a₂ z (start_hears ha₂) hz m hzm
    have h2 := walk_laid_drawn _ _ _ a₂ z hz
    rw [start_laid ha₂] at h2
    refine ⟨R, hR, hany, ?_⟩
    rw [h1, h2]
    rfl
  · simp only [hany, Bool.not_false, if_true] at hm
    cases hm

end walk

/-- The rounds in front of a part are at least as many as the sub-protocols declare that stand in
front of its place. -/
theorem front_le {S Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {hs : List (Placed V W X)}
    {pre rest : List (Block S Cl)} {ss : List (Step W X)}
    (h : chainSteps B rows look v (pre ++ rest) hs = .ok ss) (a : Addr)
    (hp : ∀ b ∈ pre, b.place ≠ a.place) :
    (pre.flatMap (·.rounds)).length ≤ (ss.takeWhile fun s => s.addr != a).length := by
  rw [chainSteps_append] at h
  obtain ⟨l₁, h1, h⟩ := exBind_ok h
  obtain ⟨l₂, -, rfl⟩ := exMap_ok h
  have hall : ∀ s ∈ l₁, (s.addr != a) = true := by
    intro s hs'
    obtain ⟨b, hb, e⟩ := steps_place_mem h1 s hs'
    rw [bne_iff_ne]
    intro ea
    exact hp b hb (by rw [← e, ea])
  rw [List.takeWhile_append_of_pos hall, List.length_append, ← steps_decl h1, List.length_map]
  exact Nat.le_add_right _ _

/-- In a list whose places are all different, no other member stands at a member's place. -/
theorem apart_of_nodup {S Cl : Type} {pre t : List (Block S Cl)} {b : Block S Cl}
    (h : ((pre ++ b :: t).map (·.place)).Nodup) :
    (∀ b' ∈ pre, b'.place ≠ b.place) ∧ ∀ b' ∈ t, b'.place ≠ b.place := by
  rw [List.map_append, List.map_cons] at h
  obtain ⟨-, h2, h3⟩ := List.nodup_append.1 h
  refine ⟨fun b' hb' => h3 _ (List.mem_map_of_mem hb') _ List.mem_cons_self, fun b' hb' e => ?_⟩
  exact (List.nodup_cons.1 h2).1 (e ▸ List.mem_map_of_mem hb')

/-- Of a list cut behind its member number i, the member number i is the list's own. -/
theorem take_drop_one {α : Type} (l : List α) (n i : Nat) (hn : i + 1 ≤ n) :
    ((l.take n).drop i).take 1 = (l.drop i).take 1 := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- What heardFrom returns at a number does not move when more is heard. -/
theorem heardFrom_grows {W X W' X' : Type} {t : State W X} {t' : State W' X'} {i : Nat}
    {d : Fmt.Drawn} {more : List Fmt.Drawn} (h : heardFrom t i 1 = [d])
    (ht : t'.heard = t.heard ++ more) : heardFrom t' i 1 = [d] := by
  unfold heardFrom at h
  refine heardFrom_of ht h ?_
  by_contra hc
  rw [List.drop_eq_nil_of_le (by omega)] at h
  cases h

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- **In front of a part behind "LIN point" the shared point is heard whole.** ha: the part stands
neither at the chain's front nor at "LIN point". hdue: the challenges fit the declared rounds. -/
theorem point_at_walk (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {B : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins B}
    {ρ : Draws} {a : Addr} {stand : Mid (Common W₀ Rc TableKey) X₀}
    (hdue : drawsFit (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true)
    (ha : a.place ≠ ⟨2, none, 0, .frame⟩ ∧ a.place ≠ place 1)
    (hm : midSharedAtW (F0T OnBytes.secondHashFunction Zp Np cF) B H w₀ rc x c ρ a = .ok (some stand)) :
    ∃ d : Fmt.Drawn, d.elems.length = (qAt Zp Np).S.kCol ∧ heardFrom stand.st 0 1 = [d] := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨E⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, l0, l1, -⟩ :
      Desc.K14.Honest.FlatOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder Zp.p.chains E.b1 E.b2 E.b3
        E.b4 E.b5 E.b6 E.b7 E.b8 := by
    rw [shared_flat_at]
    exact Desc.K14.Honest.flatOf_carried Zp.p.chains _ E.b1 E.b2 E.b3 E.b4 E.b5 E.b6 E.b7 E.b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last E.made
  obtain ⟨r₁, hr, hre⟩ : ∃ r₁, E.b1.rounds = [r₁] ∧
      r₁.entry = entryAt (p14Of Zp.p.chains (beforePointOf Np)) 0 := by
    have q := (Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ E.made).1
    cases hb1 : E.b1.rounds with
    | nil => rw [hb1] at q; cases q
    | cons a' t =>
      rw [hb1] at q
      cases t with
      | nil => exact ⟨a', rfl, (List.cons.inj q).1⟩
      | cons a'' t' => cases (List.cons.inj q).2
  obtain ⟨R, hR, hh⟩ := heard_at_shared_walk hm
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := ready_ok hR
  have hpre : ([x0, x1].flatMap (·.rounds)) = [r₁] := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [l0.rounds, l1.rounds, hr]
    rfl
  have hn : 1 ≤ (R.shared.takeWhile fun s => s.addr != a).length := by
    have hS' : chainSteps B (B.rowsOf 1) (sharedLook B c.shared) (Face.shared.sees R.common)
        ([x0, x1] ++ (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl)) H.shared = .ok R.shared := by
      rw [e] at hS
      exact hS
    have k := front_le hS' a (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [l0.place]
        exact fun e' => ha.1 e'.symm
      · rw [l1.place, (places4 _ _ _ _ _ _ _ _ _ E.made).1]
        exact fun e' => ha.2 e'.symm)
    rw [hpre] at k
    exact k
  have hd : drawsFit ([] ++ r₁ :: ((x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).flatMap
      (·.rounds))) ρ.shared = true := by
    have e2 : (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 =
        [x0, x1].flatMap (·.rounds) ++
          (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).flatMap (·.rounds) := by
      show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds) = _
      rw [e, ← List.flatMap_append]
      rfl
    rw [e2, hpre] at hdue
    exact hdue
  obtain ⟨d, h1, -, h3⟩ := drawsFit_at [] r₁ _ ρ.shared hd
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h3
  refine ⟨d, ?_, ?_⟩
  · rw [h3.1.1.1.1.1.1.1, hre]
    exact (Desc.K14.Law.entry_point _).1
  · unfold heardFrom
    rw [hh, take_drop_one _ _ 0 hn]
    exact h1

/-- **In front of the part at "SPLIT" the challenge of "LIN zeta" is heard whole.** -/
theorem zeta_at_walk (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {B : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins B}
    {ρ : Draws} {a : Addr} {stand : Mid (Common W₀ Rc TableKey) X₀}
    (hdue : drawsFit (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true)
    (ha : a.place = place 8)
    (hm : midSharedAtW (F0T OnBytes.secondHashFunction Zp Np cF) B H w₀ rc x c ρ a = .ok (some stand)) :
    ∃ d : Fmt.Drawn, d.elems.length = (qAt Zp Np).S.kRow ∧ heardFrom stand.st 6 1 = [d] := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨E⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, l0, l1, l2, l3, l4, l5, l6, l7, -⟩ :
      Desc.K14.Honest.FlatOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder Zp.p.chains E.b1 E.b2 E.b3
        E.b4 E.b5 E.b6 E.b7 E.b8 := by
    rw [shared_flat_at]
    exact Desc.K14.Honest.flatOf_carried Zp.p.chains _ E.b1 E.b2 E.b3 E.b4 E.b5 E.b6 E.b7 E.b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last E.made
  obtain ⟨-, r2, r3, r4, r5, r6, -, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU E.b1 E.b2 E.b3 E.b4
    E.b5 E.b6 E.b7 E.b8 E.made hQ.facts.goes
  have q := Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ E.made
  obtain ⟨r₁, hr1⟩ : ∃ r₁, E.b1.rounds = [r₁] := by
    have q1 := congrArg List.length q.1
    rw [List.length_map] at q1
    exact List.length_eq_one_iff.1 q1
  obtain ⟨r₇, hr7, hre⟩ : ∃ r₇, E.b7.rounds = [r₇] ∧
      r₇.entry = entryAt (p14Of Zp.p.chains (beforePointOf Np)) 2 := by
    have q7 := q.2.2
    cases hb7 : E.b7.rounds with
    | nil => rw [hb7] at q7; cases q7
    | cons a' t =>
      rw [hb7] at q7
      cases t with
      | nil => exact ⟨a', rfl, (List.cons.inj q7).1⟩
      | cons a'' t' => cases (List.cons.inj q7).2
  obtain ⟨pre, hlen, hpre⟩ : ∃ pre : List Fmt.DeclaredRound, pre.length = 6 ∧
      [x0, x1, x2, x3, x4, x5, x6, x7].flatMap (·.rounds) = pre ++ [r₇] := by
    refine ⟨r₁ :: (VerifiableInference.Desc.K1.rounds
        (parU (p14Of Zp.p.chains (beforePointOf Np)) sentU) ++ (E.b4.rounds ++
      VerifiableInference.Desc.K1.rounds (parO (p14Of Zp.p.chains (beforePointOf Np))))), ?_, ?_⟩
    · rw [r4]
      rfl
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
        hr1, r2, r3, r5, r6, hr7]
      simp only [List.nil_append, List.cons_append, List.append_assoc]
      rfl
  obtain ⟨R, hR, hh⟩ := heard_at_shared_walk hm
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := ready_ok hR
  obtain ⟨p1, p4, p7, -⟩ := places4 _ _ _ _ _ _ _ _ _ E.made
  obtain ⟨p3, p6⟩ := places2 _ _ _ _ _ _ _ _ _ E.made
  obtain ⟨-, p2, -, p5⟩ := send_declares _ 0 _ _ _ _ _ _ _ _ E.made
  have hn : 6 + 1 ≤ (R.shared.takeWhile fun s => s.addr != a).length := by
    have hS' : chainSteps B (B.rowsOf 1) (sharedLook B c.shared) (Face.shared.sees R.common)
        ([x0, x1, x2, x3, x4, x5, x6, x7] ++ (x8 :: tl)) H.shared = .ok R.shared := by
      rw [e] at hS
      exact hS
    have k := front_le hS' a (by
      intro b hb
      rw [ha]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [l0.place]
        show (⟨2, none, 0, .frame⟩ : Place) ≠ place 8
        decide
      · rw [l1.place, p1]
        decide
      · rw [l2.place, p2]
        decide
      · rw [l3.place, p3]
        decide
      · rw [l4.place, p4]
        decide
      · rw [l5.place, p5]
        decide
      · rw [l6.place, p6]
        decide
      · rw [l7.place, p7]
        decide)
    rw [hpre, List.length_append, hlen] at k
    exact k
  have hd : drawsFit (pre ++ r₇ :: ((x8 :: tl).flatMap (·.rounds))) ρ.shared = true := by
    have e2 : (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 =
        [x0, x1, x2, x3, x4, x5, x6, x7].flatMap (·.rounds) ++ (x8 :: tl).flatMap (·.rounds) := by
      show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds) = _
      rw [e, ← List.flatMap_append]
      rfl
    rw [e2, hpre, List.append_assoc] at hdue
    exact hdue
  obtain ⟨d, h1, -, h3⟩ := drawsFit_at pre r₇ _ ρ.shared hd
  rw [hlen] at h1
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h3
  refine ⟨d, ?_, ?_⟩
  · rw [h3.1.1.1.1.1.1.1, hre]
    exact (Desc.K14.Law.entry_zeta _).1
  · unfold heardFrom
    rw [hh, take_drop_one _ _ 6 hn]
    exact h1

/-- **Off every list of challenges that the rounds of the description's members 2 and 5 can draw,
the two sendings' seeds are whole**, at the sendings' own parameters. -/
theorem seeds_at_members (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (n : Nat) :
    (∀ blk, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[2]? = some blk → ∀ ds,
      drawsFit blk.rounds ds = true → K1.seedsFit (jobU ⟨qAt Zp Np, n⟩).Q ds = true ∧
        ∀ s ∈ K1.seedsAt (jobU ⟨qAt Zp Np, n⟩).Q ds, OnBytes.Slice.readE s.2 ≠ 0) ∧
    ∀ blk, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[5]? = some blk → ∀ ds,
      drawsFit blk.rounds ds = true → K1.seedsFit (jobOmega ⟨qAt Zp Np, n⟩).Q ds = true ∧
        ∀ s ∈ K1.seedsAt (jobOmega ⟨qAt Zp Np, n⟩).Q ds, OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨E⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, -, l2, -, -, l5, -⟩ :
      Desc.K14.Honest.FlatOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder Zp.p.chains E.b1 E.b2 E.b3
        E.b4 E.b5 E.b6 E.b7 E.b8 := by
    rw [shared_flat_at]
    exact Desc.K14.Honest.flatOf_carried Zp.p.chains _ E.b1 E.b2 E.b3 E.b4 E.b5 E.b6 E.b7 E.b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last E.made
  obtain ⟨-, r2, -, -, r5, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU E.b1 E.b2 E.b3 E.b4
    E.b5 E.b6 E.b7 E.b8 E.made hQ.facts.goes
  refine ⟨fun blk hb ds hd => ?_, fun blk hb ds hd => ?_⟩
  · rw [e] at hb
    obtain rfl : x2 = blk := Option.some.inj hb
    rw [l2.rounds, r2] at hd
    rw [jobU_par hQ.facts.goes n]
    exact OnBytes.SendSim.At.draws_send _ hd
  · rw [e] at hb
    obtain rfl : x5 = blk := Option.some.inj hb
    rw [l5.rounds, r5] at hd
    rw [jobOmega_par]
    exact OnBytes.SendSim.At.draws_send _ hd

/-- **At the very term that a sending's second move reads**: at whatever state has last heard a
challenge that fits the first round of the description's member 2 (of the member 5), the list that
the move cuts off that challenge is the whole list of seeds, and no factor is 0. -/
theorem seeds_at_second_move (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (n : Nat) :
    (∀ blk r₀ rest, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[2]? = some blk →
      blk.rounds = r₀ :: rest → ∀ d, drawFit r₀ d = true →
      ∀ (W' X' : Type) (t' : State W' X') (heard : List Fmt.Drawn), t'.heard = heard ++ [d] →
        VerifiableInference.Desc.K1.cutSeeds (jobU ⟨qAt Zp Np, n⟩).Q.coordinates
            (jobU ⟨qAt Zp Np, n⟩).Q.seeds (elems (t'.lately 1)) =
          K1.seedsAt (jobU ⟨qAt Zp Np, n⟩).Q [d] ∧
        K1.seedsFit (jobU ⟨qAt Zp Np, n⟩).Q [d] = true ∧
        ∀ s ∈ K1.seedsAt (jobU ⟨qAt Zp Np, n⟩).Q [d], OnBytes.Slice.readE s.2 ≠ 0) ∧
    ∀ blk r₀ rest, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[5]? = some blk →
      blk.rounds = r₀ :: rest → ∀ d, drawFit r₀ d = true →
      ∀ (W' X' : Type) (t' : State W' X') (heard : List Fmt.Drawn), t'.heard = heard ++ [d] →
        VerifiableInference.Desc.K1.cutSeeds (jobOmega ⟨qAt Zp Np, n⟩).Q.coordinates
            (jobOmega ⟨qAt Zp Np, n⟩).Q.seeds (elems (t'.lately 1)) =
          K1.seedsAt (jobOmega ⟨qAt Zp Np, n⟩).Q [d] ∧
        K1.seedsFit (jobOmega ⟨qAt Zp Np, n⟩).Q [d] = true ∧
        ∀ s ∈ K1.seedsAt (jobOmega ⟨qAt Zp Np, n⟩).Q [d], OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨E⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, -, l2, -, -, l5, -⟩ :
      Desc.K14.Honest.FlatOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder Zp.p.chains E.b1 E.b2 E.b3
        E.b4 E.b5 E.b6 E.b7 E.b8 := by
    rw [shared_flat_at]
    exact Desc.K14.Honest.flatOf_carried Zp.p.chains _ E.b1 E.b2 E.b3 E.b4 E.b5 E.b6 E.b7 E.b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last E.made
  obtain ⟨-, r2, -, -, r5, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU E.b1 E.b2 E.b3 E.b4
    E.b5 E.b6 E.b7 E.b8 E.made hQ.facts.goes
  have late : ∀ (W' X' : Type) (t' : State W' X') (heard : List Fmt.Drawn) (d : Fmt.Drawn),
      t'.heard = heard ++ [d] → t'.lately 1 = [d] := by
    intro W' X' t' heard d ht
    obtain ⟨i, hd', o⟩ := t'
    obtain rfl : hd' = heard ++ [d] := ht
    exact lately_one _ _ _ _
  refine ⟨fun blk r₀ rest hb hr d hd W' X' t' heard ht => ?_,
    fun blk r₀ rest hb hr d hd W' X' t' heard ht => ?_⟩
  · rw [e] at hb
    obtain rfl : x2 = blk := Option.some.inj hb
    rw [l2.rounds, r2] at hr
    obtain rfl := (List.cons.inj hr).1
    rw [late W' X' t' heard d ht, jobU_par hQ.facts.goes n]
    exact seeds_of_first _ d hd
  · rw [e] at hb
    obtain rfl : x5 = blk := Option.some.inj hb
    rw [l5.rounds, r5] at hr
    obtain rfl := (List.cons.inj hr).1
    rw [late W' X' t' heard d ht, jobOmega_par]
    exact seeds_of_first _ d hd

/-- By Lean's kernel: the places of the shared chain's written cut are all different. -/
theorem written_places_apart :
    (VerifiableInference.PlanWritten.cutSharedFull.map (·.2.1)).Nodup := by
  decide +kernel

/-- **Under the hypothesis the shared chain's places are all different.** -/
theorem places_apart_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ((F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.map (·.place)).Nodup := by
  have c2 := (P5J.cuts_of_laid h.toAtMg.scope h.toAtMg.laid).2.1
  have e : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.map (·.place) =
      (VerifiableInference.PlanWritten.cutOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).map
        (·.2.1) := by
    unfold VerifiableInference.PlanWritten.cutOf
    rw [List.map_map]
    rfl
  rw [e, c2]
  exact written_places_apart

/-- **Behind the first round of the first part of a member**: the list heard is the challenges in
front of the member, then one challenge that fits the member's first round. -/
theorem behind_first_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {B : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins B}
    {ρ : Draws} {m : Mid (Common W₀ Rc TableKey) X₀} {pre t : List (Block St ProofFile.Cl)}
    {b : Block St ProofFile.Cl} {r₀ : Fmt.DeclaredRound} {rest : List Fmt.DeclaredRound}
    (e : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ b :: t) (hb : b.rounds = r₀ :: rest)
    (hdue : drawsFit (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true)
    (hm : midSharedBehindFirstW (F0T OnBytes.secondHashFunction Zp Np cF) B H w₀ rc x c ρ ⟨b.place, 0⟩ =
      .ok (some m)) :
    ∃ d : Fmt.Drawn, drawFit r₀ d = true ∧
      m.st.heard = ρ.shared.take (pre.flatMap (·.rounds)).length ++ [d] := by
  obtain ⟨R, hR, hany, hh⟩ := heard_behind_first hm
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := ready_ok hR
  rw [e] at hS
  have nd := places_apart_at_head h
  rw [e] at nd
  obtain ⟨hp, ht⟩ := apart_of_nodup nd
  rw [chainSteps_front hS hp ht hany] at hh
  have hd : drawsFit (pre.flatMap (·.rounds) ++ r₀ :: (rest ++ t.flatMap (·.rounds))) ρ.shared =
      true := by
    have e2 : (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 =
        pre.flatMap (·.rounds) ++ r₀ :: (rest ++ t.flatMap (·.rounds)) := by
      have e3 : (pre ++ b :: t).flatMap (·.rounds) =
          pre.flatMap (·.rounds) ++ r₀ :: (rest ++ t.flatMap (·.rounds)) := by
        rw [List.flatMap_append, List.flatMap_cons, hb]
        rfl
      exact (congrArg (fun l => l.flatMap (·.rounds)) e).trans e3
    rw [e2] at hdue
    exact hdue
  obtain ⟨d, h1, -, h3⟩ := drawsFit_at _ r₀ _ ρ.shared hd
  refine ⟨d, h3, ?_⟩
  rw [hh, List.take_add]
  exact congrArg (fun l => ρ.shared.take (pre.flatMap (·.rounds)).length ++ l) h1

/-- **The second move of "send o_u", at the state that the run's walk hands it**, and at whatever
state has heard the same. -/
theorem second_move_u (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {B : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins B}
    {ρ : Draws} {m : Mid (Common W₀ Rc TableKey) X₀}
    (hdue : drawsFit (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true)
    (hm : midSharedBehindFirstW (F0T OnBytes.secondHashFunction Zp Np cF) B H w₀ rc x c ρ ⟨sendPlace 2, 0⟩ =
      .ok (some m)) (n : Nat) :
    ∃ d₀ d : Fmt.Drawn, d₀.elems.length = (qAt Zp Np).S.kCol ∧
      ∀ (W' X' : Type) (t' : State W' X'), t'.heard = m.st.heard →
        heardFrom t' 0 1 = [d₀] ∧
        VerifiableInference.Desc.K1.cutSeeds (jobU ⟨qAt Zp Np, n⟩).Q.coordinates
            (jobU ⟨qAt Zp Np, n⟩).Q.seeds (elems (t'.lately 1)) =
          K1.seedsAt (jobU ⟨qAt Zp Np, n⟩).Q [d] ∧
        K1.seedsFit (jobU ⟨qAt Zp Np, n⟩).Q [d] = true ∧
        ∀ s ∈ K1.seedsAt (jobU ⟨qAt Zp Np, n⟩).Q [d], OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨E⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, l0, l1, l2, -⟩ :
      Desc.K14.Honest.FlatOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder Zp.p.chains E.b1 E.b2 E.b3
        E.b4 E.b5 E.b6 E.b7 E.b8 := by
    rw [shared_flat_at]
    exact Desc.K14.Honest.flatOf_carried Zp.p.chains _ E.b1 E.b2 E.b3 E.b4 E.b5 E.b6 E.b7 E.b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last E.made
  obtain ⟨-, r2, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU E.b1 E.b2 E.b3 E.b4
    E.b5 E.b6 E.b7 E.b8 E.made hQ.facts.goes
  obtain ⟨-, p2, -, -⟩ := send_declares _ 0 _ _ _ _ _ _ _ _ E.made
  have q := Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ E.made
  obtain ⟨r₁, hr1, hre⟩ : ∃ r₁, E.b1.rounds = [r₁] ∧
      r₁.entry = entryAt (p14Of Zp.p.chains (beforePointOf Np)) 0 := by
    have q1 := q.1
    cases hb1 : E.b1.rounds with
    | nil => rw [hb1] at q1; cases q1
    | cons a' t =>
      rw [hb1] at q1
      cases t with
      | nil => exact ⟨a', rfl, (List.cons.inj q1).1⟩
      | cons a'' t' => cases (List.cons.inj q1).2
  have hpre : ([x0, x1].flatMap (·.rounds)) = [r₁] := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [l0.rounds, l1.rounds, hr1]
    rfl
  obtain ⟨r₀, rest, hx2⟩ : ∃ r₀ rest, x2.rounds = r₀ :: rest := by
    rw [l2.rounds, r2]
    exact ⟨_, _, rfl⟩
  have ep : x2.place = sendPlace 2 := by rw [l2.place, p2]
  have e' : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder =
      [x0, x1] ++ x2 :: (x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl) := e
  rw [← ep] at hm
  obtain ⟨d, hd, hh'⟩ := behind_first_at_head h e' hx2 hdue hm
  have hh : m.st.heard = ρ.shared.take 1 ++ [d] :=
    hh'.trans (congrArg (fun k => ρ.shared.take k ++ [d]) (congrArg List.length hpre))
  have hd0 : drawsFit ([] ++ r₁ :: ((x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).flatMap
      (·.rounds))) ρ.shared = true := by
    have e2 : (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 =
        [x0, x1].flatMap (·.rounds) ++
          (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).flatMap (·.rounds) := by
      show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds) = _
      rw [e, ← List.flatMap_append]
      rfl
    rw [e2, hpre] at hdue
    exact hdue
  obtain ⟨d₀, h1, -, h3⟩ := drawsFit_at [] r₁ _ ρ.shared hd0
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h3
  refine ⟨d₀, d, ?_, fun W' X' t' ht => ⟨?_, ?_⟩⟩
  · rw [h3.1.1.1.1.1.1.1, hre]
    exact (Desc.K14.Law.entry_point _).1
  · have h1' : (ρ.shared.take 1) = [d₀] := h1
    unfold heardFrom
    rw [ht, hh]
    show (((ρ.shared.take 1 ++ [d]).drop 0).take 1) = [d₀]
    rw [h1']
    rfl
  · exact (seeds_at_second_move h n).1 x2 r₀ rest (by rw [e]; rfl) hx2 d hd W' X' t' _
      (ht.trans hh)

/-- **The second move of "send o_omega", at the state that the run's walk hands it**, and at
whatever state has heard the same. -/
theorem second_move_omega (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {B : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins B}
    {ρ : Draws} {m : Mid (Common W₀ Rc TableKey) X₀}
    (hdue : drawsFit (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true)
    (hm : midSharedBehindFirstW (F0T OnBytes.secondHashFunction Zp Np cF) B H w₀ rc x c ρ ⟨sendPlace 5, 0⟩ =
      .ok (some m)) (n : Nat) :
    ∃ d₀ d : Fmt.Drawn, d₀.elems.length = (qAt Zp Np).S.kCol ∧
      ∀ (W' X' : Type) (t' : State W' X'), t'.heard = m.st.heard →
        heardFrom t' 0 1 = [d₀] ∧
        VerifiableInference.Desc.K1.cutSeeds (jobOmega ⟨qAt Zp Np, n⟩).Q.coordinates
            (jobOmega ⟨qAt Zp Np, n⟩).Q.seeds (elems (t'.lately 1)) =
          K1.seedsAt (jobOmega ⟨qAt Zp Np, n⟩).Q [d] ∧
        K1.seedsFit (jobOmega ⟨qAt Zp Np, n⟩).Q [d] = true ∧
        ∀ s ∈ K1.seedsAt (jobOmega ⟨qAt Zp Np, n⟩).Q [d], OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨E⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, l0, l1, -, -, -, l5, -⟩ :
      Desc.K14.Honest.FlatOf (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder Zp.p.chains E.b1 E.b2 E.b3
        E.b4 E.b5 E.b6 E.b7 E.b8 := by
    rw [shared_flat_at]
    exact Desc.K14.Honest.flatOf_carried Zp.p.chains _ E.b1 E.b2 E.b3 E.b4 E.b5 E.b6 E.b7 E.b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last E.made
  obtain ⟨-, -, -, -, r5, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU E.b1 E.b2 E.b3 E.b4
    E.b5 E.b6 E.b7 E.b8 E.made hQ.facts.goes
  obtain ⟨-, -, -, p5⟩ := send_declares _ 0 _ _ _ _ _ _ _ _ E.made
  have q := Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ E.made
  obtain ⟨r₁, hr1, hre⟩ : ∃ r₁, E.b1.rounds = [r₁] ∧
      r₁.entry = entryAt (p14Of Zp.p.chains (beforePointOf Np)) 0 := by
    have q1 := q.1
    cases hb1 : E.b1.rounds with
    | nil => rw [hb1] at q1; cases q1
    | cons a' t =>
      rw [hb1] at q1
      cases t with
      | nil => exact ⟨a', rfl, (List.cons.inj q1).1⟩
      | cons a'' t' => cases (List.cons.inj q1).2
  have hpre : ([x0, x1].flatMap (·.rounds)) = [r₁] := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [l0.rounds, l1.rounds, hr1]
    rfl
  obtain ⟨r₀, rest, hx5⟩ : ∃ r₀ rest, x5.rounds = r₀ :: rest := by
    rw [l5.rounds, r5]
    exact ⟨_, _, rfl⟩
  have ep : x5.place = sendPlace 5 := by rw [l5.place, p5]
  have e' : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder =
      [x0, x1, x2, x3, x4] ++ x5 :: (x6 :: x7 :: x8 :: tl) := e
  rw [← ep] at hm
  obtain ⟨d, hd, hh⟩ := behind_first_at_head h e' hx5 hdue hm
  have hd0 : drawsFit ([] ++ r₁ :: ((x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).flatMap
      (·.rounds))) ρ.shared = true := by
    have e2 : (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 =
        [x0, x1].flatMap (·.rounds) ++
          (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).flatMap (·.rounds) := by
      show (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds) = _
      rw [e, ← List.flatMap_append]
      rfl
    rw [e2, hpre] at hdue
    exact hdue
  obtain ⟨d₀, h1, -, h3⟩ := drawsFit_at [] r₁ _ ρ.shared hd0
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h3
  have hone : 0 + 1 ≤ ([x0, x1, x2, x3, x4].flatMap (·.rounds)).length := by
    have e5 : [x0, x1, x2, x3, x4].flatMap (·.rounds) =
        [x0, x1].flatMap (·.rounds) ++ [x2, x3, x4].flatMap (·.rounds) := by
      rw [← List.flatMap_append]
      rfl
    rw [e5, hpre]
    exact Nat.succ_le_succ (Nat.zero_le _)
  refine ⟨d₀, d, ?_, fun W' X' t' ht => ⟨?_, ?_⟩⟩
  · rw [h3.1.1.1.1.1.1.1, hre]
    exact (Desc.K14.Law.entry_point _).1
  · refine heardFrom_of (ht.trans hh) ?_ ?_
    · exact (take_drop_one ρ.shared _ 0 hone).trans h1
    · rw [List.length_take]
      have hl : 1 ≤ ρ.shared.length := by
        by_contra hc
        have h1' : (ρ.shared.drop 0).take 1 = [d₀] := h1
        rw [List.drop_eq_nil_of_le (by omega)] at h1'
        cases h1'
      exact Nat.le_min.2 ⟨hone, hl⟩
  · exact (seeds_at_second_move h n).2 x5 r₀ rest (by rw [e]; rfl) hx5 d hd W' X' t' _
      (ht.trans hh)

variable {files : VerifierAndGoals.PublicFiles}

/-- **The silent defaults of the linear claim's senders are not taken at a run at a served
request.** First the public clauses: the trees' widths; the seeds off every list of challenges that
a sending's rounds can draw; the seeds at the very term that a sending's second move reads. Then, at
a stand of such a run in front of a part: what the part reads of the challenges heard, there and at
every state that has heard more. -/
def K14RowIsWholeAtServedRuns (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl) : Prop :=
  PlayedAt returned places firstChain →
  (treesOf (jobU ⟨qAt returned.Z places, 0⟩) = 1 ∧
    treesOf (jobOmega ⟨qAt returned.Z places, 0⟩) = 2 ∧
    widthAll (jobU ⟨qAt returned.Z places, 0⟩) = true ∧
    widthAll (jobOmega ⟨qAt returned.Z places, 0⟩) = true) ∧
  (∀ blk, (descZ returned.Z places firstChain).shared.blocksInOrder[2]? = some blk → ∀ ds,
    drawsFit blk.rounds ds = true →
      K1.seedsFit (jobU ⟨qAt returned.Z places, 0⟩).Q ds = true ∧
        ∀ s ∈ K1.seedsAt (jobU ⟨qAt returned.Z places, 0⟩).Q ds, OnBytes.Slice.readE s.2 ≠ 0) ∧
  (∀ blk, (descZ returned.Z places firstChain).shared.blocksInOrder[5]? = some blk → ∀ ds,
    drawsFit blk.rounds ds = true →
      K1.seedsFit (jobOmega ⟨qAt returned.Z places, 0⟩).Q ds = true ∧
        ∀ s ∈ K1.seedsAt (jobOmega ⟨qAt returned.Z places, 0⟩).Q ds,
          OnBytes.Slice.readE s.2 ≠ 0) ∧
  (∀ blk r₀ rest, (descZ returned.Z places firstChain).shared.blocksInOrder[2]? = some blk →
    blk.rounds = r₀ :: rest → ∀ d, drawFit r₀ d = true →
    ∀ (W' X' : Type) (t' : State W' X') (heard : List Fmt.Drawn), t'.heard = heard ++ [d] →
      VerifiableInference.Desc.K1.cutSeeds (jobU ⟨qAt returned.Z places, 0⟩).Q.coordinates
          (jobU ⟨qAt returned.Z places, 0⟩).Q.seeds (elems (t'.lately 1)) =
        K1.seedsAt (jobU ⟨qAt returned.Z places, 0⟩).Q [d] ∧
      K1.seedsFit (jobU ⟨qAt returned.Z places, 0⟩).Q [d] = true ∧
      ∀ s ∈ K1.seedsAt (jobU ⟨qAt returned.Z places, 0⟩).Q [d], OnBytes.Slice.readE s.2 ≠ 0) ∧
  (∀ blk r₀ rest, (descZ returned.Z places firstChain).shared.blocksInOrder[5]? = some blk →
    blk.rounds = r₀ :: rest → ∀ d, drawFit r₀ d = true →
    ∀ (W' X' : Type) (t' : State W' X') (heard : List Fmt.Drawn), t'.heard = heard ++ [d] →
      VerifiableInference.Desc.K1.cutSeeds (jobOmega ⟨qAt returned.Z places, 0⟩).Q.coordinates
          (jobOmega ⟨qAt returned.Z places, 0⟩).Q.seeds (elems (t'.lately 1)) =
        K1.seedsAt (jobOmega ⟨qAt returned.Z places, 0⟩).Q [d] ∧
      K1.seedsFit (jobOmega ⟨qAt returned.Z places, 0⟩).Q [d] = true ∧
      ∀ s ∈ K1.seedsAt (jobOmega ⟨qAt returned.Z places, 0⟩).Q [d],
        OnBytes.Slice.readE s.2 ≠ 0) ∧
  ∀ matrix tableCoins input coins challenges,
    StandsAtServed Served returned places firstChain matrix tableCoins input challenges →
    (∀ a stand, a = ⟨sendPlace 2, 0⟩ ∨ a = ⟨sendPlace 5, 0⟩ ∨ a = ⟨place 8, 0⟩ →
      midSharedAtW (descZ returned.Z places firstChain) returned.B returned.H matrix tableCoins
        input coins challenges a = .ok (some stand) →
      ∃ d : Fmt.Drawn, d.elems.length = (qAt returned.Z places).S.kCol ∧
        ∀ (W' X' : Type) (t' : State W' X') (more : List Fmt.Drawn),
          t'.heard = stand.st.heard ++ more → heardFrom t' 0 1 = [d]) ∧
    (∀ stand,
      midSharedAtW (descZ returned.Z places firstChain) returned.B returned.H matrix tableCoins
        input coins challenges ⟨place 8, 0⟩ = .ok (some stand) →
      ∃ d : Fmt.Drawn, d.elems.length = (qAt returned.Z places).S.kRow ∧
        ∀ (W' X' : Type) (t' : State W' X') (more : List Fmt.Drawn),
          t'.heard = stand.st.heard ++ more → heardFrom t' 6 1 = [d]) ∧
    (∀ m,
      midSharedBehindFirstW (descZ returned.Z places firstChain) returned.B returned.H matrix
        tableCoins input coins challenges ⟨sendPlace 2, 0⟩ = .ok (some m) →
      ∃ d₀ d : Fmt.Drawn, d₀.elems.length = (qAt returned.Z places).S.kCol ∧
        ∀ (W' X' : Type) (t' : State W' X'), t'.heard = m.st.heard →
          heardFrom t' 0 1 = [d₀] ∧
          VerifiableInference.Desc.K1.cutSeeds (jobU ⟨qAt returned.Z places, 0⟩).Q.coordinates
              (jobU ⟨qAt returned.Z places, 0⟩).Q.seeds (elems (t'.lately 1)) =
            K1.seedsAt (jobU ⟨qAt returned.Z places, 0⟩).Q [d] ∧
          K1.seedsFit (jobU ⟨qAt returned.Z places, 0⟩).Q [d] = true ∧
          ∀ s ∈ K1.seedsAt (jobU ⟨qAt returned.Z places, 0⟩).Q [d],
            OnBytes.Slice.readE s.2 ≠ 0) ∧
    ∀ m,
      midSharedBehindFirstW (descZ returned.Z places firstChain) returned.B returned.H matrix
        tableCoins input coins challenges ⟨sendPlace 5, 0⟩ = .ok (some m) →
      ∃ d₀ d : Fmt.Drawn, d₀.elems.length = (qAt returned.Z places).S.kCol ∧
        ∀ (W' X' : Type) (t' : State W' X'), t'.heard = m.st.heard →
          heardFrom t' 0 1 = [d₀] ∧
          VerifiableInference.Desc.K1.cutSeeds
              (jobOmega ⟨qAt returned.Z places, 0⟩).Q.coordinates
              (jobOmega ⟨qAt returned.Z places, 0⟩).Q.seeds (elems (t'.lately 1)) =
            K1.seedsAt (jobOmega ⟨qAt returned.Z places, 0⟩).Q [d] ∧
          K1.seedsFit (jobOmega ⟨qAt returned.Z places, 0⟩).Q [d] = true ∧
          ∀ s ∈ K1.seedsAt (jobOmega ⟨qAt returned.Z places, 0⟩).Q [d],
            OnBytes.Slice.readE s.2 ≠ 0

/-- **It holds under the library's hypothesis at the full size**, at the returned public part and
the places and first chain named. -/
theorem k14_row_is_whole (Served : FullSizeMatrix → LPFD.Full.XF → Prop) (returned : OnlineReturn files)
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain x₀) :
    K14RowIsWholeAtServedRuns Served returned places firstChain := by
  intro _
  refine ⟨⟨(trees_at_head h.toAtMg 0).1, (trees_at_head h.toAtMg 0).2,
    (width_all_head h.toAtMg 0).1, (width_all_head h.toAtMg 0).2⟩, (seeds_at_members h 0).1,
    (seeds_at_members h 0).2, (seeds_at_second_move h 0).1, (seeds_at_second_move h 0).2, ?_⟩
  intro matrix tableCoins input coins challenges hst
  have hdue : drawsFit (F0T OnBytes.secondHashFunction returned.Z places firstChain).roundsDeclaredByBlocks.2.1
      challenges.shared = true := by
    have h2 := hst.2.1
    simp only [Draws.due, Bool.and_eq_true] at h2
    exact h2.1.1.2
  refine ⟨fun a stand ha hm => ?_, fun stand hm => ?_, fun m hm => second_move_u h hdue hm 0,
    fun m hm => second_move_omega h hdue hm 0⟩
  · obtain ⟨d, hl, hh⟩ := point_at_walk h hdue
      (by rcases ha with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩) hm
    exact ⟨d, hl, fun _ _ _ _ ht => heardFrom_grows hh ht⟩
  · obtain ⟨d, hl, hh⟩ := zeta_at_walk h hdue rfl hm
    exact ⟨d, hl, fun _ _ _ _ ht => heardFrom_grows hh ht⟩

/-- **It holds at the return of the maker from which the honest prover for a request is made**, at
whatever places and first chain: under the proposition's own premise PlayedAt these are the
hypothesis's. h: the library's hypothesis at these files, at some public part, places and chain. -/
theorem k14_row_at_return (Served : FullSizeMatrix → LPFD.Full.XF → Prop) {returned : OnlineReturn files}
    (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
    (h : AtMgA OnBytes.secondHashFunction files D r Zp Np cF x₀)
    (hA : ProofFile.Honest.Term.onlineMaker files = .ok returned) :
    K14RowIsWholeAtServedRuns Served returned places firstChain := by
  intro hP
  obtain ⟨eZ, -⟩ := ProofFile.Honest.Term.k14_at_term h hA
  subst eZ
  obtain ⟨_, _, O⟩ := h.laid.opened
  obtain rfl : Np = places := Except.ok.inj (h.laid.places.symm.trans hP.places)
  obtain rfl : cF = firstChain :=
    Except.ok.inj ((ToldDesc.pureChainAt_of_open O).symm.trans hP.chain)
  exact k14_row_is_whole Served returned Np cF h hP

end AtFullSide.K14

#print axioms AtFullSide.K14.heard_at_shared_walk
#print axioms AtFullSide.K14.front_le
#print axioms AtFullSide.K14.take_drop_one
#print axioms AtFullSide.K14.point_at_walk
#print axioms AtFullSide.K14.zeta_at_walk
#print axioms AtFullSide.K14.seeds_at_members
#print axioms AtFullSide.K14.seeds_at_second_move
#print axioms AtFullSide.K14.heardFrom_grows
#print axioms AtFullSide.K14.midSharedBehindFirstW
#print axioms AtFullSide.K14.heard_behind_first
#print axioms AtFullSide.K14.apart_of_nodup
#print axioms AtFullSide.K14.written_places_apart
#print axioms AtFullSide.K14.places_apart_at_head
#print axioms AtFullSide.K14.behind_first_at_head
#print axioms AtFullSide.K14.second_move_u
#print axioms AtFullSide.K14.second_move_omega
#print axioms AtFullSide.K14.K14RowIsWholeAtServedRuns
#print axioms AtFullSide.K14.k14_row_is_whole
#print axioms AtFullSide.K14.k14_row_at_return
