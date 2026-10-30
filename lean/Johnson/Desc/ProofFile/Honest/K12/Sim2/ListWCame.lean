-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: at a called part of the request's own test the state on entry holds a mask.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWCame.lean: CONDITIONAL on the head and a run. Statements
with their proofs; no definition.

Can the hypotheses be met together at a real run? NOT KNOWN: that ready and runC return at a prover
and a book under the head, and that the part is called, is not shown here.

What is here. THE CLAUSE came (`FrontAsksD`.came, `ShapeAsksD`.came: "the state on entry holds a
mask's
number") AT A CALLED PART OF THE REQUEST's OWN PROXIMITY TEST on the proof file's last chain: PAID,
from the head and the run alone. With `own_test_door_returns` that is the whole of what the arm (β)
owes at this test's SECOND part: On shuts `doorW`'s fall-back state out through came, and at the
called second part the door's text returns and came holds. Of the first part nothing is said here:
there On asks only that the field holds columns.

  `last_chain_is_four`   the description's last chain is four blocks. A twin of `second_flat`
      (K12/AtFile/WLetter.lean, not in this ground).
  `two_blocks_yes`   a fold over two blocks: each one's yes. A twin of `fold_two` (WTreesSentBeforeTest.lean).
  `start_is_the_records`   a yes of the description's start of the last chain is `start₃E`'s at what
  the
      first chain's last record names. A twin of `start_of_F0T` (WEnds.lean).
  `front_of_own_test_is_two`   the blocks in front of the block at `placeW` are the first two.
  `masks_ahead_at_head`   under the head the plan's shape sends the masks ahead.
  `mask_behind_the_fold`   under the head: the start's yes and the fold's yes over the blocks in
  front
      of the test give a state that holds a mask's number.
  `came_at_called_part`   **the clause**, in `door_at_own_test`'s letters.
  `own_test_door_returns`   **AT THE CALLED SECOND PART THE FALL-BACK IS NOT TAKEN**: the door's
  text
      returns, with the two ends, the start's state, the columns and the fold's state ALL TIED TO
      THE
      RUN; the state on entry holds a mask's number and is not `idleT12`.
  `own_test_door_tied`   the same tie AT EITHER PART (the number of rounds in front is free), at
  every
      front with the stand's rounds and THE STAND's FIELD.
WHAT LAY ALREADY: `door_own_at_called` (K12/DoorLastAtRun.lean): at a called part of
the
last chain, general in the part, the door is at hand (`atHandLast` … = true) at such fronts: "its
default is not taken there". WHAT IS NEW BESIDE IT: the two ends, the start's state, the columns and
the
fold's state under their four ties to the run; that the state on entry is `enterOwn`'s at that
state;
that it holds a mask's number (came); that it is not `idleT12`; that the blocks in front are K14's
second part and the sources' block.

By. `last_blocks_in` (Johnson/ToldDescR/LastBlocks.lean) · `foldBlocks_cons`, `step_inv`
(Johnson/Desc/K15/FoldInv.lean) · `hstart_at` (Johnson/Desc/Plain/StartThreeAtPure.lean) · `at_door`
(Johnson/Desc/Third/Law/AtDoor.lean) · `start_mask_ahead` (Johnson/Desc/Third/Law/Mask.lean) ·
`p₁₄Z_masksAhead` (Johnson/Desc/Third/Law/MasksAhead.lean) · `pub_chainsOf`
(Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean) · `stateAtOwnTest_at_stand` (Sim2/DoorWAt.lean).

Limits. Of the walk (runC) and of a called part, not of play. One clause of eight of `FrontAsksD`. A
fact on the verifier's own state: it reads no index, no randomness and no coin. The format's second
hash function alone. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListW
import Johnson.ToldDescR.LastBlocks
import Johnson.Desc.Plain.StartThreeAtPure
import Johnson.Desc.Third.Law.MasksAhead
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.ProofFile.Law.PlainIsPlanned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn Place foldBlocks foldBlocks_cons step_inv)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart takenSources end₃ start₃E start₃F firstOfS
  sharedOfEnd)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ToldDesc (ownAt)

/-- **The description's last chain is these four blocks**, each carried to the file's type of
claims.
-/
theorem last_chain_is_four (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain P5J.TS ProofFile.Cl) : (P5J.F0T o Zp Np cF).second.blocksInOrder =
    [batchLinearConstraintsSecondPart (ToldDesc.p14At Zp), takenSources (ownAt Np), ownAt Np,
      end₃ [batchLinearConstraintsSecondPart (ToldDesc.p14At Zp), takenSources (ownAt Np), ownAt Np]].map Block.retype :=
  ToldDesc.last_blocks_in o ProofFile.pureRoad.links Zp _ Np cF

/-- **Two blocks behind one another: each one's yes.** -/
theorem two_blocks_yes {S Cl : Type} (ft : ℕ) (a b : Block S Cl) (s₀ s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : foldBlocks ft [a, b] s₀ rs cols = .ok (s, [], [])) :
    ∃ s₁ r₁ g₁ r₂ g₂, a.decide s₀ r₁ g₁ = .ok s₁ ∧ b.decide s₁ r₂ g₂ = .ok s := by
  obtain ⟨s₁, k, -, h1, h⟩ := foldBlocks_cons ft a [b] s₀ rs cols _ h
  obtain ⟨s₂, k', -, h2, h⟩ := foldBlocks_cons ft b [] s₁ _ _ _ h
  have e : s₂ = s := congrArg (·.1) (Except.ok.inj h)
  subst e
  exact ⟨s₁, _, _, _, _, (step_inv _ _ _ _ _ _ _ h1).2.2.2, (step_inv _ _ _ _ _ _ _ h2).2.2.2⟩

variable {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **A yes of the description's start of the last chain.** -/
theorem start_is_the_records {q : ProofFile.InstPub} {e₁ : P5J.TS} {e₂ : Desc.K14.St} {s₀ : S₃}
    (h : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂ = .ok s₀) :
    ∃ f e, firstOfS e₁ = some f ∧ Desc.K14.ended e₂ = some e ∧
      start₃E (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S f.st f.book f.roots f.w f.own f.mask
        f.pending (sharedOfEnd e) = .ok s₀ := by
  have h' : ((ProofFile.seatedAt OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂).toOption = some s₀ := by
    show ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂).toOption = some s₀
    rw [h]
    rfl
  obtain ⟨e, hd, hs⟩ := ProofFile.hstart_at OnBytes.secondHashFunction Zp Np cF (fun x => x) (fun _ _ => rfl) q e₁ e₂
    s₀ h'
  have hs' : start₃F (ToldDesc.p14At Zp) firstOfS sharedOfEnd q e₁ e = .ok s₀ := hs
  unfold start₃F at hs'
  cases hf : firstOfS e₁ with
  | none =>
    rw [hf] at hs'
    cases hs'
  | some f =>
    rw [hf] at hs'
    exact ⟨f, e, rfl, hd, hs'⟩

/-- **The blocks in front of the block at the test's place are the chain's first two.** -/
theorem front_of_own_test_is_two {b : Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T
                OnBytes.secondHashFunction Zp Np cF).Cl}
    {pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)}
    (hcut : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre ++ b :: t) (hb : b.place = placeW) :
    pre = [(batchLinearConstraintsSecondPart (ToldDesc.p14At Zp) : Block S₃ Unit).retype,
      (takenSources (ownAt Np) : Block S₃ Unit).retype] := by
  rw [last_chain_is_four] at hcut
  simp only [List.map_cons, List.map_nil] at hcut
  rcases pre with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l⟩⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at hcut
    obtain ⟨rfl, -⟩ := hcut
    exact absurd (show (⟨3, none, 0, .K14⟩ : Place) = placeW from hb) (by decide)
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hcut
    obtain ⟨-, rfl, -⟩ := hcut
    exact absurd (show (⟨3, none, 1, .frame⟩ : Place) = placeW from hb) (by decide)
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hcut
    obtain ⟨rfl, rfl, -⟩ := hcut
    rfl
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hcut
    obtain ⟨-, -, -, rfl, -⟩ := hcut
    exact absurd (show (⟨3, none, 3, .frame⟩ : Place) = placeW from hb) (by decide)
  · simp only [List.cons_append] at hcut
    injection hcut with _ h1
    injection h1 with _ h2
    injection h2 with _ h3
    injection h3 with _ h4
    exact absurd h4.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}

/-- **Under the head the plan's shape sends the masks ahead.** -/
theorem masks_ahead_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    (ToldDesc.p14At Zp).S.masksAhead = true :=
  OnBytes.Model.Verify.p₁₄Z_masksAhead (ProofFile.Law.pub_chainsOf h.laid.pub)

/-- CONDITIONAL on the head, the cut, the start's yes and the fold's yes. **The state behind the
blocks in front of the test holds a mask's number.** -/
theorem mask_behind_the_fold (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    {b : Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl}
    {pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)}
    (hcut : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre ++ b :: t) (hb : b.place = placeW)
    {q : ProofFile.InstPub} {e₁ : P5J.TS} {e₂ : Desc.K14.St} {v₀ s : S₃}
    (hstart : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂ = .ok v₀) {ft : ℕ} {rs : List Fmt.RoundView}
        {cols : List OpenedColumn}
    (hfold : foldBlocks ft pre v₀ rs cols = .ok (s, [], [])) : s.loc.mask.isSome = true := by
  rw [front_of_own_test_is_two hcut hb] at hfold
  obtain ⟨s₁, r₁, g₁, r₂, g₂, h1, h2⟩ := two_blocks_yes _ _ _ _ _ _ _ hfold
  obtain ⟨f, e, -, -, hs⟩ := start_is_the_records hstart
  have h1' : (batchLinearConstraintsSecondPart (Cl := Unit) (ToldDesc.p14At Zp)).decide v₀ r₁ g₁ = .ok s₁ := h1
  have h2' : (takenSources (ownAt Np) : Block S₃ Unit).decide s₁ r₂ g₂ = .ok s := h2
  have hm := (VerifiableInference.Desc.Third.Law.at_door (ToldDesc.p14At Zp) (ownAt Np) _ _ _ _ _ _
      _
    _ v₀ s₁ s r₁ r₂ g₁ g₂ hs h1' h2').2.2.2
  rw [hm, VerifiableInference.Desc.Third.Law.start_mask_ahead _ _ _ _ _ _ _ _ _ _ _ hs]
  exact masks_ahead_at_head h

/-- CONDITIONAL on the head, ready, runC, the job's door, where the part stands, and that it is
called. **THE CLAUSE came AT A CALLED PART**: at the stand that the walk returns and the part's own
front, the job's state on entry holds a mask's number. -/
theorem came_at_called_part (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    {W₀ Rc Tr Ky X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J.rec₀ = doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (·.x) enterOwn placeW idleT12)
    (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl V (Local W₀
                                Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
    (S : StandsAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder R.second σ u pre t (firstLen
                             J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = placeW) :
    ∃ m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y,
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok
          (some m) ∧
      (J.rec₀ m.st.input (restFront J m)).mask.isSome = true := by
  obtain ⟨m, hm, hdoor⟩ := door_at_own_test h.laid.planOk hR hrun J hJ σ u pre t S hc ha
  obtain ⟨e₁, e₂, v₀, s, cols, -, -, hstart, hfold, hst⟩ :=
    stateAtOwnTest_at_stand h.laid.planOk hR hrun σ u pre t _ S hc ha
  refine ⟨m, hm, ?_⟩
  rw [hdoor, hst]
  exact mask_behind_the_fold h S.cut ha hstart hfold

/-- CONDITIONAL on the head, ready, runC, where the part stands, and that it is called. **AT A
CALLED
PART OF THE TEST, THE FIRST OR THE SECOND (i is free), THE DOOR IS TIED TO THE RUN's OWN FOLD.** e₁,
e₂:
the run's own ends of the two earlier chains. v₀: what the description's start makes of them. cols:
the columns that the run's own reads fill. s: the state of the fold from v₀ over the blocks in
front,
at the run's own rounds and these columns; it holds a mask's number. At every front with the stand's
rounds up to some k behind these blocks AND WITH THE STAND's FIELD, `doorW`'s state at the stand's
input is `enterOwn`'s at s, and is not `idleT12`. -/
theorem own_test_door_tied (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    {W₀ Rc Tr Ky X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl V (Local W₀
                                Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
        (i : ℕ)
    (S : StandsAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder R.second σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = placeW) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (e₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁) (e₂ :
                          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂) (v₀ s : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (cols :
                                                      List OpenedColumn),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok
          (some m) ∧
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x) e₁ e₂ = .ok
          v₀ ∧
      fillCols (readsOf 2 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber (P.storedWords w₀ rc)
        (treeThird r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols ∧
      foldBlocks (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      s.loc.mask.isSome = true ∧
      ∀ (fr : Front Y) (n : ℕ),
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
          (pre.flatMap (·.rounds)).length ≤ n →
        fr.seen.rounds = m.seen.take n → fr.seen.opened = m.opened →
        enterOwn s = .ok (doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun w : Local W₀ Rc ProofFile.Inst Tr
                        => w.x) enterOwn placeW idleT12
          m.st.input fr) ∧
        doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) enterOwn
            placeW idleT12 m.st.input fr ≠
          idleT12 := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlen, -, he₁, he₂, hst, hfold, hfill, hd⟩ :=
    door_last_with_columns h.laid.planOk hR σ u pre t i S hrun hc
  have hn := (places_nodup (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1
      h.laid.planOk).places).2.2
  have hcut : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW) = pre :=
      by
    rw [← ha, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  have hmask : s.loc.mask.isSome = true := mask_behind_the_fold h hcut ha hst hfold
  refine ⟨m, e₁, e₂, v₀, s, cols, hm, he₁, he₂, hst, hfill, hfold, hmask,
    fun fr n hk hfr hop => ?_⟩
  have hx : (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input = x := by rw [hin]
  have hdoor := hd (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input enterOwn fr n hx hk hfr hop
  have hrec : enterOwn s = .ok (doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (fun w : Local W₀ Rc
                  ProofFile.Inst Tr => w.x) enterOwn placeW idleT12
      m.st.input fr) := by
    unfold doorW doorLast
    rw [hpre, hdoor]
    rfl
  refine ⟨hrec, fun e => ?_⟩
  rw [e] at hrec
  have e2 : s.loc.mask = none := congrArg T12.mask (Except.ok.inj hrec)
  rw [e2] at hmask
  cases hmask

/-- CONDITIONAL on the head, ready, runC, the job's door, where the second part stands, and that it
is called. **AT THE CALLED SECOND PART THE DOOR's TEXT RETURNS: THE FALL-BACK IS NOT TAKEN.** e₁,
e₂:
the run's own ends of the two earlier chains. v₀: what the description's start makes of them. cols:
the columns that the run's own reads fill. s: the state of the fold from v₀ over the blocks in
front,
at the run's own rounds and these columns. The door's text `doorLastTry`, at the stand's input and
the part's own front (field and all), returns the job's state on entry; that state is `enterOwn`'s
at
s; it holds a mask's number; it is not `idleT12`. -/
theorem own_test_door_returns (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    {W₀ Rc Tr Ky X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J.rec₀ = doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (·.x) enterOwn placeW idleT12)
    (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl V (Local W₀
                                Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
    (S : StandsAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder R.second σ u pre t (firstLen
                             J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = placeW) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (e₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁) (e₂ :
                          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂) (v₀ s : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃) (cols :
                                                      List OpenedColumn),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok
          (some m) ∧
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x) e₁ e₂ = .ok
          v₀ ∧
      fillCols (readsOf 2 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber (P.storedWords w₀ rc)
        (treeThird r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((r.run.played.2.2.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols ∧
      foldBlocks (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      doorLastTry (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder (P5J.F0T OnBytes.secondHashFunction Zp Np
                               cF).shared.blocksInOrder
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW)) (P5J.F0T
                                 OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
        (fun w : Local W₀ Rc ProofFile.Inst Tr => (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T
                              OnBytes.secondHashFunction Zp Np cF).pub w.x))
        (fun w => (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub
                        w.x))
        (fun w => (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub
                        w.x)) enterOwn colsOpened m.st.input
        (restFront J m) = .ok (J.rec₀ m.st.input (restFront J m)) ∧
      enterOwn s = .ok (J.rec₀ m.st.input (restFront J m)) ∧
      (J.rec₀ m.st.input (restFront J m)).mask.isSome = true ∧
      J.rec₀ m.st.input (restFront J m) ≠ idleT12 := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlen, -, he₁, he₂, hst, hfold, hfill, hd⟩ :=
    door_last_with_columns h.laid.planOk hR σ u pre t _ S hrun hc
  have hn := (places_nodup (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1
      h.laid.planOk).places).2.2
  have hcut : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW) = pre :=
      by
    rw [← ha, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  have hx : (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input = x := by rw [hin]
  have hk : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
      (pre.flatMap (·.rounds)).length ≤ m.seen.length - firstLen J.p.nums.stages := by
    omega
  have hdoor := hd (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input enterOwn (restFront J m)
    (m.seen.length - firstLen J.p.nums.stages) hx hk rfl rfl
  have hrec : enterOwn s = .ok (J.rec₀ m.st.input (restFront J m)) := by
    rw [hJ]
    unfold doorW doorLast
    rw [hpre, hdoor]
    rfl
  have hmask : (J.rec₀ m.st.input (restFront J m)).mask.isSome = true := by
    have e : J.rec₀ m.st.input (restFront J m) =
        { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
          mask := s.loc.mask } := (Except.ok.inj hrec).symm
    rw [e]
    exact mask_behind_the_fold h hcut ha hst hfold
  refine ⟨m, e₁, e₂, v₀, s, cols, hm, he₁, he₂, hst, hfill, hfold, ?_, hrec, hmask, fun e => ?_⟩
  · rw [hpre, hdoor]
    exact hrec
  · rw [e] at hmask
    cases hmask

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.last_chain_is_four
#print axioms ProofFile.Honest.K12.Sim2.two_blocks_yes
#print axioms ProofFile.Honest.K12.Sim2.start_is_the_records
#print axioms ProofFile.Honest.K12.Sim2.front_of_own_test_is_two
#print axioms ProofFile.Honest.K12.Sim2.masks_ahead_at_head
#print axioms ProofFile.Honest.K12.Sim2.mask_behind_the_fold
#print axioms ProofFile.Honest.K12.Sim2.came_at_called_part
#print axioms ProofFile.Honest.K12.Sim2.own_test_door_tied
#print axioms ProofFile.Honest.K12.Sim2.own_test_door_returns
