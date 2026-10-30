-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/AtHandU.lean: a test that says whether the state on entry
of the proximity test on G_u fell back, and that at a called part, under the library's head, it did
not. Five definitions with code; six theorems.

Why. `doorOf` (K12/JobShared.lean) runs the description's own fold over the blocks in front, then
the way into the test; where either refuses it returns a fall-back, without a warning. `doorUF`
(K12/DoorsByShape.lean) is `doorOf` at the test on G_u. `door_at_run` (K12/DoorAtRun.lean) ends in
"the way in at d8 returns `doorUF`'s value": that sentence alone does not say that the fold which
`doorOf` makes has returned. Its proof has that fact, from `door_of_cols` (K12/DoorAtWalk.lean), and
does not state it. Here it is stated.

  `doorTryOf`, `atHandOf`   the fold, then the way in, with their refusals; both return. General,
                 as `doorOf`
  `doorOf_try`   `doorOf` is what `doorTryOf` returns; the fall-back where it refuses
  `doorTryU`, `atHandU`, `doorUF_try`   the three at the test on G_u
  `atHandU_at_run`   `door_at_run`'s hypotheses and first three clauses; then, at every front that
                 has seen the eight's rounds as the stand has: `atHandU` is true; `doorTryU` is the
                 way in at d8; that is `doorUF`'s value
  `atHandAtU`    the test at the letters of the half's own job (`realU`, HalfU.lean in this folder),
                 off the public part: to be printed beside a play. False where these are not made
  `p14At_at_head`   under the head the frame's parameters of the shared chain are the head's
  `realU_rec`    the real job's state on entry is `doorUF` at the letters of `atHandAtU`
  `atHandAtU_at_run`   `atHandU_at_run` at these letters

Four names of one family. `atHandZ`, `atHandL` (K12/Blind/DoorL.lean) and `atHandAtL`
(LotAtDoor.lean in this folder) are of the first chain's test, at made-up columns: the state there
agrees with the fold's once wiped; `atHandOf`, `atHandU`, `atHandAtU` are of `doorOf`, at columns
that a reader makes, nothing wiped.

Limits.
- "At hand" is "the fold and the way in return". It does not say that the state is the verifier's.
  What ties d8 to a run is the third clause: the same fold at the run's own shared view returns d8.
- The proof of `atHandU_at_run` is the text of `door_at_run`'s a second time, with one fact kept.
  If that proof turns, this one does not follow.
- All hypotheses of `door_at_run` stay: the head; hb, h9, on the eight; hα, on the prover's key; on
  the filling and the book (hR, S); on the run (hrun, hc). Nothing on whether `ready` or `runC`
  returns or a part is called.
- `atHandAtU_at_run` has two more. hst: the prover's stored words are the filling's columns as
  words; how the frame makes the one of the other is not read here. ha: the frame's count of the
  rounds in front returns: a public test; where it fails `halfU` is empty and `atHandAtU` false.
- Nothing is evaluated here. The test on G_u alone.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, soundness or hiding.
Over what it stands. HalfU.lean and, beneath it, Bare.lean, Members.lean, Doors.lean in this folder,
and the frame's authors' Johnson/Desc/ProofFile/Honest/SharedChainProverSides.lean, whose `p14At` and
`sharedInFront` are called here by name.
Also beneath this file: K12/LiveField.lean and, of the frame's authors
(Johnson/Desc/ProofFile/Honest/): Blind, Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW,
WalkHeard, WalkLive, WalkOpened, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt, Law/Rule/OpenedStep,
Law/WalkMid.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAtRun
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12 Seat.enter)
open Desc.K14 (P14 St blocks first)
open Desc.K14.Honest (flatOf_carried)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  midSharedAtW)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

section
variable {S₀ W X : Type}

/-- **The state on entry, tried**: the fold that `doorOf` makes, then the way in. A refusal where
either refuses. -/
def doorTryOf (bs : List (Block S₀ Unit)) (s₀ : W → S₀) (enter : S₀ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) : Except String T12 :=
  (foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr)).bind fun x => enter x.1

/-- **The state on entry is at hand**: both return. -/
def atHandOf (bs : List (Block S₀ Unit)) (s₀ : W → S₀) (enter : S₀ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) : Bool :=
  (doorTryOf bs s₀ enter cols w fr).toOption.isSome

/-- `doorOf` is what `doorTryOf` returns; `fall` where it refuses. -/
theorem doorOf_try (bs : List (Block S₀ Unit)) (s₀ : W → S₀) (enter : S₀ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (fall : T12) (w : W) (fr : Front X) :
    doorOf bs s₀ enter cols fall w fr = (doorTryOf bs s₀ enter cols w fr).toOption.getD fall := by
  unfold doorOf doorTryOf
  cases foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) <;> rfl

/-- `doorTryOf` at the test on G_u. -/
def doorTryU (Q : P14) (bs : List (Block St Unit)) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) : W → Front X → Except String T12 :=
  doorTryOf bs (fun w => first Q.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols

/-- `atHandOf` at the test on G_u. -/
def atHandU (Q : P14) (bs : List (Block St Unit)) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) : W → Front X → Bool :=
  atHandOf bs (fun w => first Q.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols

theorem doorUF_try (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit))
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    doorUF Q sentU bs key cols w fr =
      (doorTryU Q bs key cols w fr).toOption.getD (fallU Q sentU) :=
  doorOf_try _ _ _ _ _ _ _

end

/-- **At a called part of the side at the test on G_u, under the head: the fall-back is not
taken.** `door_at_run`'s hypotheses and its first three clauses. Then, at every front that has seen
the eight's rounds as the stand has, at every value of the front's field `opened`: `atHandU` is
true; `doorTryU` is the way in at d8; and that is `.ok` of `doorUF`'s value (`door_at_run`'s own
clause). -/
theorem atHandU_at_run {W₀ Rc Tr X₀ Y V Pb X : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre t : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (d8 : St) (rest : List Fmt.RoundView)
      (more : List OpenedColumn),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length + i ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest, more) ∧
      ∀ fr : Front X, fr.seen.rounds =
          m.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length →
        atHandU (K1.qAt Zp Np) [b1, b2, b3, b4, b5, b6, b7, b8]
            (fun w : Common W₀ Rc TableKey => w.key)
            (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
            m.st.input fr = true ∧
        doorTryU (K1.qAt Zp Np) [b1, b2, b3, b4, b5, b6, b7, b8]
            (fun w : Common W₀ Rc TableKey => w.key)
            (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
            m.st.input fr = Seat.enter (·.gU) (·.firstMask) d8 ∧
        Seat.enter (·.gU) (·.firstMask) d8 =
          .ok (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
            (fun w : Common W₀ Rc TableKey => w.key)
            (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
            m.st.input fr) := by
  obtain ⟨m, s, cols, more, rest, hm, hin, hrounds, hlen, hcols, hfold, hfill⟩ :=
    called_at_run h.laid.planOk hR σ u pre t i S hrun hc
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  subst epre
  have eR : [x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  have hlen : m.seen.length =
      (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds)).length +
        i := hlen
  have hfold' : foldBlocks 0 ([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl))
      (first (K1.qAt Zp Np).codes x.pub.key)
      (m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
        (·.rounds)).length) cols = .ok (s, [], []) := hfold
  have hfill : ProofFile.Honest.fillCols (ProofFile.Honest.readsOf 1 0 (P.storedWords w₀ rc)
            (ProofFile.Honest.treeOwn (r.run.played.2.1.take
                    (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
                      (·.rounds)).length))
            (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds))
            ((m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
              (·.rounds)).length).map (·.drawn))) [] = .ok cols := hfill
  rw [eR] at hlen hfold' hfill
  obtain ⟨g1, g2⟩ := door_of_cols (V := Common W₀ Rc TableKey) (X := X) Zp.p.chains (K1.qAt Zp Np)
    (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb (facts_at_head h).2.2 _
    (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 .nil))))))))) 1 (P.storedWords w₀ rc) _ x.pub.key _ cols s hfold' hfill
  have gE := Desc.K14.Honest.peel_front Zp.p.chains 0 _ _ _ _ _
    (Desc.K14.Honest.fold_like 0 _ _ (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5
      (.cons l6 (.cons l7 (.cons l8 .nil))))))))) _ _ _ _ hfold')
  have hview := foldBlocks_more 0 _ _ _ _ _ gE
    (m.seen.drop ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length ++ rest) more
  rw [← List.append_assoc, List.take_append_drop, ← hrounds, ← hcols] at hview
  refine ⟨m, s, _, more, hm, hlen, hview, fun fr hfr => ?_⟩
  have hk : m.st.input.key = x.pub.key := by
    rw [hin]
    exact hα x
  have hs : P.storedWords m.st.input.w₀ m.st.input.rc = P.storedWords w₀ rc := by rw [hin]
  have e2 := g2 (fun w => w.key) (fun w => P.storedWords w.w₀ w.rc) m.st.input fr hk hs hfr
  have e1 : doorTryU (K1.qAt Zp Np) [b1, b2, b3, b4, b5, b6, b7, b8]
      (fun w : Common W₀ Rc TableKey => w.key)
      (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
      m.st.input fr = Seat.enter (·.gU) (·.firstMask) s := by
    show (foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes m.st.input.key)
      fr.seen.rounds (colsLoc (K1.qAt Zp Np) (P.storedWords m.st.input.w₀ m.st.input.rc)
        fr.seen.rounds)).bind (fun y => Seat.enter (·.gU) (·.firstMask) y.1) = _
    rw [hk, hs, hfr, g1]
    rfl
  refine ⟨?_, e1, e2⟩
  show (doorTryU (K1.qAt Zp Np) [b1, b2, b3, b4, b5, b6, b7, b8]
    (fun w : Common W₀ Rc TableKey => w.key)
    (fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds)
    m.st.input fr).toOption.isSome = true
  rw [e1, e2]
  rfl

end ProofFile.Honest.K12.Light

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open ProofFile.Honest.K12.Light (atHandU colsLoc doorUF sentOf atHandU_at_run)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  midSharedAtW)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The test for the half's own job, off the public part.** False where the public letters are not
made: there `halfU` is empty. enc: the filling's columns. -/
def atHandAtU {W₀ X : Type} (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub)
    (w₁ : Common W₀ IndexCommitterCoins TableKey) (fr₁ : Front X) : Bool :=
  ((sendPub Z).bind fun A => (Desc.K14.blocks A.P).map fun bs =>
    atHandU A.P bs (fun w => w.key)
      (fun w fr => colsLoc A.P (fun i x => (enc w.w₀ w.rc i x).map (·.map OnBytes.Slice.ofF))
        fr.seen.rounds) w₁ fr₁).getD false

/-- Under the head the frame's own parameters of the shared chain are the head's. -/
theorem p14At_at_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : p14At Zp = some (K1.qAt Zp Np) := by
  unfold p14At
  rw [h.laid.places]

/-- **The real job's state on entry is `doorUF` at the letters of `atHandAtU`.** -/
theorem realU_rec {W₀ : Type} (wt : W₀ → Weights)
    (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub)
    (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) (h : realU wt enc Z = some J) :
    ∃ A bs, sendPub Z = some A ∧ Desc.K14.blocks A.P = some bs ∧
      J.rec₀ = doorUF A.P (sentOf A.P.S) bs (fun w => w.key)
        (fun w fr => colsLoc A.P (fun i x => (enc w.w₀ w.rc i x).map (·.map OnBytes.Slice.ofF))
          fr.seen.rounds) := by
  unfold realU jobRealU at h
  cases hF : four Z with
  | none => rw [hF] at h; cases h
  | some F =>
    cases hA : sendPub Z with
    | none => rw [hF, hA] at h; cases h
    | some A =>
      cases hb : Desc.K14.blocks A.P with
      | none => rw [hF, hA] at h; simp [hb] at h
      | some bs =>
        rw [hF, hA] at h
        simp only [Option.bind_some, hb, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨A, bs, rfl, hb, rfl⟩

/-- **The same at the half's own letters**, at the same fronts: at every value of the field
`opened`. hst: the prover's stored words are the filling's columns as words. ha: the frame's count
of the rounds in front returns. -/
theorem atHandAtU_at_run {W₀ Tr X₀ Y V Pb X : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl V (Common W₀ IndexCommitterCoins TableKey) X₀ Pb)
    (u : Member V (Common W₀ IndexCommitterCoins TableKey) X₀ Pb) (pre t : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F))
    (hst : ∀ w₀ rc i x, P.storedWords w₀ rc i x = (enc w₀ rc i x).map (·.map OnBytes.Slice.ofF))
    (a : ℕ) (ha : sharedInFront Zp (K14.place 1) = some a) :
    ∃ m : ProofFile.Honest.Mid (Common W₀ IndexCommitterCoins TableKey) X₀,
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      ∀ fr : Front X, fr.seen.rounds =
          m.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length →
        atHandAtU enc Zp m.st.input fr = true := by
  obtain ⟨m, d8, rest, more, a1, -, -, b⟩ :=
    atHandU_at_run (X := X) h b1 b2 b3 b4 b5 b6 b7 b8 hb hα hR σ u pre t i S h9 hrun hc
  refine ⟨m, a1, fun fr hfr => ?_⟩
  have hsp : sendPub Zp = some ⟨K1.qAt Zp Np, a⟩ := by
    unfold sendPub
    rw [p14At_at_head h, ha]
    rfl
  have hcols : (fun (w : Common W₀ IndexCommitterCoins TableKey) (fr : Front X) =>
      colsLoc (K1.qAt Zp Np) (fun i x => (enc w.w₀ w.rc i x).map (·.map OnBytes.Slice.ofF))
        fr.seen.rounds) =
      fun w fr => colsLoc (K1.qAt Zp Np) (P.storedWords w.w₀ w.rc) fr.seen.rounds := by
    funext w fr
    congr 1
    funext i x
    exact (hst _ _ _ _).symm
  unfold atHandAtU
  rw [hsp]
  show ((Desc.K14.blocks (K1.qAt Zp Np)).map fun bs =>
    atHandU (K1.qAt Zp Np) bs (fun w => w.key)
      (fun w fr => colsLoc (K1.qAt Zp Np)
        (fun i x => (enc w.w₀ w.rc i x).map (·.map OnBytes.Slice.ofF)) fr.seen.rounds)
      m.st.input fr).getD false = true
  rw [hb, hcols]
  exact (b fr hfr).1

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.Light.doorTryOf
#print axioms ProofFile.Honest.K12.Light.atHandOf
#print axioms ProofFile.Honest.K12.Light.doorOf_try
#print axioms ProofFile.Honest.K12.Light.doorTryU
#print axioms ProofFile.Honest.K12.Light.atHandU
#print axioms ProofFile.Honest.K12.Light.doorUF_try
#print axioms ProofFile.Honest.K12.Light.atHandU_at_run
#print axioms ProofFile.Honest.K12.AtProof.atHandAtU
#print axioms ProofFile.Honest.K12.AtProof.p14At_at_head
#print axioms ProofFile.Honest.K12.AtProof.realU_rec
#print axioms ProofFile.Honest.K12.AtProof.atHandAtU_at_run
