-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHEval.lean: the claim (Eval) behind W's sending, at number 17 of the key file's first chain,
at the thread `T₁`: the row that the text lays on W says its claim of the words that the part lays.

  `fold_rest`: a fold's leftover rounds are what stands behind the rounds that its sub-protocols
    declare.
  `HeardOfFold`: the verifier's state behind the two lookups holds the claims at the prover's points:
    the named sentence, on the fold alone. `HeardAtKeys` at a stand follows by `heard_at_stand`.
  `WPublic`: the closed facts on W's shape at the written sizes.
  `w_text`: what a yes of W's sub-protocol says.
  `back_of_stand`: a stand at border 17 comes from a yes of the batching at the verifier's state in
    front: the one step back, out of the clause `Made`.
  `weights_of_stand`: the claim's weights are those of which W's job makes W.
  `eval_item`: the item.

Limits. `HeardOfFold` is a premise. Nothing on any property.
-/
import E2E.FirstHPileItem
import E2E.FirstHWRow
import E2E.KeyWIs
import Johnson.Desc.K13.Law.M4
import Johnson.Desc.K13.Law.Agree
import Johnson.RunOne.KeySeam1
import Johnson.Desc.K15.FoldInv
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Place noDigest foldBlocks)
open VerifiableInference.Desc.Key (Xi FirstState Claim ChainState KItem Source LaterPlaces start₁
  sendW sendingSeat withLoc batchWhere batchLens pieces Pieces lens_get layPile TensorRowHolds matOf
  mkOf valOf RowHolds ownB shape₁_iff)
open Johnson.RunOne.KeyRows23 (core₁_own)
open VerifiableInference.Desc.K1 (decideSend)
open VerifiableInference.Desc.K13 (battRounds batt)
open VerifiableInference.Desc.K13.Law (ρg Holds Wit rows_ok OnLedger AgreeAt holds_congr
  rowOf_onLedger onLedger_of_fit)
open VerifiableInference.Desc.Keeps (ebind_ok emap_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ pend_law)
open AtPublicFiles.KeyThread (D one₀ rowsFirst)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced keysAt sentAt sendWAt groupsW)
open AtPublicFiles.KeyValues (keyPoints batchedRowsSending oneOf battAt blocksOf matrixEntryOf firstW)
open AtPublicFiles.Key (pileOf pile_same elemAt wWeights BattAt wJob HeardIs handed_is ties_of_batt
  BattTies eval_iff_held evalIn_of_rows)
open AtPublicFiles.KeyBook (rideW)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob proverSideOfSending rowsLaid lentCut dueR rowsLaid_part)

/-- **A fold's leftover rounds stand behind the rounds that its sub-protocols declare.** -/
theorem fold_rest {S Cl : Type} (ft : Nat) : ∀ (l : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (t : S) (r : List Fmt.RoundView) (c : List OpenedColumn),
    foldBlocks ft l s rs cols = .ok (t, r, c) →
    ∃ pre, rs = pre ++ r ∧ pre.length = (l.flatMap (·.rounds)).length
  | [], s, rs, cols, t, r, c, h => by
    have e : (s, rs, cols) = (t, r, c) := Except.ok.inj h
    cases e
    exact ⟨[], rfl, rfl⟩
  | b :: l, s, rs, cols, t, r, c, h => by
    obtain ⟨s', k, hl, -, h'⟩ := VerifiableInference.Desc.foldBlocks_cons ft b l s rs cols _ h
    obtain ⟨pre, e, hp⟩ := fold_rest ft l s' _ _ t r c h'
    refine ⟨rs.take b.rounds.length ++ pre, ?_, ?_⟩
    · rw [List.append_assoc, ← e, List.take_append_drop]
    · rw [List.length_append, hl, hp, List.flatMap_cons, List.length_append]

/-- The reader by number reads the elements of a challenge alone. -/
theorem elemAt_bare (seen : List Fmt.RoundView) (i : Nat) :
    elemAt (seen.map fun z => (noDigest z).drawn) i = elemAt (seen.map (·.drawn)) i := by
  unfold elemAt
  simp only [List.getElem?_map]
  cases seen[i]? <;> rfl

/-- **The claims on the keys at the prover's points, on the fold alone.** The verifier's state that
the first sixteen sub-protocols leave, from the chain's start, over the rounds seen, holds its claims
at the points that the prover makes of these rounds' challenges. -/
def HeardOfFold (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) : Prop :=
  ∀ (x : Xi) (seen : List Fmt.RoundView) (cols : List OpenedColumn) (s : FirstState) (r : List Fmt.RoundView)
    (c : List OpenedColumn), foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 16) ((D Xs N Pl).start₁ x) seen cols =
      .ok (s, r, c) → ∀ tail, HeardAtKeys Xs N (seen.map (·.drawn) ++ tail) s

/-- **The closed facts on W's shape.** -/
structure WPublic (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) : Prop where
  answers : (oneOf Xs).lin.w.answers ≠ 0
  maskRows : (oneOf Xs).lin.w.maskRows ≠ 0
  mainDeg : (oneOf Xs).lin.w.mainDeg = 3
  bits : (oneOf Xs).lin.kCol ≤ (linLayW (oneOf Xs).codes (oneOf Xs).lin).bits
  room : ∀ e < 2 ^ (oneOf Xs).lin.kCol,
    (linLayW (oneOf Xs).codes (oneOf Xs).lin).index e % 2 ^ ceilLog2 (oneOf Xs).lin.w.mainRows <
        (oneOf Xs).lin.w.mainRows ∧
      (linLayW (oneOf Xs).codes (oneOf Xs).lin).index e / 2 ^ ceilLog2 (oneOf Xs).lin.w.mainRows <
        ((oneOf Xs).codes.base.getD (oneOf Xs).lin.w.code default).ell
  base : (roundsInFront (blocksOf Xs N) (⟨1, none, pieces.batt, .K13⟩ : Place)).getD 0 =
    roundsTo (D Xs N Pl).first.blocksInOrder 16

section Text
variable {β Cl : Type}

/-- **What a yes of W's sub-protocol says.** -/
theorem w_text {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)}
    {bw : Block (ChainState β) Cl} (hb : sendW one N sent groups = some bw) {s s' : ChainState β}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : bw.decide s [r₁, r₂] gs = .ok s') :
    ∃ (msg : Array OracleNotice) (l : LinFirst) (ids : Array Nat)
      (d' : _root_.Desc.Plain.DState (Array Nat)) (d : VerifiableInference.Desc.K13.St)
      (o : LinFirst × VerifiableInference.Desc.K13.St),
      decideSend (VerifiableInference.Desc.Key.sendingPar one N.w "W and what rides with it" msg groups)
        s.debt (withLoc s.d #[]) [r₁, r₂] = .ok (ids, d') ∧ d.st = d'.st ∧ s.lin = some l ∧
      VerifiableInference.Desc.K13.rows (batchWhere one N sent).lin l.claim ids d = .ok o ∧
      s'.lin = some o.1 ∧ s'.d = o.2 := by
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none =>
    rw [hm] at hb
    cases hb
  | some msg =>
    rw [hm] at hb
    have hb' := Option.some.inj hb
    subst hb'
    obtain ⟨m₃, h₃, hr⟩ := ebind_ok h
    obtain ⟨m₂, h₂, hq₂⟩ := ebind_ok h₃
    obtain ⟨m₁, hq₁, hk⟩ := ebind_ok h₂
    obtain ⟨_, _, hq₁⟩ := bind_ok hq₁
    obtain rfl : s = m₁ := Except.ok.inj hq₁
    obtain ⟨ids, d', hd, e1, e2⟩ := Johnson.RunOne.KeyKeeps.k1At_sent hk
    obtain ⟨y, -, he⟩ := emap_ok hk
    have eL : m₂.lin = s.lin := by
      rw [← he]
    have e₃ := Except.ok.inj hq₂
    obtain ⟨p, hp, hr⟩ := bind_ok hr
    obtain ⟨-, rfl⟩ := (lens_get _ _).1 (VerifiableInference.Desc.K13.part_ok hp)
    obtain ⟨l, hl, hr⟩ := bind_ok hr
    obtain ⟨o, ho, hr⟩ := bind_ok hr
    have hl' : m₃.lin = some l := VerifiableInference.Desc.K13.there_ok hl
    have eL₃ : m₃.lin = s.lin := by
      rw [← e₃]
      exact eL
    have eI : m₃.ids = ids := by
      rw [← e₃]
      exact e2
    have eD : m₃.d = m₂.d := by
      rw [← e₃]
    refine ⟨msg, l, ids, d', m₃.d, o, hd, ?_, eL₃.symm.trans hl', ?_, ?_, ?_⟩
    · rw [eD]
      exact e1
    · rw [← eI]
      exact ho
    · rw [← Except.ok.inj hr] <;> rfl
    · rw [← Except.ok.inj hr] <;> rfl

end Text

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- **`HeardAtKeys` at a stand at border 16.** -/
theorem heard_at_stand (hF : HeardOfFold Xs N Pl) {k : Coins Bk} {s : FirstState}
    {m : Mid (In1 W₀ Rc) X'} {E : Env} (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 16 k s m E)
    (tail : List Fmt.Drawn) : HeardAtKeys Xs N (m.st.heard ++ tail) s := by
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hT.2.2.2.2.1
  have hb : s₀ = (D Xs N Pl).start₁ m.st.input.x := hbeg
  subst hb
  have e := hF m.st.input.x m.seen cols s [] [] hfold tail
  rw [hseen] at e
  exact e

/-- **The one step back.** -/
theorem back_of_stand (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hF : HeardOfFold Xs N Pl) {k : Coins Bk}
    {s : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 17 k s m E) :
    ∃ (t : FirstState) (rows : List TensorRow) (out : TensorRow × VerifiableInference.Desc.K13.St)
      (msg : Array OracleNotice) (pre rest : List Fmt.RoundView),
      m.seen = pre ++ rest ∧ pre.length = roundsTo (D Xs N Pl).first.blocksInOrder 16 ∧
      (∀ tail, HeardAtKeys Xs N (m.st.heard ++ tail) t) ∧
      layPile keysAt (oneOf Xs) t = .ok { t with pile := rows } ∧
      memberRowsFit t.d.st (oneOf Xs).lin t.idx rows = true ∧
      batt t.debt (oneOf Xs).lin.kCol
        (batchWhere (oneOf Xs) pieces (sentAt Xs.Y.D.1)).rows rows t.idx t.d
        (rest.map noDigest) = .ok out ∧
      s = { t with pile := rows, atEnd := true, owed := none, msgW := msg,
                   lin := some { claim := memberClaim out.1 }, d := out.2 } := by
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hT.2.2.2.2.1
  have hb₀ : s₀ = (D Xs N Pl).start₁ m.st.input.x := hbeg
  subst hb₀
  obtain ⟨blk, hb, hr, -, -, -, hdecide⟩ :=
    batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  have etake : (Th Xs N Pl K f Q w₀ rc x).bs.take 17 =
      (Th Xs N Pl K f Q w₀ rc x).bs.take 16 ++ [blk] := take_succ_some hb
  have hfold' : foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 16 ++ [blk])
      ((D Xs N Pl).start₁ m.st.input.x) m.seen cols = .ok (s, [], []) := by
    have e := hfold
    rw [etake] at e
    exact e
  obtain ⟨t, rest, c, h1, h2⟩ := Johnson.Desc.First.Walk.Tied.fold_split 0 [blk] _ _ _ _ _ hfold'
  obtain ⟨s₁, kk, -, hstep, hlast⟩ := VerifiableInference.Desc.foldBlocks_cons 0 blk [] t rest c _ h2
  have elast : (s₁, rest.drop blk.rounds.length, c.drop kk) = (s, [], []) := Except.ok.inj hlast
  obtain ⟨rfl, e2⟩ := Prod.mk.inj elast
  have erest : rest.drop blk.rounds.length = [] := (Prod.mk.inj e2).1
  have etk : rest.take blk.rounds.length = rest := by
    have := List.take_append_drop blk.rounds.length rest
    rw [erest, List.append_nil] at this
    exact this
  rw [etk] at hstep
  obtain ⟨hfit, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ blk t s₁ _ _ _ hstep
  have hlenrs : (rest.map noDigest).length =
      (battRounds (batchWhere (oneOf Xs) pieces (sentAt Xs.Y.D.1))).length := by
    have e := VerifiableInference.Desc.K13.Law.roundsFit_length _ _ hfit
    rw [hr, hp.batt] at e
    rw [List.length_map]
    exact e
  obtain ⟨rows, out, msg, hlay, hfits, -, hbt, rfl⟩ := seat_rounds_said keysAt (oneOf Xs) pieces
    (sentAt Xs.Y.D.1) t _ _ gs hlenrs ((hdecide _ _ _).symm.trans hdec)
  obtain ⟨pre, epre, hpre⟩ := fold_rest 0 _ _ _ _ _ _ _ h1
  refine ⟨t, rows, out, msg, pre, rest, epre, ?_, fun tail => ?_, hlay, hfits, hbt, rfl⟩
  · exact hpre
  · have e := hF m.st.input.x m.seen cols t rest c h1 tail
    rw [hseen] at e
    exact e

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.fold_rest
#print axioms AtPublicFiles.FirstH.elemAt_bare
#print axioms AtPublicFiles.FirstH.w_text
#print axioms AtPublicFiles.FirstH.heard_at_stand
#print axioms AtPublicFiles.FirstH.back_of_stand
