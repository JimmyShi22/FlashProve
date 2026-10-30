-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHPileItem.lean: the item "pile" behind the batching at number 16 of the key file's first
chain, at the thread `T₁`: the one row that the batching hands on is true at the thread's witness.

  `seat_rounds_said`: what a yes of the batching's sub-protocol says, at the rounds that it was handed.
  `pileOf_congr`: the pile reads its points at the real parts alone.
  `handed_true`: THE CORE: where the rounds are those that the kind's part plays, the pile's rows are
    true and the part's pile has the weights and column points of the state's rows, and the coins of
    the sum are the mask entries under the slots taken: the row that the text returns is true.
  `pile_item`: at the thread, from `HeardAtKeys` and `CoinsAtSlots`.

Limits. `HeardAtKeys` and `CoinsAtSlots` are premises. The rows' truth comes from the items kclaims in
front, which are the lookups'. Nothing on any property.
-/
import E2E.FirstHBatt
import E2E.KeyEvalBoth
import E2E.KeyPile
import Johnson.Desc.Key.KeyCoinK13
import Johnson.Desc.Key.KeyBattRow
import Johnson.Desc.K13.Honest.CodeRow
import Johnson.Desc.K13.Honest.PileReads
import Johnson.Desc.K13.Law.Then
import Johnson.RunOne.KeyPend

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Place noDigest)
open VerifiableInference.Desc.Key (Xi FirstState Claim ChainState KItem Source LaterPlaces start₁
  batchTableRows batchWhere batchLens pieces quietAt layPile lens_enter lens_get layPile_says Pieces
  TensorRowHolds matOf mkOf valOf)
open VerifiableInference.Desc (rounds_andThen decide_andThen)
open VerifiableInference.Desc.K13 (battRounds batt)
open VerifiableInference.Desc.K13.Law (ρg Holds Wit batt_ok ebind_ok battB_ok quietB_ok frontB_fit)
open VerifiableInference.Desc.K13.Honest (ReadsCode movesAtM3 rowReads movesAtM3_congr code_row maskAt)
open VerifiableInference.Desc.Ground (takeMasksP)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ pend_law)
open AtPublicFiles.KeyThread (D one₀ rowsFirst)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced keysAt sentAt)
open AtPublicFiles.KeyValues (keyBatt constraintRowsAtClaimPoints keyPoints oneOf)
open AtPublicFiles.Key (pileOf readsCode_of_moves pile_same rowOfPoint)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K13 (proverSideOfClaimCombination k13Wit k13Ask k13E k13_plays fits_batt chainSteps_one k13Dr)

/-- **What a yes of the batching's sub-protocol says**, at the rounds that it was handed. -/
theorem seat_rounds_said {β Cl : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime)
    (N : Pieces) (sent : Nat) (s s' : ChainState β) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hl : rs.length = (battRounds (batchWhere one N sent)).length)
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') :
    ∃ (rows : List TensorRow) (out : TensorRow × VerifiableInference.Desc.K13.St)
      (msg : Array OracleNotice),
      layPile keysOf one s = .ok { s with pile := rows } ∧
      memberRowsFit s.d.st one.lin s.idx rows = true ∧
      s.atEnd = false ∧ batt s.debt (batchWhere one N sent).lin.kCol (batchWhere one N sent).rows rows s.idx s.d rs =
        .ok out ∧
      s' = { s with pile := rows, atEnd := true, owed := none, msgW := msg,
                    lin := some { claim := memberClaim out.1 }, d := out.2 } := by
  unfold batchTableRows at h
  dsimp only at h
  rw [decide_andThen] at h
  obtain ⟨t₃, h3, hq⟩ := ebind_ok.1 h
  rw [decide_andThen] at h3
  obtain ⟨t₂, h2, hb⟩ := ebind_ok.1 h3
  rw [decide_andThen] at h2
  obtain ⟨t₁, h1, hf⟩ := ebind_ok.1 h2
  have h1' : layPile keysOf one s = .ok t₁ := h1
  obtain ⟨rows, rfl⟩ := layPile_says keysOf one s t₁ h1'
  obtain ⟨p, he, hpf, hfit⟩ := frontB_fit batchLens _ hf
  obtain ⟨hend, rfl⟩ := (lens_enter _ _).1 he
  obtain ⟨_, rfl⟩ := (lens_get _ _).1 hpf
  obtain ⟨p₂, out, hp₂, hbt, rfl⟩ := battB_ok batchLens _ hb
  obtain ⟨_, rfl⟩ := (lens_get _ _).1 hp₂
  obtain ⟨p₃, msg, hp₃, rfl⟩ := quietB_ok batchLens _ hq
  obtain ⟨_, rfl⟩ := (lens_get _ _).1 hp₃
  refine ⟨rows, out, msg, h1', hfit, hend, ?_, rfl⟩
  simp [rounds_andThen, quietAt, VerifiableInference.Desc.K13.frontB, VerifiableInference.Desc.K13.still,
    VerifiableInference.Desc.K13.claimCombinationBlock] at hbt
  rw [List.take_of_length_le (Nat.le_of_eq hl)] at hbt
  exact hbt

/-- The pile reads its points at the real parts alone. -/
theorem pileOf_congr (m : Wf.Matrix) (lookups : List WfLookup) (pts pts' : Nat → Nat → List E)
    (h : ∀ i p, i < lookups.length → p < (lookups.getD i default).parts.length →
      pts i p = pts' i p) : pileOf m lookups pts = pileOf m lookups pts' := by
  unfold pileOf
  simp only [List.flatMap_def]
  congr 1
  refine List.map_congr_left fun x hx => List.map_congr_left fun p hp => ?_
  have hi := List.mem_zipIdx_iff_getElem?.1 hx
  have hq := List.mem_zipIdx_iff_getElem?.1 hp
  have hlt : x.2 < lookups.length := (List.getElem?_eq_some_iff.1 hi).1
  have hg : lookups.getD x.2 default = x.1 := by
    rw [List.getD_eq_getElem?_getD, hi]
    rfl
  have hplt : p.2 < (lookups.getD x.2 default).parts.length := by
    rw [hg]
    exact (List.getElem?_eq_some_iff.1 hq).1
  rw [h x.2 p.2 hlt hplt]

section Core
variable {W₀ Rc Tr X : Type} {S Cl : Type}

/-- **THE CORE.** The rounds are those that the kind's part plays at the coins c; the text accepts
them; the state's rows are true at the matrix and mask entries (mat, mk); the part's pile reads as
the state's; under the slots taken the mask entries are the coins. Then the row returned is true. -/
theorem handed_true (weights : W₀ → Weights) (pile : ProofFile.Honest.K13.PileOf Xi)
    (P : VerifiableInference.Desc.K13.Where) (b : Block S Cl) (hr : b.rounds = battRounds P)
    (ho : b.oracles = List.replicate (2 + P.lin.kCol) []) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) X)
    (hy : play ((proverSideOfClaimCombination weights pile P).steps b v c) ds [] m = .ok y)
    {owed : Johnson.Desc.First.ForkGround.RowsOwed} {n : Nat} {rows : List TensorRow} {ledger : Nat}
    {d : VerifiableInference.Desc.K13.St} {out : TensorRow × VerifiableInference.Desc.K13.St}
    (hb : batt owed P.lin.kCol n rows ledger d ((roundsOf y.1).map noDigest) = .ok out)
    (mat : Nat → Nat → F) (mk : Slot → E)
    (hmat : (VerifiableInference.Desc.Key.witOf (Wf.matrixOf P.lin) mat mk).mat =
      (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (hrows : ∀ r ∈ rows, TensorRowHolds VerifiableInference.Desc.Key.sameGl (Wf.matrixOf P.lin) mat
      mk r)
    (hreads : ∀ e, (pile m.st.input.x (m.st.heard ++ [e])).map rowReads = rows.map rowReads)
    (hcoins : ∀ t, takeMasksP d ledger (Batt.masksOf P.lin.kCol) = some t → ∀ j,
      j < Batt.masksOf P.lin.kCol →
        rdE.val ((coinsE c.2.1.2.1.1).getD j zeroE) = readE (mk ⟨ledger, t.1.getD j 0⟩)) :
    TensorRowHolds VerifiableInference.Desc.Key.sameGl (Wf.matrixOf P.lin) mat mk out.1 := by
  rw [hr] at hd
  obtain ⟨x₁, eps, gs, hbr, hg⟩ := fits_batt P ds hd
  obtain ⟨r, rs', x₀, t, hdd, o, e1, -, hfits, hx, -, ht, hh, hrun, -, hout⟩ := batt_ok hb
  have hpsi := VerifiableInference.Desc.Key.batt_row_psi hb
  have hlen : t.1.length = Batt.masksOf P.lin.kCol := VerifiableInference.Desc.K13.Honest.takeMasks_length ht
  let W : Wit GE P.lin.matrixRows P.lin.kCol := VerifiableInference.Desc.Key.witOf (Wf.matrixOf P.lin) mat mk
  let fresh : List Slot := t.1.map fun i => ⟨ledger, i⟩
  have hu : ∀ j, j < 2 * P.lin.kCol + 1 →
      ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE) = maskAt W fresh j := by
    intro j hj
    have hj' : j < Batt.masksOf P.lin.kCol := by
      unfold Batt.masksOf
      omega
    refine (hcoins t ht j hj').trans ?_
    have hl : j < t.1.length := by
      rw [hlen]
      exact hj'
    have e : fresh.getD j default = ⟨ledger, t.1.getD j 0⟩ := by
      simp [fresh, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    show _ = W.mask (fresh.getD j default)
    rw [e]
    rfl
  match ds, hbr, hd, hy with
  | d0 :: d1 :: dr, hbr, _, hy =>
    have hb' : bare d0 :: bare d1 :: dr.map bare = k13Dr x₁ :: k13Dr eps :: gs.map k13Dr := hbr
    obtain ⟨h0, hb''⟩ := List.cons.inj hb'
    obtain ⟨h1, hrr⟩ := List.cons.inj hb''
    obtain ⟨l, hp, -, hmv⟩ := k13_plays weights pile P b hr ho v c m d0 d1 dr x₁ eps gs h0 h1 hrr hg
      W hmat fresh hu
    have hyl : y.1 = l := by
      have e := Except.ok.inj (hy.symm.trans hp)
      rw [e]
    rw [hyl] at e1
    have hm : movesAtM3 ρg k13E W rows fresh x₁ eps gs = r :: rs' := by
      rw [← e1, hmv]
      exact movesAtM3_congr ρg k13E W (hreads d0).symm fresh x₁ eps gs
    have hc := readsCode_of_moves k13E (fun a => toE_ofE a) W rows ledger d t ht x₁ eps gs hg r rs'
      x₀ t hdd hm hx ht hh
    have hH : ∀ q ∈ rows, Holds ρg W q := fun q hq =>
      (VerifiableInference.Desc.Key.tensorRowHolds_iff_k13 _ mat mk q
        (VerifiableInference.Desc.Key.fits_psi hfits q hq)).1 (hrows q hq)
    have hrow := code_row ρg W rows fresh hfits hH x₀ hdd o hc hrun
    have e2 : out.1 = Batt.rowOf rows o := by
      rw [hout]
    refine (VerifiableInference.Desc.Key.tensorRowHolds_iff_k13 _ mat mk out.1 hpsi).2 ?_
    rw [e2]
    exact hrow
  | [], hbr, _, _ => cases hbr
  | [d], hbr, _, _ =>
    have hb' : bare d :: [] = k13Dr x₁ :: k13Dr eps :: gs.map k13Dr := hbr
    exact absurd (List.cons.inj hb').2 (by simp)

end Core

/-- At border 16 the index masks' message is number 0. -/
theorem idx_zero {Xs : Source} {s : FirstState} (h : ShapeAt Xs 16 s = true) : s.idx = 0 := by
  have ht : Johnson.RunOne.KeyRows1.ties₁ (one₀ Xs) 16 s = true :=
    ((VerifiableInference.Desc.Key.shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold Johnson.RunOne.KeyRows1.ties₁ Johnson.RunOne.KeyRows1.tiesA at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht.1.1.1.2 with h | h
  · exact absurd h (by decide)
  · exact h

/-- The claim of a row gives the row back. -/
theorem row_of_member (r : TensorRow) :
    VerifiableInference.Desc.Key.rowOfLinClaim (memberClaim r) = r := by
  cases r with
  | mk g psi masks target =>
    simp only [VerifiableInference.Desc.Key.rowOfLinClaim, memberClaim, List.map_map,
      Function.comp_def, List.map_id']

/-- Two ways of reading a column's bits as a number. -/
theorem ofBits_rowNo {k : Nat} (β : Fin k → Bool) : Nat.ofBits β = Sz.rowNo β := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · rw [Nat.testBit_ofBits_lt β i hi]
    exact (testBit_rowNo β ⟨i, hi⟩).symm
  · rw [Nat.testBit_ofBits_ge β i (Nat.le_of_not_lt hi)]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowNo_lt β)
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))).symm

section Thread
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- **The item "pile" behind the batching.** -/
theorem pile_item (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hH : ∀ (k : Coins Bk) s m E, Thr (Th Xs N Pl K f Q w₀ rc x) 16 k s m E →
      ∀ tail, HeardAtKeys Xs N (m.st.heard ++ tail) s)
    (hC : CoinsAtSlots Xs N Pl K f Q w₀ rc x)
    {blk : Block (D Xs N Pl).S₁ (D Xs N Pl).Cl} (hb : (Th Xs N Pl K f Q w₀ rc x).bs[16]? = some blk)
    {k : Coins Bk} {s s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (In1 W₀ Rc) X'} {cols : List OpenedColumn}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) 16 k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s') :
    (Th Xs N Pl K f Q w₀ rc x).Items [.pile] k s' y.2 (E.add y.1) := by
  obtain ⟨blk₀, hb₀, hr, ho, hf, -, hdecide⟩ :=
    batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  obtain rfl : blk = blk₀ := Option.some.inj (hb.symm.trans hb₀)
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hS.1
  obtain ⟨c, hlend, rfl⟩ := chainSteps_one hf hl
  obtain ⟨hfit, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hS.2
  have hval : m.st.input = ⟨w₀, rc, x, ()⟩ := hT.2.2.2.2.2.2.1
  have hin : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hy).1
  have hhe : y.2.st.heard = m.st.heard ++ ds := play_heard _ _ _ _ _ hy
  have hkl : K.batt.lin = (oneOf Xs).lin := by
    rw [hp.batt]
    rfl
  have hlenrs : ((roundsOf y.1).map noDigest).length =
      (battRounds (batchWhere (oneOf Xs) pieces (sentAt Xs.Y.D.1))).length := by
    have e := VerifiableInference.Desc.K13.Law.roundsFit_length _ _ hfit
    rw [hr, hp.batt] at e
    rw [List.length_map]
    exact e
  obtain ⟨rows, out, msg, hlay, -, -, hbt, rfl⟩ := seat_rounds_said keysAt (oneOf Xs) pieces
    (sentAt Xs.Y.D.1) s s' _ gs hlenrs ((hdecide _ _ _).symm.trans hdec)
  intro ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  have hw : (Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input (y.2.st.heard ++ ds') =
      (Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ (ds ++ ds')) := by
    rw [hin, hhe, List.append_assoc]
  obtain ⟨rr, erows, hlenr, hgr⟩ := pend_law keysAt (oneOf Xs) s _ hlay
  have erows' : rows = rr.flatten := congrArg (fun z : FirstState => z.pile) erows
  have hkeys := VerifiableInference.Desc.Key.layPile_whole keysAt (oneOf Xs) s _ hlay
  obtain ⟨rr', hn, hmap, erows''⟩ := hkeys
  have err : rows = rr'.flatten := congrArg (fun z : FirstState => z.pile) erows''
  -- the matrix and the mask entries of the witness
  let v := (Th Xs N Pl K f Q w₀ rc x).wit k m.st.input (m.st.heard ++ (ds ++ ds'))
  let mat := matOf (plan₁ (one₀ Xs)) readH v
  let mk := mkOf (plan₁ (one₀ Xs)) readH v
  have hmatE : ∀ a b, mat a b = OnBytes.Slice.ofF ((f m.st.input.w₀).entry a b) := by
    intro a b
    exact matAt_cells (one₀ Xs).lin (f m.st.input.w₀) a b
  have hrows : ∀ r ∈ rows, TensorRowHolds VerifiableInference.Desc.Key.sameGl
      (Wf.matrixOf K.batt.lin) mat mk r := by
    intro r hr'
    rw [erows'] at hr'
    obtain ⟨R, hR, hrR⟩ := List.mem_flatten.1 hr'
    obtain ⟨l', hl'⟩ := List.mem_iff_getElem?.1 hR
    have hlt : l' < 2 := by
      have := (List.getElem?_eq_some_iff.1 hl').1
      rw [hlenr, hp.lookupsTwo] at this
      exact this
    have hk := hgr l' R hl'
    have hopen : KItem.kclaims l' ∈ (Th Xs N Pl K f Q w₀ rc x).opened 16 := by
      have h2 : l' = 0 ∨ l' = 1 := by omega
      show KItem.kclaims l' ∈ ProofFile.Honest.fwdOpen (start₁ 2) rowsFirst 16
      rcases h2 with rfl | rfl <;> decide
    obtain ⟨L, ks, -, hks, -, hall⟩ := hT.2.2.2.1 (ds ++ ds') _ hopen
    have hks' : ((s.base.keys)[l']?).bind (Johnson.RunOne.KeyReaders.pendingOf (oneOf Xs) l') =
      some ks := hks
    have eR : R = ks := Option.some.inj (hk.symm.trans hks')
    rw [hkl]
    exact hall r (eR ▸ hrR)
  have hreads : ∀ e, (K.pile m.st.input.x (m.st.heard ++ [e])).map rowReads = rows.map rowReads := by
    intro e
    rw [hp.pile, err]
    have e1 := pile_same (Wf.matrixOf (oneOf Xs).lin) (oneOf Xs).ranges.lookups s.base.keys rr' 0 hn
      hmap
    have e2 : constraintRowsAtClaimPoints Xs N m.st.input.x (m.st.heard ++ [e]) =
        pileOf (Wf.matrixOf (oneOf Xs).lin) (oneOf Xs).ranges.lookups
          fun i p => ((s.base.keys.getD i []).getD p default).point :=
      pileOf_congr _ _ _ _ (hH k s m E hT [e])
    rw [e2]
    exact e1.symm
  have hcoins : ∀ t, takeMasksP s.d s.idx (Batt.masksOf K.batt.lin.kCol) = some t → ∀ j,
      j < Batt.masksOf K.batt.lin.kCol →
        rdE.val ((coinsE c.2.1.2.1.1).getD j zeroE) = readE (mk ⟨s.idx, t.1.getD j 0⟩) := by
    intro t ht j hj
    refine (hC blk hb k s m E hT _ hlay c hlend t ht j hj).trans ?_
    have h0 : s.idx = 0 := idx_zero hT.2.2.1.1
    rw [h0]
    have hseat := seat_idx (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
    have hfirst : K.idx.first = 0 := by
      rw [hp.idx]
      rfl
    have e := val_first hseat v OnBytes.Part.mask (t.1.getD j 0)
    rw [hfirst] at e
    refine Eq.symm (e.trans ?_)
    have hw₀ : m.st.input.w₀ = w₀ := by rw [hval]
    have hrc : m.st.input.rc = rc := by rw [hval]
    show (Fl Xs N Pl K f Q x).msg 0 k m.st.input.w₀ m.st.input.rc
      ((m.st.heard ++ (ds ++ ds')).take (roundsTo (D Xs N Pl).first.blocksInOrder 0)) OnBytes.Part.mask (t.1.getD j 0) = _
    rw [hw₀, hrc]
    rfl
  have hmat : (VerifiableInference.Desc.Key.witOf (Wf.matrixOf K.batt.lin) mat mk).mat =
      (k13Wit K.batt.lin.matrixRows K.batt.lin.kCol (k13Ask K.weights K.pile m.st.input)).mat := by
    funext a β
    show readE (OnBytes.ofF (mat a.val (Sz.rowNo β))) =
      Reading.gl.val (eOfF ((K.weights m.st.input.w₀).entry a.val (Nat.ofBits β)))
    rw [hmatE, ofBits_rowNo, hp.weights]
    rfl
  have hbt' : batt s.debt K.batt.lin.kCol (batchWhere (oneOf Xs) pieces (sentAt Xs.Y.D.1)).rows rows
      s.idx s.d ((roundsOf y.1).map noDigest) = .ok out := by
    rw [hkl]
    exact hbt
  have hlast := handed_true K.weights K.pile K.batt blk hr ho _ c m ds hd y hy hbt' mat mk hmat
    hrows hreads hcoins
  rw [hkl] at hlast
  show ∃ z, some (VerifiableInference.Desc.Key.rowOfLinClaim (memberClaim out.1)) = some z ∧
    TensorRowHolds readH.same (plan₁ (one₀ Xs)).m
      (matOf (plan₁ (one₀ Xs)) readH ((Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input
        (y.2.st.heard ++ ds')))
      (mkOf (plan₁ (one₀ Xs)) readH ((Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input
        (y.2.st.heard ++ ds'))) z
  rw [hw, row_of_member]
  exact ⟨out.1, rfl, hlast⟩

end Thread

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.seat_rounds_said
#print axioms AtPublicFiles.FirstH.pileOf_congr
#print axioms AtPublicFiles.FirstH.handed_true
#print axioms AtPublicFiles.FirstH.idx_zero
#print axioms AtPublicFiles.FirstH.row_of_member
#print axioms AtPublicFiles.FirstH.ofBits_rowNo
#print axioms AtPublicFiles.FirstH.pile_item
