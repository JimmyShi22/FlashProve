-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LOpensRows.lean: the column of the one tree that the job of
the first chain's closing proximity test opens (`treesL`, K12/AtProof/JobL.lean) is the column of
the finish's own sending, where the coins of the two sides are tied. No thread, no book, no head:
general in the sender's place.

  `flatMap_congr_mem`, `col_congr`   a written column hangs on the messages' symbols alone
  `CoinsTied`               THE TIE: what the test's second part carries is what the finish carried
                            and what it laid: three clauses
  `SendingFits`             public facts on the sender's place and the test's first stage
  `carryRows_is_sent`       under the tie the job's text `carryRows` returns the finish's message 0
  `freshSymbols_are_sent`   under the tie the job's fresh table and tails give the symbols of the
                            finish's message 1
  `closingColumn_is_sent`   THE END: the two columns are one, at every position

Limits.
- `CoinsTied` and `SendingFits` are premises. Neither is shown of any book, run or place here.
- That the finish's rows are laid (hLaid) is a premise.
- An equation at one run's coins: what is written where. Nothing on how a coin is sampled.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: the three laws under `CoinsTied` bear this label; the rule is at
its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: `CoinsTied` and hLaid
tie the letters cK, mem and V to a run's coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingReturns
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.SameRows
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin
import Johnson.Desc.ProofFile.Honest.K12.PackingAt
import Johnson.Desc.ProofFile.Honest.K12.HideCongr
import Johnson.Desc.ProofFile.Honest.K12.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K2.Honest (mainRows zeroG)
open Johnson.Prover.Send (col mainSyms maskSyms shapeAt)
open ProofFile.Honest.K2.Reads (bind_ok' map_ok)
open Johnson.Prover.Link (packedN symG_congr)
open OnBytes.Slice (GE codeOf)
open H2K.Pub (sgOf)

variable {W₀ Rc Xi Tr : Type}

local notation "Rows" => Johnson.Prover.Send.Rows

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- **A written column hangs on the messages' symbols alone.** -/
theorem col_congr (P : VerifiableInference.Desc.K1.Par) (V V' : ℕ → Rows) (t x : ℕ)
    (h : ∀ k, k < P.sent.size →
      mainSyms P V k x = mainSyms P V' k x ∧ maskSyms P V k x = maskSyms P V' k x) :
    col P V t x = col P V' t x := by
  unfold col
  dsimp only
  rw [flatMap_congr_mem _ (fun k => mainSyms P V k x) (fun k => mainSyms P V' k x) fun k hk =>
      (h k (List.mem_range.1 (List.mem_filter.1 hk).1)).1,
    flatMap_congr_mem _ (fun k => maskSyms P V k x) (fun k => maskSyms P V' k x) fun k hk =>
      (h k (List.mem_range.1 (List.mem_filter.1 hk).1)).2]

/-- **The tie of the coins.** cK: what the finish's part is handed. mem: the stretches that the
test's second part carries, by number: first those that the finish carries, then the finish's
message 0's own, then the fresh table's. -/
structure CoinsTied (p : K2.SwitchPlace)
    (cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries) (mem : ℕ → Stretch) : Prop where
  /-- what the finish carries -/
  front : ∀ n x, p.carries[n]? = some x →
    K2.Stretch.carried p.carries cK.2.2 n = .ok (asK2 x.2 (mem n))
  /-- the carrying message's own coins: the finish's own from number 0 on -/
  carrying : ∀ c' : Cs (K2.messageDue p.sizes.codes (shapeL p) none),
    cK.1.cut ⟨0, 0⟩ (K2.messageDue p.sizes.codes (shapeL p) none) = some c' →
      (⟨_, c'⟩ : K2.Stretch) = asK2 (K2.messageDue p.sizes.codes (shapeL p) none)
        (mem p.front.length)
  /-- the fresh table's coins: the finish's own from message 1's start on -/
  fresh : ∀ i, i < (K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars)).e →
    (mem (p.front.length + 1)).e i =
      K1.ce cK.1 ((K2.dueBefore p.sizes.codes (sentL p)
        (K2.switchFresh p.sizes p.others p.foldVars) 1).e + i)

/-- **Under the tie the job's text returns the finish's message 0.** -/
theorem carryRows_is_sent (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    (cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries) {V : ℕ → Rows}
    (hLaid : K2.switchRowsLaid D readers closing p cK w hd = .ok V) (hTwo : (sentL p).size = 2)
    (mem : ℕ → Stretch) (T : CoinsTied p cK mem) :
    carryRows D readers closing p w hd mem = .ok (V 0) := by
  rw [carryRows_eq D readers closing p w hd mem cK.2.2 T.front]
  unfold K2.switchRowsLaid at hLaid
  split at hLaid
  · cases hLaid
  split at hLaid
  · cases hLaid
  obtain ⟨M, hM, hRows⟩ := bind_ok' hLaid
  unfold K2.switchRowsAt at hM
  obtain ⟨Wl, hW, rfl⟩ := map_ok hM
  have hW' : closing p (D w.x) (readers w) hd (K2.Stretch.carried p.carries cK.2.2) = .ok Wl := by
    have e : hd.take (hd.length - 0) = hd := by simp
    have hW2 : closing p (D w.x) (readers w) (hd.take (hd.length - 0))
        (K2.Stretch.carried p.carries cK.2.2) = .ok Wl := hW
    rwa [e] at hW2
  rw [hW']
  have h0 : 0 < (K2.switchSent p.sizes p.others).size := by
    have e : (K2.switchSent p.sizes p.others).size = 2 := hTwo
    omega
  obtain ⟨c', hcut, hm⟩ := K2.rowsAll_at hRows h0
  have hfold : K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 0 = none := by
    have e : (K2.switchSent p.sizes p.others).size = 2 := hTwo
    simp [K2.foldAt, K2.switchFresh, e]
  revert c'
  rw [hfold, K2.dueBefore_zero]
  intro c' hcut hm
  have e := T.carrying c' hcut
  show K2.messageRows K2.freshTable p.sizes.codes (shapeL p) none
    (mainRows p.sizes Wl (fun _ _ _ => zeroG) 0)
    (asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (mem p.front.length)) = .ok (V 0)
  rw [← e]
  exact hm

/-- **Public facts on the sender's place and the test's first stage s.** -/
structure SendingFits (p : K2.SwitchPlace) (s : Fmt.M1.Stage) : Prop where
  two : (sentL p).size = 2
  noWord : K2.NoWord (sentL p)
  freshMain : (freshShapeL p).mainRows = 0
  freshRows : (freshShapeL p).maskRows = 2 ^ s.h
  logRows : OnBytes.ceilLog2 (freshShapeL p).maskRows = s.h
  fold : p.foldVars = s.k
  low : s.h ≤ s.k
  room : s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l
  code : codeOf (p.sizes.codes.mask.getD (freshShapeL p).maskCode default) = s.Z
  count : K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars) = ⟨0, dueFresh s⟩

/-- The rows that the job's tree holds: `treesL`'s own text, under a name. R₀: message 0. -/
def treeRows (p : K2.SwitchPlace) (R₀ : Rows) (P : Johnson.Prover.Link.PS) : ℕ → Rows := fun k =>
  if k == 0 then R₀
  else if k == (sentL p).size - 1 then { K2.zeroMessage with mask := P.fM, maskTl := P.fT }
  else K2.zeroMessage

/-- **Under the tie the job's fresh table and its tails give the symbols of the finish's message
1.** hide: the fresh table's stretch, as the test's second part reads it. -/
theorem freshSymbols_are_sent (p : K2.SwitchPlace) (s : Fmt.M1.Stage) (F : SendingFits p s)
    (cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries)
    {M : ℕ → ℕ → ℕ → Cb.Gl.E} {V : ℕ → Rows}
    (hRows : K2.rowsAll K2.freshTable p.sizes.codes (sentL p)
      (K2.switchFresh p.sizes p.others p.foldVars) M cK.1 = .ok V)
    (mem : ℕ → Stretch) (T : CoinsTied p cK mem) (R₀ : Rows) (P : Johnson.Prover.Link.PS)
    (hM : P.fM = packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) (mem (p.front.length + 1)).e))
    (hT : P.fT = tailsIn s (mem (p.front.length + 1)).e) (x : ℕ) :
    maskSyms (K2.sendingPar p.sizes.codes (sentL p)) V 1 x =
      maskSyms (K2.sendingPar p.sizes.codes (sentL p)) (treeRows p R₀ P) 1 x := by
  have hfit := K2.rowsAll_fits hRows
  have h1 : 1 < (sentL p).size := by rw [F.two]; omega
  have hsh : shapeAt (K2.sendingPar p.sizes.codes (sentL p)) 1 = freshShapeL p := by
    rw [K2.sendingPar_shape]
    unfold freshShapeL
    rw [F.two]
  have hfold : K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 1 = some p.foldVars := by
    have e : (K2.switchSent p.sizes p.others).size = 2 := F.two
    simp [K2.foldAt, K2.switchFresh, e]
  have hK : s.h + (s.k - s.h) = s.k := by have := F.low; omega
  have hride : K2.rideOf (sentL p) (K2.switchFresh p.sizes p.others p.foldVars) 1 =
      some ⟨s.h + (s.k - s.h), s.h⟩ := by
    unfold K2.rideOf
    rw [hfold, Option.map_some]
    have e : ((sentL p).getD 1 default).shape = freshShapeL p := by
      unfold freshShapeL
      rw [F.two]
    rw [e, F.logRows, F.fold, hK]
  -- message 1 by the shared sending's text, at the finish's own coins
  have hV : V 1 = K2.sharedRows p.sizes.codes (freshShapeL p) (some ⟨s.h + (s.k - s.h), s.h⟩)
      (K2.dueBefore p.sizes.codes (sentL p) (K2.switchFresh p.sizes p.others p.foldVars) 1)
      (K2.dataShared (sentL p) M 1) cK.1 := by
    rw [K2.rowsAll_shared_paid F.noWord (fun _ _ _ _ _ => rfl) hRows h1, K2.rowsR_shared,
      K2.sharedRows_cast, hsh, hride, K2.dueBefore_shared hfit F.noWord 1 (Nat.le_of_lt h1)]
    rfl
  have hl : (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).ell = s.Z.l := by
    rw [← F.code]
    rfl
  have hr : (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).r = s.Z.r := by
    rw [← F.code]
    rfl
  have hmain : (K1.stepsOf p.sizes.codes (freshShapeL p)
      (some ⟨s.h + (s.k - s.h), s.h⟩)).main = 0 := by
    have hz : ((freshShapeL p).maskRows == 0) = false := by
      rw [F.freshRows]
      exact beq_false_of_ne (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
    simp [K1.Steps.main, K1.stepsOf, F.freshMain, hz]
  have hdue : (K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars)).e = dueFresh s := by
    rw [F.count]
  have hL : (treeRows p R₀ P) 1 = { K2.zeroMessage with mask := P.fM, maskTl := P.fT } := by
    unfold treeRows
    rw [F.two]
    rfl
  unfold maskSyms
  dsimp only
  rw [hsh]
  refine flatMap_congr_mem _ _ _ fun r hrr => ?_
  have hr' : r < 2 ^ s.h := by
    rw [← F.freshRows]
    exact List.mem_range.1 hrr
  congr 2
  have ec : (K2.sendingPar p.sizes.codes (sentL p)).codes = p.sizes.codes := rfl
  rw [ec, F.code]
  refine symG_congr _ _ _ _ _ _ (fun j hj => ?_) fun q hq => ?_
  · rw [hV, hL, hM]
    show (if r < (freshShapeL p).maskRows ∧
        j < (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).ell then
      (⟨s.h + (s.k - s.h), s.h⟩ : K1.Ride).lay _ r j else 0) = _
    rw [if_pos ⟨by rw [F.freshRows]; exact hr', by rw [hl]; exact hj⟩]
    refine (packing_at (sgOf s) F.room _ r j).symm.trans ?_
    show packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) _) r j =
      packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) (mem (p.front.length + 1)).e) r j
    rw [ProofFile.Honest.K12.Light.hideAt_congr _ _ (mem (p.front.length + 1)).e fun i hi => ?_]
    have hi' : i < 2 * s.k + 1 := by
      have e : (sgOf s).h + (sgOf s).g = s.h + (s.k - s.h) := rfl
      rw [e, hK] at hi
      exact hi
    have hc : i < (⟨s.h + (s.k - s.h), s.h⟩ : K1.Ride).count := by
      show i < 2 * (s.h + (s.k - s.h)) + 1
      rw [hK]
      exact hi'
    rw [if_pos hc, T.fresh i (by rw [hdue]; unfold dueFresh; omega), hmain]
    congr 1
    split <;> omega
  · rw [hV, hL, hT]
    show (if r < (freshShapeL p).maskRows ∧
        q < (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).r then K1.ce cK.1 _
      else 0) = _
    rw [if_pos ⟨by rw [F.freshRows]; exact hr', by rw [hr]; exact hq⟩]
    show K1.ce cK.1 _ = (mem (p.front.length + 1)).e (2 * s.k + 1 + r * s.Z.r + q)
    have hb : 2 * s.k + 1 + r * s.Z.r + q < dueFresh s := by
      unfold dueFresh
      have : r * s.Z.r + q < 2 ^ s.h * s.Z.r := by
        calc r * s.Z.r + q < r * s.Z.r + s.Z.r := Nat.add_lt_add_left hq _
          _ = (r + 1) * s.Z.r := (Nat.succ_mul r s.Z.r).symm
          _ ≤ 2 ^ s.h * s.Z.r := Nat.mul_le_mul_right _ hr'
      omega
    rw [T.fresh _ (by rw [hdue]; exact hb), hmain, hr]
    congr 1
    show _ + (2 * (s.h + (s.k - s.h)) + 1) + r * s.Z.r + q = _
    rw [hK]
    split <;> omega

/-- Where the finish's rows are laid, they are `rowsAll`'s at some main rows. -/
theorem rowsAll_of_laid {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {w : Local W₀ Rc Xi Tr} {hd : List Fmt.Drawn}
    {cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries} {V : ℕ → Rows}
    (hLaid : K2.switchRowsLaid D readers closing p cK w hd = .ok V) :
    ∃ M, K2.rowsAll K2.freshTable p.sizes.codes (sentL p)
      (K2.switchFresh p.sizes p.others p.foldVars) M cK.1 = .ok V := by
  unfold K2.switchRowsLaid at hLaid
  split at hLaid
  · cases hLaid
  split at hLaid
  · cases hLaid
  obtain ⟨M, -, hRows⟩ := bind_ok' hLaid
  exact ⟨M, hRows⟩

variable {X : Type}

/-- **THE END: the column of the finish's own sending is the column of the job's one tree**, at
every position. fr: the front at the test; hd: the challenges in front of the finish. -/
theorem closingColumn_is_sent (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (fr : Front X)
    (cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries) {V : ℕ → Rows}
    (hLaid : K2.switchRowsLaid D readers closing p cK w (heardL fr) = .ok V) (s : Fmt.M1.Stage)
    (F : SendingFits p s) (mem : ℕ → Stretch) (T : CoinsTied p cK mem)
    (P : Johnson.Prover.Link.PS)
    (hM : P.fM = packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) (mem (p.front.length + 1)).e))
    (hT : P.fT = tailsIn s (mem (p.front.length + 1)).e) (y : ℕ) :
    col (K2.sendingPar p.sizes.codes (sentL p)) V 0 y =
      ((treesL D readers closing p w fr mem P).getD 0 (0, fun _ => [])).2 y := by
  show _ = col (K2.sendingPar p.sizes.codes (sentL p))
    (treeRows p ((carryRows D readers closing p w (heardL fr) mem).toOption.getD K2.zeroMessage) P)
    0 y
  rw [carryRows_is_sent D readers closing p w (heardL fr) cK hLaid F.two mem T]
  obtain ⟨M, hRows⟩ := rowsAll_of_laid hLaid
  refine col_congr _ _ _ _ _ fun k hk => ?_
  have hk2 : k < 2 := by
    have e : (K2.sendingPar p.sizes.codes (sentL p)).sent.size = 2 := by
      rw [K2.sendingPar_sent]
      exact F.two
    omega
  have hcase : k = 0 ∨ k = 1 := by omega
  rcases hcase with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · refine ⟨?_, freshSymbols_are_sent p s F cK hRows mem T _ P hM hT y⟩
    have hsh : shapeAt (K2.sendingPar p.sizes.codes (sentL p)) 1 = freshShapeL p := by
      rw [K2.sendingPar_shape]
      unfold freshShapeL
      rw [F.two]
    unfold mainSyms
    dsimp only
    rw [hsh, F.freshMain]
    rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.rowsAll_of_laid
#print axioms ProofFile.Honest.K12.AtProof.closingColumn_is_sent
#print axioms ProofFile.Honest.K12.AtProof.SendingFits
#print axioms ProofFile.Honest.K12.AtProof.treeRows
#print axioms ProofFile.Honest.K12.AtProof.freshSymbols_are_sent
#print axioms ProofFile.Honest.K12.AtProof.flatMap_congr_mem
#print axioms ProofFile.Honest.K12.AtProof.col_congr
#print axioms ProofFile.Honest.K12.AtProof.CoinsTied
#print axioms ProofFile.Honest.K12.AtProof.carryRows_is_sent
