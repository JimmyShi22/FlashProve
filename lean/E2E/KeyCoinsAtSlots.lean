-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyCoinsAtSlots.lean: CoinsAtSlots (E2E/FirstHPile.lean), in scope, at the book of
the written sizes: the mask entries that the verifier's ledger hands the batching are the coins that
the book lends the batching's sum.

  lend_second, lendPart_spends, lend_one, cuts_same   what a lending hands out, by its text
  battEntryOk, batt_entry_full, idxDueOk, idx_due_full   the book at the written sizes, by the kernel
  coinsAtSlots                                    the lot

The road: at the border 16 the ledger stands at 48 takes and one mask row (E2E/KeyLedgerSixteen.lean),
so entry j of the takes is 48 + j. The book lends the sum the index-mask sending's coins from number
48 on, and message 0's mask row at entry 48 + j holds that coin (held_slot). Nothing on any property.
-/
import E2E.KeyLedgerSixteen
import E2E.FirstHBatt
import Johnson.RunOne.KeyStep16
import Johnson.Desc.ProofFile.Honest.K13.CoinsThere
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open VerifiableInference.Desc.Ground (takeMasksP)
open AtPublicFiles.KeyThread (D)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull battPlace idxPlace)
open AtPublicFiles.KeyValues (indexMaskSending oneOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob rowsLaid lentCut dueR dueMsg stepsOf rowsR)
open ProofFile.Honest.K13 (proverSideOfClaimCombination)

/-! ## 1 What a lending hands out -/

section Lending
variable {V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}

/-- Of a row of two parts, the second's coins. -/
theorem lend_second {a : VerifiableInference.Desc.Place} {p₀ p₁ : Part V W X}
    {c : RowCoins [p₀, p₁]} (h : lendRow B rows look a [p₀, p₁] 0 = .ok c) :
    lendPart B rows look ⟨a, 1⟩ p₁ = .ok c.2.1 := by
  unfold lendRow at h
  cases h0 : lendPart B rows look ⟨a, 0⟩ p₀ with
  | error e =>
    rw [h0] at h
    cases h
  | ok c₀ =>
    rw [h0] at h
    unfold lendRow at h
    cases h1 : lendPart B rows look ⟨a, 0 + 1⟩ p₁ with
    | error e =>
      rw [h1] at h
      cases h
    | ok c₁ =>
      rw [h1] at h
      have e : ((c₀, (c₁, ())) : RowCoins [p₀, p₁]) = c := Except.ok.inj h
      subst e
      rfl

/-- What a part is lent, by its text. -/
theorem lendPart_spends {a : Addr} {p : Part V W X} {y : p.Coins}
    (h : lendPart B rows look a p = .ok y) :
    lend look p.spends ((B.ahead.filter fun e => e.spender == a).filter (·.once)) = .ok y.2.1 := by
  unfold lendPart at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i own _
      dsimp only at h
      cases h1 : lend look p.spends ((B.ahead.filter fun e => e.spender == a).filter (·.once)) with
      | error e =>
        rw [h1] at h
        cases h
      | ok sp =>
        rw [h1] at h
        cases h2 : lend look p.carries ((B.ahead.filter fun e => e.spender == a).filter (!·.once)) with
        | error e =>
          rw [h2] at h
          cases h
        | ok ca =>
          rw [h2] at h
          have e : ((own, sp, ca) : p.Coins) = y := Except.ok.inj h
          subst e
          rfl

/-- One named stretch, lent from one entry. -/
theorem lend_one {d : String × Due} {e : Ahead} {y : CsAll [d]}
    (h : lend look [d] [e] = .ok y) : (look e.owner).2.cut e.start d.2 = some y.1 := by
  unfold lend at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases hc : (look e.owner).2.cut e.start d.2 with
      | none =>
        simp only [hc] at h
        cases h
      | some z =>
        simp only [hc] at h
        unfold lend at h
        have := Except.ok.inj (show Except.ok (z, ()) = .ok y from h)
        subst this
        rfl

/-- Two cuts of one purse, at one coin. -/
theorem cuts_same {d a b n m : Due} (c : Cs d) (z : Cs n) (y : Cs m) (h₁ : c.cut a n = some z)
    (h₂ : c.cut b m = some y) (i : Fin n.e) (i' : Fin m.e) (hv : a.e + i.1 = b.e + i'.1) :
    z.e i = y.e i' := by
  unfold Cs.cut at h₁ h₂
  split at h₁
  · split at h₂
    · obtain rfl := Option.some.inj h₁
      obtain rfl := Option.some.inj h₂
      exact congrArg c.e (Fin.ext hv)
    · cases h₂
  · cases h₁

end Lending

/-! ## 2 The book and the sending, at the written sizes -/

/-- **The book's one entry for the batching's sum**, at the written sizes: it takes the index-mask
sending's coins from number 48 on. -/
def battEntryOk (publicData : KeyPub) : Bool :=
  match ((keyBook publicData).ahead.filter fun e => e.spender == ⟨battPlace, 1⟩).filter (·.once) with
  | [e] => e.owner == ⟨idxPlace, 0⟩ && e.start == ⟨0, 48⟩
  | _ => false

theorem batt_entry_full : atFull battEntryOk = true := by decide +kernel

/-- **The sending's count**: what the book has for it covers the message, whose mask row has ell 256
entries from coin 0 on. -/
def idxDueOk (publicData : KeyPub) : Bool :=
  let shape := Lk6.AtPlan.keyFull.once.input.shape
  let n := stepsOf Lk6.AtPlan.keyFull.codes shape none
  let d := dueMsg Lk6.AtPlan.keyFull.codes shape none
  decide (d.f ≤ publicData.sIdx.due.f) && decide (d.e ≤ publicData.sIdx.due.e) && (n.main == 0) &&
    shape.maskRows == 1 &&
    (Lk6.AtPlan.keyFull.codes.mask.getD shape.maskCode default).ell == 256 && decide (256 ≤ d.e)

theorem idx_due_full : atFull idxDueOk = true := by decide +kernel

/-! ## 3 The lot -/

section Lot
variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀}
  {rc : Rc} {x : Xi} {Z : PublicFiles}

theorem written_kCol : Lk6.AtPlan.keyFull.once.shape.kCol = 18 := by decide +kernel

/-- A coin, read back out of the list that a part speaks of. -/
theorem coinsE_read {d : Due} (c : Cs d) (j : Nat) (hj : j < d.e) :
    rdE.val ((coinsE c).getD j zeroE) = c.e ⟨j, hj⟩ := by
  unfold coinsE
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hj, dite_true, Option.getD_some]
  exact toE_ofE _

/-- **CoinsAtSlots, in scope, at the book of the written sizes.** -/
theorem coinsAtSlots (hK : fullPub = some K₀) (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hp : FirstPublic (Pl := Pl) Xs N K f) :
    CoinsAtSlots Xs N Pl K f Q w₀ rc x := by
  intro blk hb k s m E hT laid _ c hlend t ht j hj
  -- the ledger
  have hshape := AtPublicFiles.AtFiles.Full.shape16_of_thr hs scope (Th Xs N Pl K f Q w₀ rc x) rfl
    (fun k' w h s₀ hv hbeg => ⟨_, hbeg⟩) hT
  have h0 : s.idx = 0 := LPFD.idx0_of_shape _ s hT.2.2.1.1
  rw [h0] at ht
  have hnum := AtPublicFiles.AtFiles.Full.takes_at16 hshape ht hj
  rw [hnum]
  -- the book's entry
  have hb₁ := batt_entry_full
  rw [atFull, hK] at hb₁
  obtain ⟨e, he, ho, hst⟩ : ∃ e : Ahead,
      ((keyBook K₀).ahead.filter fun e => e.spender == ⟨battPlace, 1⟩).filter (·.once) = [e] ∧
      e.owner = ⟨idxPlace, 0⟩ ∧ e.start = ⟨0, 48⟩ := by
    simp only [Option.map_some, Option.getD_some, battEntryOk] at hb₁
    split at hb₁
    · rename_i e hs'
      simp only [Bool.and_eq_true, beq_iff_eq] at hb₁
      exact ⟨e, hs', hb₁.1, hb₁.2⟩
    · cases hb₁
  -- the lending
  obtain ⟨blk₀, hb₀, -, -, hf₀, -, -⟩ := batt_member (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  obtain rfl : blk = blk₀ := Option.some.inj (hb.symm.trans hb₀)
  have hplace : blk.place = battPlace := by
    have h1 := List.find?_some hf₀
    have h2 := LawfulBEq.eq_of_beq h1
    rw [← h2, hp.batt]
    rfl
  rw [hplace] at hlend
  have hs1 := lendPart_spends (lend_second hlend)
  rw [he] at hs1
  have hcut := lend_one hs1
  rw [ho, hst] at hcut
  -- the sending
  have hd := idx_due_full
  rw [atFull, hK] at hd
  simp only [Option.map_some, Option.getD_some, idxDueOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨⟨df, de⟩, hmain⟩, hrows⟩, hell⟩, hbig⟩ := hd
  obtain ⟨-, -, e2, e3, e4⟩ := AtPublicFiles.AtFiles.five_sourced hs scope
  have hsent : (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.sent.size = 1 := rfl
  have hshape0 : Johnson.Prover.Send.shapeAt (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P 0 =
      Lk6.AtPlan.keyFull.once.input.shape := by
    show (oneOf Xs).indexMasks.shape = _
    show Xs.Y.k.oneTime.indexMasks.shape = _
    rw [e3]
  have hcodes : (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.codes = Lk6.AtPlan.keyFull.codes := e4
  have hdue : dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P
      (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride =
      dueMsg Lk6.AtPlan.keyFull.codes Lk6.AtPlan.keyFull.once.input.shape none := by
    show Due.plus ⟨0, 0⟩ (dueMsg _ (Johnson.Prover.Send.shapeAt _ 0) none) = _
    rw [hshape0, hcodes]
    simp [Due.plus]
  have hcover : ProofFile.Honest.K1.bookCovers (keyBook K₀) 0 ⟨(indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.place, 0⟩
      (dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P
        (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride) = true := by
    rw [hdue]
    exact decide_eq_true ⟨df, de⟩
  have hsome := ProofFile.Honest.K1.lentCut_isSome k 0 (Nat.zero_le 1)
    ⟨(indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.place, 0⟩
    (dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P
      (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride)
  rw [hcover] at hsome
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hsome
  have hj' : 48 + j < (Johnson.Prover.Send.shapeAt (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P 0).maskRows *
      ((indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.codes.mask.getD
        (Johnson.Prover.Send.shapeAt (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P 0).maskCode default).ell := by
    rw [hshape0, hcodes, hrows, hell]
    have hk : K.batt.lin.kCol = 18 := by
      rw [hp.batt]
      show Xs.Y.k.oneTime.lin.kCol = 18
      rw [e2]
      exact written_kCol
    rw [hk] at hj
    have : Batt.masksOf 18 = 37 := rfl
    omega
  have hheld := ProofFile.Honest.K1.held_slot_in (fun _ _ _ => 0) 0
    (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride
    ((indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).data ⟨w₀, rc, x, ()⟩
      { heard := [], own := K.own₀, seen := .bare [] }) c' 0 (48 + j) (by rw [hsent]; decide) rfl hj'
  have hmask : ProofFile.Honest.K1.maskStart (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P
      (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride 0 = 0 := by
    unfold ProofFile.Honest.K1.maskStart
    rw [hshape0, hcodes]
    show 0 + (if _ then (stepsOf _ _ none).main else 0) = 0
    split
    · exact (Nat.zero_add _).trans hmain
    · rfl
  -- the two sides are one coin
  have hright : (Fl Xs N Pl K f Q x).msg 0 k w₀ rc [] .mask (48 + j) =
      c'.e ⟨ProofFile.Honest.K1.maskStart (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P
        (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride 0 + (48 + j),
        ProofFile.Honest.K1.mask_in _ _ 0 _ (by rw [hsent]; decide) rfl hj'⟩ := by
    show msgRun K.idx K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) [] .mask (48 + j) = _
    rw [hp.idx]
    unfold msgRun
    rw [hc']
    have ei : (48 + j) % 1 + (48 + j) / 1 * 2 ^ VerifiableInference.Desc.K1.clog 1 = 48 + j := by
      rw [Nat.mod_one, Nat.div_one]
      show 0 + (48 + j) * 2 ^ 0 = _
      omega
    rw [hshape0, hrows, ei] at hheld
    exact hheld
  rw [hright]
  have hjc : j < ProofFile.Honest.ownRun (ProofFile.Honest.K13.k13Shape K.batt.lin.kCol) := by
    rw [ProofFile.Honest.K13.k13_ownRun]
    have e : Batt.masksOf K.batt.lin.kCol = 1 + 2 * K.batt.lin.kCol := rfl
    omega
  rw [coinsE_read c.2.1.2.1.1 j hjc]
  have hc'' : (k.look 0 ⟨idxPlace, 0⟩).2.cut ⟨0, 0⟩ (dueR (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P
      (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).ride) = some c' := hc'
  exact cuts_same _ _ _ hcut hc'' ⟨j, hjc⟩ _ (by simp [hmask])

end Lot

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.coinsAtSlots
