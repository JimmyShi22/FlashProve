-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHRangeTies.lean: what the two ties of `acceptedS_ties` (E2E/KeyRangesWholeS.lean) rest on
at the thread `T₁`.

  `rows0_same`: the rows of a sending's message 0, where it holds no coin of its main rows and nothing
    rides on it, read its data and its mask's coins alone.
  `tree_term`: the sending's tree 0 at the cut of the purse is the thread's table.
  `CarryFits`: a public test on the book: what the test's second part carries first is the sender's
    stretch from 0, message 0's count long, inside the sender's count.
  `carried_read`: so the stretch and the cut read the same coins.
  `T15Ok`, `t15_ok`: by the kernel: at the closed term of border 15 the group under test has message 1
    alone.
  `words_core`: a sending's message 0 at the test's words.

The ties themselves stand in E2E/FirstHRangeLots.lean. Limits. Nothing on any property.
-/
import E2E.FirstHSeats
import E2E.KeyRangesWholeS
import E2E.KeyHeldWords
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces valOf pieces)
open Johnson.Prover.Send (Rows shapeAt held)
open Johnson.RunOne.KeyRows1 (plan₁)
open AtPublicFiles.KeyThread (D one₀ laid₁ sentRanges rangesTestJob TbIsSent WitIsJob)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups multiplicitiesSending oneOf)
open AtPublicFiles.Key (held_wordsAt)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob dueR rowsR ce cf stepsOf dueMsg treeTables treeTbl lentCut rowsLaid)
open ProofFile.Honest.K12 (stretchOf stretches plainOne csOfStretch restCoins restPart firstPart TestCoins)
open ProofFile.Honest.K12.Light (carriedOf lend_cut carried_of_lendPart lendRow_snd cut_at)

/-- **The rows of message 0**, where it holds no coin of its main rows and nothing rides on it. -/
theorem rows0_same {P P' : VerifiableInference.Desc.K1.Par} {ride ride' : Nat → Option ProofFile.Honest.K1.Ride}
    {data data' : Nat → Nat → Nat → Option (GF ⊕ GE)} {c : Cs (dueR P ride)}
    {c' : Cs (dueR P' ride')} (hP : P' = P) (hR : ride' = ride)
    (hD : ∀ r j, data' 0 r j = data 0 r j)
    (hw : (stepsOf P.codes (shapeAt P 0) (ride 0)).word = 0)
    (hpad : (stepsOf P.codes (shapeAt P 0) (ride 0)).pad = 0) (hn : ride 0 = none)
    (hE : ∀ i, i < (dueMsg P.codes (shapeAt P 0) (ride 0)).e → ce c' i = ce c i) :
    (∀ b, (rowsR P' ride' data' c' 0).main b = (rowsR P ride data c 0).main b) ∧
      (rowsR P' ride' data' c' 0).mask = (rowsR P ride data c 0).mask := by
  subst hP hR
  have hd : data' 0 = data 0 := funext fun r => funext fun j => hD r j
  constructor
  · intro b
    funext r j
    unfold Johnson.Prover.Send.Rows.main rowsR
    simp only [hw, hpad, hd, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false,
      Option.map_none]
  · funext r j
    unfold rowsR
    simp only [hn]
    by_cases hrj : r < (shapeAt P' 0).maskRows ∧ j < (P'.codes.mask.getD (shapeAt P' 0).maskCode default).ell
    · rw [if_pos hrj, if_pos hrj]
      apply hE
      have hb : j * (shapeAt P' 0).maskRows + r <
          (shapeAt P' 0).maskRows * (P'.codes.mask.getD (shapeAt P' 0).maskCode default).ell := by
        have h1 : (j + 1) * (shapeAt P' 0).maskRows ≤
            (P'.codes.mask.getD (shapeAt P' 0).maskCode default).ell * (shapeAt P' 0).maskRows :=
          Nat.mul_le_mul_right _ hrj.2
        rw [Nat.mul_comm (shapeAt P' 0).maskRows]
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega
      unfold dueMsg
      simp only [hn]
      by_cases h3 : (shapeAt P' 0).mainDeg == 3
      · simp only [h3, if_true, ProofFile.Honest.K1.startR, List.range_zero, List.foldl_nil, Bool.true_eq]
        simp [stepsOf, ProofFile.Honest.K1.Steps.main] at hb ⊢
        omega
      · simp only [h3, Bool.false_eq_true, if_false, ProofFile.Honest.K1.startR, List.range_zero,
          List.foldl_nil]
        simp [stepsOf] at hb ⊢
        omega
    · rw [if_neg hrj, if_neg hrj]

/-- The coin of a cut, by number. -/
theorem ce_stretch {d : Due} (c : Cs d) (i : Nat) : ce c i = (stretchOf c).e i := rfl

/-- The coins of a stretch at a count that holds i. -/
theorem ce_of_stretch (d : Due) (S : ProofFile.Honest.K12.Stretch) (i : Nat) (h : i < d.e) :
    ce (csOfStretch d S) i = S.e i := by
  unfold ce csOfStretch
  rw [dif_pos h]

/-- **A public test on the book.** -/
def CarryFits (Bk : ProverCoinCounts) (a sender : Addr) (d : Due) (total : Due) : Bool :=
  match (carriedOf Bk a)[0]? with
  | some e => e.owner == sender && e.start == ⟨0, 0⟩ && e.count == d && decide (d.e ≤ total.e)
  | none => false

/-- **So the stretch and the cut read the same coins.** -/
theorem carried_read {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a sender : Addr} {d total : Due} {V W X : Type} (p : Part V W X) (c : p.Coins)
    (hl : lendPart Bk rows look a p = .ok c) (hf : CarryFits Bk a sender d total = true)
    {own : Cs total} (hown : (look sender).2.cut ⟨0, 0⟩ total = some own) :
    ∀ i, i < d.e → (stretches p.carries c.2.2 0).e i = ce own i := by
  unfold CarryFits at hf
  split at hf
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨ho, hs⟩, hc⟩, hin⟩ := hf
    obtain ⟨x, hx, hst⟩ := lend_cut look _ _ _ (carried_of_lendPart Bk rows look a p c hl) 0 e he
    intro i hi
    rw [hst, cut_at _ _ _ x hx i (by rw [hc]; exact hi), ho, hs, ce_stretch,
      cut_at _ _ _ own hown i (by omega)]
  · cases hf

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀}
  {rc : Rc} {x : Xi} {Z : PublicFiles}

/-- **The sending's tree 0 at the cut of the purse is the thread's table.** -/
theorem tree_term {J : SendJob (In1 W₀ Rc) X'} (hJ : J = multiplicitiesSending f Xs) (own₀ : X')
    (k : Coins (keyBook K₀)) (w : In1 W₀ Rc) (h : List Fmt.Drawn)
    (ht : (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P.trees.length = 1)
    (c₁ : Cs (dueR (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P
      (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).ride))
    (hc : ((k.look 0) AtPublicFiles.KeyTest.sMsg).2.cut ⟨0, 0⟩
      (dueR (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P
        (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).ride) = some c₁) :
    (treeTables (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P
      (rowsR (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P
        (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).ride
        ((sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).data w) c₁))[0]? =
      some (treeTbl 0 id J own₀ 0 k w h).2 := by
  subst hJ
  have hcut : lentCut k 0 ⟨(multiplicitiesSending (X := X') (Rc := Rc) f Xs).P.place, 0⟩
      (dueR (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P (multiplicitiesSending (X := X') (Rc := Rc) f Xs).ride) =
      some c₁ := hc
  unfold treeTbl
  rw [hcut]
  have hl : 0 < (treeTables (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P
      (rowsR (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P
        (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).ride
        ((sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).data w) c₁)).length := by
    rw [ProofFile.Honest.K1.treeTables_length]
    show 0 < (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P.trees.length
    rw [ht]
    decide
  rw [List.getElem?_eq_getElem hl]
  show _ = some ((treeTables _ _)[0]?.getD _)
  have hl2 : 0 < (treeTables (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P
      (rowsLaid (multiplicitiesSending (X := X') (Rc := Rc) f Xs) own₀ c₁ (id w) h)).length := hl
  rw [List.getElem?_eq_getElem hl2]
  rfl

/-- Closing ledgers leaves the shapes. -/
theorem close_shape : ∀ (l : List Nat) (S : Statement) (o : Nat),
    ((OnBytes.Slice.closeLedgers S l).oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape)
  | [], _, _ => rfl
  | p :: l, S, o => by
    have e := close_shape l { S with oracles := S.oracles.modify p fun x =>
      { x with ledger := x.ledger.map fun l => { l with closed := true } } } o
    refine e.trans ?_
    show ((S.oracles.modify p _)[o]?).map _ = _
    rw [Array.getElem?_modify]
    by_cases h : p = o
    · rw [if_pos h]
      cases S.oracles[o]? <;> rfl
    · rw [if_neg h]

/-- **At the closed term of border 15**: the group under test has message 1 alone. -/
def T15Ok : Bool :=
  ((AtPublicFiles.AtFiles.Full.T15.1.st.groups[0]?).any fun G => G.members == [1]) &&
    ((AtPublicFiles.AtFiles.Full.T15.1.st.oracles[1]?).any fun x =>
      x.shape == ((Wf.messageOf AtPublicFiles.AtFiles.Full.oneF.ranges).getD 0 default).shape)

theorem t15_ok : T15Ok = true := by decide +kernel

/-- **The core.** A sending's message 0 at the test's words. -/
theorem words_core {J : SendJob (In1 W₀ Rc) X'} (hJ : J = multiplicitiesSending f Xs) (own₀ : X') (w : In1 W₀ Rc)
    (hd : List Fmt.Drawn) (own : Cs (dueR J.P J.ride)) (St : ProofFile.Honest.K12.Stretch)
    (Pst : Johnson.Prover.Link.PS) (S : Statement) (L : GroupLayout) (y : OnBytes.Oracle)
    (hfirst : J.first = 1) (hf : L.find 1 = some 0) (hy : S.oracles[1]? = some y)
    (hs : y.shape = shapeAt J.P 0) (hk : 0 < J.P.sent.size)
    (hzero : (stepsOf J.P.codes (shapeAt J.P 0) (J.ride 0)).word = 0 ∧
      (stepsOf J.P.codes (shapeAt J.P 0) (J.ride 0)).pad = 0)
    (hn : J.ride 0 = none) (hcap : (dueMsg J.P.codes (shapeAt J.P 0) (J.ride 0)).e ≤ (dueR J.P J.ride).e)
    (hcoins : ∀ i, i < (dueMsg J.P.codes (shapeAt J.P 0) (J.ride 0)).e → St.e i = ce own i)
    (part : Part) (i : Nat) :
    held (fun _ _ _ => 0) J.first J.P (rowsLaid J own₀ own w hd) J.first part i =
      ProofFile.Honest.K12.wordsAt S L (plainOne (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0) w St Pst) 1 part i := by
  subst hJ
  have hr := rows0_same (P := (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P)
    (P' := (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).P) (ride := AtPublicFiles.KeyBook.rideMsg) (ride' := AtPublicFiles.KeyBook.rideMsg)
    (data := (multiplicitiesSending (X := X') (Rc := Rc) f Xs).data w ⟨hd, own₀, Seen.bare []⟩)
    (data' := (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0).data w) (c := own)
    (c' := csOfStretch _ St) rfl rfl (fun _ _ => rfl) hzero.1 hzero.2 hn fun j hj =>
      (ce_of_stretch _ _ _ (Nat.lt_of_lt_of_le hj hcap)).trans (hcoins j hj)
  have e := AtPublicFiles.Key.held_wordsAt S L
    (plainOne (sentRanges (Rc := Rc) Xs (matrixEntryOf f) (multiplicitiesGroups Xs) 0) w St Pst) (fun _ _ _ => 0) 1
    (multiplicitiesSending (X := X') (Rc := Rc) f Xs).P (rowsLaid (multiplicitiesSending (X := X') (Rc := Rc) f Xs) own₀ own w hd)
    0 0 hk hf hy hs (fun r j => congrFun (congrFun (hr.1 _) r) j)
    (fun r j => congrFun (congrFun hr.2 r) j) part i
  exact e

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.close_shape
#print axioms AtPublicFiles.FirstH.t15_ok
#print axioms AtPublicFiles.FirstH.words_core
#print axioms AtPublicFiles.FirstH.rows0_same
#print axioms AtPublicFiles.FirstH.ce_of_stretch
#print axioms AtPublicFiles.FirstH.carried_read
#print axioms AtPublicFiles.FirstH.tree_term
