-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WordsAtOwnTab.lean: the words of the last thread, at a
message of kind K1 and at a sampled message of the shared chain: wordsAtOwn at a seat where the
witness's table is known; and the last witness at the first chain's seats.

  wordsOn_rowsMsg       words out of a table that is a message's rows are these rows' word
  wordsAtOwn_at_seat    wordsAtOwn at a message whose table at its seat is the rows
  lastWitness_tab_first the last witness at a seat of the first chain's trees is the first chain's
                        witness: it lays the shared chain's three messages elsewhere
  wordsAtOwn_at_table   wordsAtOwn at a message whose table at its seat is a given table
  lastWitness_tab_sampled   the last witness at a sampled message's seat is that message's table
  words_first_at_W      the last thread's words at a message of a K1 sender of the first chain: the
                        sender's rows at its own coins and the challenges in front of it

By what. K1.rowsMsg, Rows.word; wordsAtOwn (LotWJoint.lean); lastWitness (Thread/TheFirstThread.lean).
hf: FarFrom (K14/Law/SharedConstFold.lean), at a place of the first chain's book; the injectivity of
the three numbers: P5T.harr_of_found.

Limits.
- hseat, hx, htab are premises: K1.tab_rows has htab at a Script of the senders' record.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsOfK1
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointAtLastThread
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Statement OracleShape Oracle ceilLog2)
open OnBytes.Slice (GE)
open OnBytes.Means (Words wordsOn realRows)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT tabAt)
open VerifiableInference.Desc.Shared (Msg2)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest (OnlineProverWithDescription Coins Local)
open ProofFile.Honest.K1 (rowsMsg)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtOwn)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders lastWitness)

/-- **Words out of a table that is a message's rows are these rows' word.** -/
theorem wordsOn_rowsMsg (S : Statement) (o : Nat) (s : OracleShape)
    (hx : (S.oracles[o]?).map (·.shape) = some s) (R : Johnson.Prover.Send.Rows) (T : Nat → Bool → Nat → Nat → GE)
    (hT : T o = rowsMsg s R) (pt : OnBytes.Part) (i : Nat) :
    wordsOn S T o pt i = R.word s pt i := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  have hg : (S.oracles.getD o default) = y := by
    rw [Array.getD_eq_getD_getElem?, hy]
    rfl
  have hrb : ∀ p, S.rowBits o p = ceilLog2 (y.shape.rows p) := fun p => by
    rw [ProofFile.Honest.K12.Light.rowBits_shape, hg]
  have hrr : ∀ p, realRows S o p = y.shape.rows p := fun p => by
    unfold realRows
    rw [hy]
  unfold wordsOn
  rw [hrb, hrr, hT]
  cases pt <;> rfl

variable {Cells Tok : Type}

/-- **The last thread's words at a message whose table at its seat is the rows.** -/
theorem wordsAtOwn_at_seat (codes : OnBytes.Codes) (arr : Nat → Nat → Nat) (t₁ t₂ : Nat) (s : S₃)
    (v : Wit Cells Tok MsgT) (o j t : Nat) (x : Oracle)
    (hseat : VerifiableInference.Desc.Sound.seatBy
      (VerifiableInference.Desc.Sound.noLast t₁ t₂ s.loc.firstTree) s.book o = some (j, t))
    (hx : s.st.oracles[o]? = some x) (R : Johnson.Prover.Send.Rows)
    (htab : v.tab codes x.shape (arr j t) j t = rowsMsg x.shape R) (pt : OnBytes.Part) (i : Nat) :
    wordsAtOwn codes arr t₁ t₂ s v o pt i = R.word x.shape pt i := by
  refine wordsOn_rowsMsg s.st o x.shape (by rw [hx]; rfl) R _ ?_ pt i
  unfold tabAt
  rw [hseat, hx]
  exact htab

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The last witness at a seat of the first chain's trees is the first chain's witness.** -/
theorem lastWitness_tab_first (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (j t : Nat)
    (hf : ∀ m, P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 ≠
      P5J.At.arr A.Z j t ∧ h.sharedNumbers.tenant m ≠ (j, t))
    (cs : OnBytes.Codes) (s : OracleShape) :
    (lastWitness h first reads k w heard).tab cs s (P5J.At.arr A.Z j t) j t =
      (first.script.wit k w heard).tab cs s (P5J.At.arr A.Z j t) j t := by
  have e1 : (([.oU, .oOmega, .oSp] : List Msg2).find? fun m =>
      P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 ==
        P5J.At.arr A.Z j t) = none := by
    rw [List.find?_eq_none]
    intro m _ e
    exact (hf m).1 (beq_iff_eq.1 e)
  have e2 : (([.oU, .oOmega, .oSp] : List Msg2).find? fun m =>
      h.sharedNumbers.tenant m == (j, t)) = none := by
    rw [List.find?_eq_none]
    intro m _ e
    exact (hf m).2 (beq_iff_eq.1 e)
  funext mask row place
  unfold Wit.tab lastWitness
  dsimp only
  rw [e1, e2]

/-- **The last thread's words at a message whose table at its seat is a given table.** -/
theorem wordsAtOwn_at_table {Cells' Tok' : Type} (codes : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (t₁ t₂ : Nat) (s : S₃) (v : Wit Cells' Tok' MsgT) (o j t : Nat) (x : Oracle)
    (hseat : VerifiableInference.Desc.Sound.seatBy
      (VerifiableInference.Desc.Sound.noLast t₁ t₂ s.loc.firstTree) s.book o = some (j, t))
    (hx : s.st.oracles[o]? = some x) (T : MsgT)
    (htab : v.tab codes x.shape (arr j t) j t = T) (pt : OnBytes.Part) (i : Nat) :
    wordsAtOwn codes arr t₁ t₂ s v o pt i = wordsOn s.st (fun _ => T) o pt i := by
  have e : tabAt codes arr (VerifiableInference.Desc.Sound.seatBy
      (VerifiableInference.Desc.Sound.noLast t₁ t₂ s.loc.firstTree) s.book) s.st v o = T := by
    unfold tabAt
    rw [hseat, hx]
    exact htab
  unfold wordsAtOwn wordsOn
  rw [e]

/-- The search over the three sampled messages finds the one that alone says yes. -/
theorem find_msg2 (p : Msg2 → Bool) (m : Msg2) (hm : p m = true)
    (hu : ∀ m', p m' = true → m' = m) :
    ([.oU, .oOmega, .oSp] : List Msg2).find? p = some m := by
  have key : ∀ m', m' ≠ m → p m' = false := fun m' h => by
    cases e : p m' with
    | false => rfl
    | true => exact absurd (hu m' e) h
  cases m with
  | oU => simp [List.find?, hm]
  | oOmega => simp [List.find?, hm, key .oU (by intro h; cases h)]
  | oSp => simp [List.find?, hm, key .oU (by intro h; cases h), key .oOmega (by intro h; cases h)]

/-- **The last witness at a sampled message's seat is that message's table.** -/
theorem lastWitness_tab_sampled (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn)
    (hA : Function.Injective (fun m : Msg2 => P5J.At.arr A.Z (h.sharedNumbers.tenant m).1
      (h.sharedNumbers.tenant m).2)) (m : Msg2) (cs : OnBytes.Codes) (s : OracleShape) :
    (lastWitness h first reads k w heard).tab cs s
        (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2)
        (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 =
      ProofFile.Honest.FirstThread.sharedTable h reads k ⟨w.w₀, w.rc, A.H.key w.x⟩
        (heard.drop (ProofFile.Honest.declsTo h.description.first.blocksInOrder
          h.description.first.blocksInOrder.length).length) m := by
  have e1 := find_msg2 (fun m' =>
      P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2 ==
        P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) m
    (beq_self_eq_true _) (fun m' e => hA (beq_iff_eq.1 e))
  have e2 := find_msg2 (fun m' => h.sharedNumbers.tenant m' ==
      ((h.sharedNumbers.tenant m).1, (h.sharedNumbers.tenant m).2)) m
    (beq_self_eq_true _) (fun m' e => hA (by
      have e' := beq_iff_eq.1 e
      show P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2 = _
      rw [e']))
  funext mask row place
  unfold Wit.tab lastWitness
  dsimp only
  rw [e1, e2]
  dsimp only
  split <;> rfl

/-- **The last thread's words at a message of a K1 sender of the first chain.** hm, hp: the Script's
tie at the sender's texts (msgs_of_lots, pads_of_lots at a Script of the senders' record). -/
theorem words_first_at_W {Wj Xj : Type} (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (J : ProofFile.Honest.K1.SendJob Wj Xj) (own₀ : Xj) (front n j t : Nat)
    (hf : ∀ m, P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 ≠
      P5J.At.arr A.Z j t ∧ h.sharedNumbers.tenant m ≠ (j, t))
    (hm : ProofFile.Honest.FirstThread.OwnMsgs first.script Vd N (P5J.At.arr A.Z j t) front
      (ProofFile.Honest.K1.msgTxt 0 wit J own₀ n))
    (hp : ProofFile.Honest.FirstThread.OwnPads first.script Vd j t
      (fun k _ => ProofFile.Honest.K1.padTxt 0 J n k))
    (k : Coins A.B) (c : ProofFile.Honest.Cs (ProofFile.Honest.K1.dueR J.P J.ride))
    (hc : ProofFile.Honest.K1.lentCut k 0 ⟨J.P.place, 0⟩ (ProofFile.Honest.K1.dueR J.P J.ride) = some c)
    (w : Local W₀ Rc ProofFile.Inst Tr) (hw : Vd w) (heard : List Fmt.Drawn) (hN : N ≤ heard.length)
    (t₁ t₂ : Nat) (s : S₃) (o : Nat) (x : Oracle)
    (hseat : VerifiableInference.Desc.Sound.seatBy
      (VerifiableInference.Desc.Sound.noLast t₁ t₂ s.loc.firstTree) s.book o = some (j, t))
    (hx : s.st.oracles[o]? = some x) (hsh : x.shape = Johnson.Prover.Send.shapeAt J.P n)
    (pt : OnBytes.Part) (i : Nat) :
    wordsAtOwn J.P.codes (P5J.At.arr A.Z) t₁ t₂ s (lastWitness h first reads k w heard) o pt i =
      (ProofFile.Honest.K1.rowsLaid J own₀ c (wit w) (heard.take front) n).word
        (Johnson.Prover.Send.shapeAt J.P n) pt i := by
  rw [← hsh]
  refine wordsAtOwn_at_seat J.P.codes (P5J.At.arr A.Z) t₁ t₂ s _ o j t x hseat hx _ ?_ pt i
  rw [lastWitness_tab_first h first reads k w heard j t hf, hsh]
  exact ProofFile.Honest.K1.tab_rows first.script Vd N 0 wit J own₀ front n _ j t hm hp k c hc w hw heard hN

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.words_first_at_W
#print axioms ProofFile.Honest.K12.AtProof.wordsOn_rowsMsg
#print axioms ProofFile.Honest.K12.AtProof.wordsAtOwn_at_table
#print axioms ProofFile.Honest.K12.AtProof.lastWitness_tab_sampled
#print axioms ProofFile.Honest.K12.AtProof.wordsAtOwn_at_seat
#print axioms ProofFile.Honest.K12.AtProof.lastWitness_tab_first
