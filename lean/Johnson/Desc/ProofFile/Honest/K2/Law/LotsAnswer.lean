-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LotsAnswer.lean: the kind "the code switch" (K2): WHERE THE
TEXTS OF THE KIND's LOTS (Honest/K2/ScriptLots.lean) ANSWER: AT THE CLOSING AS THE KIND's LOT LAYS
IT (`lotClosingAt`), UNDER ONE PUBLIC TEST ON THE PLACE AND THE SEGMENTS IN FRONT OF IT
(`closingOk`): WHETHER `switchMsgTxt` ANSWERS IS THE SAME AT ALL ENTRIES, ALL CHALLENGES, ALL COINS
OF THE RUN AND ALL INPUTS WITH ONE PUBLIC INSTANCE; and it is said by name what it hangs on. The
like for `switchPadTxt`. Seven statements with their proofs: joins; no definition.

  `handed_public`     whether the frame hands the part anything is the same at all coins of the run
  `rows_isSome`       whether `switchRowsLaid` returns: four public tests
  `msgTxt_isSome`     whether `switchMsgTxt` answers: these four, and whether the part is handed
  `msgTxt_public`     THE SAME AT ALL ENTRIES, CHALLENGES AND COINS, AND AT INPUTS WITH ONE PUBLIC
                      INSTANCE
  `msgTxt_answers`    so, where the five hold, it answers
  `padTxt_isSome`     whether `switchPadTxt` answers at an entry: the library's `padB` there,
                      whether the part's own cut is at hand, and `placeFits`
  `padTxt_public`     so it is the same at all coins

THE FIVE, BY NAME: the frame's `lendPart` hands the part its stretches (at one run's coins: by
`handed_public` at all) · `Sizes.serves` · `Sizes.roomy` · `publicOk` at the input's public instance
(it takes that instance alone) · `placeFits` (the sender's own public test at the place's messages).

By: `lendPart_any`, `look_due`, `cut_some` (Honest/Law/ReadyAny.lean, the frame's authors'): the
lending goes by counts · `returnsLaw` (Honest/K2/Law/SegmentAlike.lean): under `closingOk` the
closing returns just where `publicOk` says yes, at all challenges and all carried stretches ·
`rowsAll_returns`, `rowsAll_fits` (Honest/K2/Law/Laid.lean): the rows return just where the sender's
public test passes, at all data and all coins. Near, not called: `lentCut_isSome`
(Honest/K1/ScriptAtLaw.lean, of other authors): at the first and the shared chain the own cut is at
hand just where their public test `bookCovers` accepts.

Limits. ON WHETHER A TEXT ANSWERS: NOTHING ON WHAT IT ANSWERS. `closingOk` is a premise: shown here
at no place. AT `lotClosingAt` ALONE: at another closing nothing is said. That the five hold is
shown here at no place, book or input. NO LOT IS LAID. All that Honest/K2/ScriptLots.lean's head
says stands. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid
import Johnson.Desc.ProofFile.Honest.K2.Law.PlanAsks
import Johnson.Desc.ProofFile.Honest.Law.ReadyAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.K2.Honest (zeroG)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **Whether the frame hands the part anything is the same at all coins of the run.** -/
theorem handed_public (ch : Nat) (p : SwitchPlace) (k k' : Coins Bk) :
    (handed ch p k).isSome = (handed ch p k').isSome := by
  have key : ∀ a b : Coins Bk, (handed ch p a).isSome = true → (handed ch p b).isSome = true := by
    intro a b h
    unfold handed at h ⊢
    cases e : lendPart Bk (Bk.rowsOf ch) (a.look ch) ⟨p.place, 0⟩
        (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
    | error _ =>
      rw [e] at h
      cases h
    | ok y =>
      obtain ⟨y', hy'⟩ := lendPart_any (look_due a b ch) Bk _ _ _ e
      rw [hy']
      rfl
  exact Bool.eq_iff_iff.2 ⟨key k k', key k' k⟩

/-- **Whether the rows return: four public tests.** -/
theorem rows_isSome (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) :
    (switchRowsLaid D readers (lotClosingAt lay segs) p c w h).toOption.isSome =
      (p.sizes.serves && p.sizes.roomy && publicOk D lay p (segs.take p.link) w.x &&
        placeFits p) := by
  have hR := returnsLaw D readers lay segs p hc w (h.take (h.length - 0)) c.2.2
  unfold switchRowsLaid
  cases hs : p.sizes.serves with
  | false => rfl
  | true =>
    cases hr : p.sizes.roomy with
    | false => rfl
    | true =>
      rw [← hR]
      show ((switchRowsAt p.sizes p.carries c.2.2
        ⟨switchWit D readers (lotClosingAt lay segs) p w, h, ()⟩ 0).bind fun M =>
          rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) M c.1).toOption.isSome = _
      unfold switchRowsAt
      show (((lotClosingAt lay segs p (D w.x) (readers w) (h.take (h.length - 0))
        (Stretch.carried p.carries c.2.2)).map _).bind _).toOption.isSome = _
      cases lotClosingAt lay segs p (D w.x) (readers w) (h.take (h.length - 0))
          (Stretch.carried p.carries c.2.2) with
      | error _ => rfl
      | ok Wl =>
        show (rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) _ c.1).toOption.isSome = placeFits p
        cases hf : placeFits p with
        | true =>
          obtain ⟨V, hV⟩ := rowsAll_returns hf freshTable
            (VerifiableInference.Desc.K2.Honest.mainRows p.sizes Wl
              (switchWit D readers (lotClosingAt lay segs) p w).own) c.1
          rw [hV]
          rfl
        | false =>
          cases hV : rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
              (switchFresh p.sizes p.others p.foldVars)
              (VerifiableInference.Desc.K2.Honest.mainRows p.sizes Wl
                (switchWit D readers (lotClosingAt lay segs) p w).own) c.1 with
          | error _ => rfl
          | ok V =>
            have q : placeFits p = true := rowsAll_fits hV
            rw [hf] at q
            cases q

/-- **Whether `switchMsgTxt` answers.** -/
theorem msgTxt_isSome (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (hc : closingOk freshTable (segs.take p.link) p = true) (n : Nat) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) (mask : Bool) (r j : Nat) :
    (switchMsgTxt ch D readers (lotClosingAt lay segs) p n k w h mask r j).isSome =
      ((handed ch p k).isSome && (p.sizes.serves && p.sizes.roomy &&
        publicOk D lay p (segs.take p.link) w.x && placeFits p)) := by
  unfold switchMsgTxt
  cases handed ch p k with
  | none => rfl
  | some c =>
    show ((switchRowsLaid D readers (lotClosingAt lay segs) p c w h).toOption.map _).isSome = _
    rw [Option.isSome_map, rows_isSome D readers lay segs p hc c w h]
    rfl

/-- **THE SAME AT ALL ENTRIES, CHALLENGES AND COINS, AND AT INPUTS WITH ONE PUBLIC INSTANCE.** -/
theorem msgTxt_public (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (hc : closingOk freshTable (segs.take p.link) p = true) (n n' : Nat) (k k' : Coins Bk)
    (w w' : Local W₀ Rc Xi Tr) (hx : w.x = w'.x) (h h' : List Fmt.Drawn) (mask mask' : Bool)
    (r r' j j' : Nat) :
    (switchMsgTxt ch D readers (lotClosingAt lay segs) p n k w h mask r j).isSome =
      (switchMsgTxt ch D readers (lotClosingAt lay segs) p n' k' w' h' mask' r' j').isSome := by
  rw [msgTxt_isSome ch D readers lay segs p hc, msgTxt_isSome ch D readers lay segs p hc, hx,
    handed_public ch p k k']

/-- **Where the five hold it answers.** -/
theorem msgTxt_answers (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace)
    (hc : closingOk freshTable (segs.take p.link) p = true) (n : Nat) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) (mask : Bool) (r j : Nat)
    (hh : (handed ch p k).isSome = true) (hs : p.sizes.serves = true)
    (hr : p.sizes.roomy = true) (hv : publicOk D lay p (segs.take p.link) w.x = true)
    (hf : placeFits p = true) :
    ∃ y, switchMsgTxt ch D readers (lotClosingAt lay segs) p n k w h mask r j = some y := by
  apply Option.isSome_iff_exists.1
  rw [msgTxt_isSome ch D readers lay segs p hc, hh, hs, hr, hv, hf]
  rfl

/-- **Whether `switchPadTxt` answers at an entry.** -/
theorem padTxt_isSome (ch : Nat) (p : SwitchPlace) (n : Nat) (k : Coins Bk) (mask : Bool)
    (r j : Nat) :
    (switchPadTxt ch p n k mask r j).isSome =
      (padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r j &&
        (K1.lentCut k ch ⟨p.place, 0⟩ (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars))).isSome && placeFits p) := by
  unfold switchPadTxt
  cases padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r j with
  | false => rfl
  | true =>
    cases K1.lentCut k ch ⟨p.place, 0⟩ (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) with
    | none => rfl
    | some c₁ =>
      show ((rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) (fun _ _ _ => zeroG) c₁).toOption.map _).isSome =
          placeFits p
      rw [Option.isSome_map]
      cases hf : placeFits p with
      | true =>
        obtain ⟨V, hV⟩ := rowsAll_returns hf freshTable (fun _ _ _ => zeroG) c₁
        rw [hV]
        rfl
      | false =>
        cases hV : rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) (fun _ _ _ => zeroG) c₁ with
        | error _ => rfl
        | ok V =>
          have q : placeFits p = true := rowsAll_fits hV
          rw [hf] at q
          cases q

/-- **So it is the same at all coins.** -/
theorem padTxt_public (ch : Nat) (p : SwitchPlace) (n : Nat) (k k' : Coins Bk) (mask : Bool)
    (r j : Nat) :
    (switchPadTxt ch p n k mask r j).isSome = (switchPadTxt ch p n k' mask r j).isSome := by
  have key : ∀ a b : Coins Bk, (switchPadTxt ch p n a mask r j).isSome = true →
      (switchPadTxt ch p n b mask r j).isSome = true := by
    intro a b h
    unfold switchPadTxt at h ⊢
    by_cases hp : padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r j
        = true
    · rw [if_pos hp] at h ⊢
      unfold K1.lentCut at h ⊢
      cases e : (a.look ch ⟨p.place, 0⟩).2.cut ⟨0, 0⟩ (sendingDue p.sizes.codes
          (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) with
      | none =>
        rw [e] at h
        cases h
      | some c₁ =>
        rw [e] at h
        obtain ⟨c₂, e₂⟩ := cut_some (look_due a b ch ⟨p.place, 0⟩) _ _ e
        rw [e₂]
        have hf : placeFits p = true := by
          cases hV : rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
              (switchFresh p.sizes p.others p.foldVars) (fun _ _ _ => zeroG) c₁ with
          | error _ =>
            have h' := h
            simp only [Option.bind_some, hV] at h'
            cases h'
          | ok V => exact rowsAll_fits hV
        obtain ⟨V, hV⟩ := rowsAll_returns hf freshTable (fun _ _ _ => zeroG) c₂
        simp only [Option.bind_some, hV]
        rfl
    · rw [if_neg hp] at h
      cases h
  exact Bool.eq_iff_iff.2 ⟨key k k', key k' k⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.handed_public
#print axioms ProofFile.Honest.K2.Law.rows_isSome
#print axioms ProofFile.Honest.K2.Law.msgTxt_isSome
#print axioms ProofFile.Honest.K2.Law.msgTxt_public
#print axioms ProofFile.Honest.K2.Law.msgTxt_answers
#print axioms ProofFile.Honest.K2.Law.padTxt_isSome
#print axioms ProofFile.Honest.K2.Law.padTxt_public
