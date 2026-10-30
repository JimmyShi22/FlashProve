-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskSwitch.lean: CONDITIONAL: THE LOT OF K5's SLOTS OF A
SEGMENT's MASK ROW AND THE CODE SWITCH's WHOLE-MESSAGE LOT ANSWER ONE ELEMENT WHEREVER BOTH ANSWER
(`agree2_mask_switch`): under one premise at every run, on what the book lends K5's row (hB), and
public premises. AND WHERE THE TWO BEAR ONE NUMBER AND THE SWITCH's TEXT ANSWERS WHEREVER K5's DOES,
THE SWITCH's LOT COVERS K5's (`covers_mask_switch`): these two are premises more (hnum, hS), and hS
is none on public data; `covers_mask_switch_at` takes one premise at every run more (hL). What is
WRITTEN where: nothing on what an entry is for. No definition; three theorems, and one small lemma
that stays in the file.

What it is for. The list of lots of which the frame's `Script.ofLots`
(Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) makes a Script is meant to hold the senders'
whole-message lots alone. The honest side of an attention segment's own rounds (kind K5) wants the
frame's form `OwnMsgs` at a text of its own, `maskTxt` (LotsMask.lean in this folder), which answers
at K5's slots alone. `Covers` (Covers.lean in this folder) hands the form over from a sender's lot.
Here the sender's lot is a code switch's (kind K2), with the text `K2.switchMsgTxt`
(Johnson/Desc/ProofFile/Honest/K2/ScriptLots.lean). That a later segment's own messages of moment 0
are sent by the switch that leads into it is that kind's authors' word (the head of
Johnson/Desc/ProofFile/Honest/K2/OwnData.lean), and no theorem here; that the message that `maskMsg`
names is such a message is not said here either.

Main names:
  `agree2_mask_switch`: `Agree2 (maskLot h x₁ kM hk Z5 ν₅) ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing
    p n⟩`.
  `covers_mask_switch`: `Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩ (maskLot …)`,
    its last premise in the weakest form: wherever K5's text answers.
  `covers_mask_switch_at`: the same, with that premise asked at the public test `maskAnswers`.

THE PREMISES, ALL OF THEM.
  hB : `RowIsStretch` (Johnson/Desc/ProofFile/Honest/Law/Rule/TiesFall.lean): AT EVERY RUN: what
    K5's row spends is the stretch of cnt entries of the switch's part's own run, from number
    `K2.maskBase … n` + ν₅ on: an equation between two lists of what the run holds. PROVED HERE AT
    NO BOOK. It follows from a test with code on the book (`rowIsStretch_of`,
    Johnson/Desc/ProofFile/Honest/BookStretch.lean: not imported).
  hn, hl: PUBLIC: n is a message of the switch's sending, and not the last.
  h1: PUBLIC: message n has one mask row. The switch's own files have it from "it has a mask row",
    under the library's head and an opening, at each place of their list (`maskRows_eq_one`,
    `atMostOneMaskRow_at_head`, Johnson/Desc/ProofFile/Honest/K2/Law/OneMaskRowAtHead.lean): NOT
    CALLED: that file stands over files that do not lie beneath this one.
  hN: PUBLIC: K5's slots lie within that row.
  hnum (the two coverings): the two lots bear one number. num IS A LETTER: nothing here says which
    number the switch's lot bears in a list.
  hS (the two coverings): AT EVERY RUN AND INPUT OF WHICH `Covers` SPEAKS: wherever K5's text
    answers, the switch's does: that a text answers, not what. NAMED, NOT PAID. The switch's own
    files say where its text answers: under the library's head and an opening, at a place of their
    list and at their lot's own closing: just where the frame hands the part its stretches and
    `publicOk` holds at the input's public instance (`msgTxt_two_head`,
    Johnson/Desc/ProofFile/Honest/K2/Law/LotsAnswerAtHead.lean): NOT CALLED: that file is dear to
    build.
  hL (`covers_mask_switch_at`) : `Lends5` (CoinsFewOf.lean in this folder): AT EVERY RUN: the
    frame's lending to K5's row returns. It is one Bool of the book and the row (`lends5_iff`,
    LendsRow5.lean in this folder: not imported).
  h: the library's hypothesis on the public input (`P5J.AtMgA`): it stands in the statements as a
    letter of `maskLot`, whose number is made of it. h IS A HYPOTHESIS: it has a member at the
    library's written copy of the full-size public files (`AtFullSide.Top.headMember_zFull`,
    AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the package's files by no theorem: ONE
    EXAMPLE.
  D₁, rd, closing, p, n, cnt, fx, x₁, kM, Z5, ν₅ ARE LETTERS. NOTHING TIES THE SWITCH's PLACE p AND
    ITS MESSAGE n TO K5's SEGMENT (x₁, Z5) BUT hB AND hnum.

How. The sender's own equation is called: `K2.Law.msgTxt_mask`
(Johnson/Desc/ProofFile/Honest/K2/Law/MaskTxt.lean): wherever the switch's text answers at an entry
of a message's mask rows, it answers the element number `maskBase` + ν of the part's own cut.
`K2.eAt_coinsE`, `cut_coinsE` and `getD_stretch` bring that number to the list of which hB speaks;
`OnBytes.Slice.toE_ofE` brings the two readings of an element together. The coverings:
`covers_of_agree`.

Limits. CONDITIONAL. THEY MAY HOLD EMPTILY: `Agree2` asks nothing where the two numbers differ, or
where one of the two texts does not answer; the switch's text answers nowhere where the frame hands
the part nothing, a public test of the switch's fails or the closing refuses; K5's text answers
nowhere at a run at which the list that it reads is empty; `Covers` asks the numbers' equation alone
where K5's text answers nowhere; at a book at which the frame hands the switch's part nothing hS
fails as soon as K5's text answers at one run, input and list of challenges of which `Covers`
speaks, and the coverings then hold of nothing; that hB holds at any place p is not said, least of
all at one that leads elsewhere. At chain number 0 alone. Not at the last message of a sending. No
lot is put into a list here, and no Script is spoken of. That ν₅ is the number of K5's first scalar
in the segment is not said: it is a letter. `ok_of_toOption` is a twin of a sealed lemma of that
name (Johnson/Desc/Plain/StartThree.lean), typed again and kept in the file, so that no further file
is imported; FillSwitch.lean in this folder keeps the like. The file stands over files of the
frame's, of K1's and of K2's folders, and over LotsK5.lean and LotsMask.lean in this folder: none
lies in a seal. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above
the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Covers
import Johnson.Desc.ProofFile.Honest.K5.Law.AgreeK5
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers covers_of_agree)
open P5J (AtMgA TS)

/-- A result that is read as "some" is no refusal. -/
private theorem ok_of_toOption {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok b =>
    have e : b = a := by simpa [Except.toOption] using h
    rw [e]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **THE LOT OF K5's SLOTS AND THE SWITCH's LOT OF MESSAGE n AGREE.** CONDITIONAL: hB: at every
run: what K5's row spends is the stretch of cnt entries of the switch's part's own, from the number
of message n's first mask entry + ν₅ on; hn, hl, h1, hN: public: n is a message of the sending, not
the last; it has one mask row; the slots lie within that row. -/
theorem agree2_mask_switch {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {ν₅ : ℕ}
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) {n cnt : ℕ} (num fx : ℕ)
    (hn : n < (K2.switchSent p.sizes p.others).size)
    (hl : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (h1 : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hB : RowIsStretch Bk 0 Z5.place (H2K5.Honest.shapes Z5.P.x).length ⟨p.place, 0⟩
      (K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅) cnt)
    (hN : ∀ j, j < cnt →
      ν₅ + j < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n) :
    Agree2 (maskLot (Bk := Bk) (W₀ := W₀) (Rc := Rc) (Tr := Tr) h x₁ kM hk Z5 ν₅)
      ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩ := by
  intro _ k w hd mask row place y y' q q'
  have q0 : maskTxt Bk Z5 ν₅ k w (hd.take 0) mask row place = some y := q
  have q1 : K2.switchMsgTxt 0 D₁ rd closing p n k w (hd.take fx) mask row place = some y' := q'
  unfold maskTxt at q0
  split at q0
  · rename_i hg
    obtain ⟨rfl, rfl, hle, hlt⟩ := hg
    obtain rfl := Option.some.inj q0
    have hp : ν₅ + (place - ν₅) = place := Nat.add_sub_cancel' hle
    have e5 : coins5 Bk k Z5 = ((coinsE (k.look 0 ⟨p.place, 0⟩).2).drop
        (K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
          (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅)).take cnt := hB k
    rw [e5] at hlt ⊢
    have hcnt : place - ν₅ < cnt := Nat.lt_of_lt_of_le hlt (by
      rw [List.length_take]
      exact Nat.min_le_left _ _)
    have hν : place < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n := by
      have := hN _ hcnt
      rwa [hp] at this
    have hE := K2.Law.msgTxt_mask 0 D₁ rd closing p hn hl hν k w (hd.take fx)
      (by rw [h1, Nat.mod_one, Nat.div_one, q1]; rfl)
    rw [h1, Nat.mod_one, Nat.div_one, q1] at hE
    obtain ⟨cs, hcut, hcs⟩ := Option.bind_eq_some_iff.1 hE.symm
    obtain ⟨hin, he⟩ := K2.eAt_coinsE (ok_of_toOption hcs)
    unfold K1.lentCut at hcut
    rw [cut_coinsE hcut, getD_stretch _ _ _ _ _ hin, Nat.zero_add] at he
    rw [getD_stretch _ _ _ _ _ hcnt, Nat.add_assoc, hp, he]
    show y' = OnBytes.Slice.toE (OnBytes.Slice.ofE y')
    exact (OnBytes.Slice.toE_ofE _).symm
  · cases q0

/-- **THE SWITCH's LOT OF MESSAGE n COVERS THE LOT OF K5's SLOTS.** CONDITIONAL: hnum: the two lots
bear one number; hn, hl, h1, hN: public; hB: at every run; hS: wherever K5's text answers, the
switch's does. -/
theorem covers_mask_switch {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {ν₅ : ℕ}
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) {n cnt num : ℕ} (fx : ℕ) (hnum : num = maskNo5 h x₁ kM hk)
    (hn : n < (K2.switchSent p.sizes p.others).size)
    (hl : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (h1 : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hB : RowIsStretch Bk 0 Z5.place (H2K5.Honest.shapes Z5.P.x).length ⟨p.place, 0⟩
      (K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅) cnt)
    (hN : ∀ j, j < cnt →
      ν₅ + j < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      (maskTxt Bk Z5 ν₅ k w (hd.take 0) mask row place).isSome = true →
      (K2.switchMsgTxt 0 D₁ rd closing p n k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩
      (maskLot (Bk := Bk) h x₁ kM hk Z5 ν₅) :=
  covers_of_agree hnum (agree2_mask_switch h D₁ rd closing p num fx hn hl h1 hB hN) hS

/-- **THE SAME, WITH THE LAST PREMISE ASKED AT THE PUBLIC TEST.** CONDITIONAL: as
`covers_mask_switch`; hL: at every run the frame's lending to K5's row returns; hS: wherever
`maskAnswers` says yes, the switch's text answers. -/
theorem covers_mask_switch_at {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {ν₅ : ℕ}
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) {n cnt num : ℕ} (fx : ℕ) (hnum : num = maskNo5 h x₁ kM hk)
    (hn : n < (K2.switchSent p.sizes p.others).size)
    (hl : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (h1 : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hB : RowIsStretch Bk 0 Z5.place (H2K5.Honest.shapes Z5.P.x).length ⟨p.place, 0⟩
      (K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅) cnt)
    (hN : ∀ j, j < cnt →
      ν₅ + j < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n)
    {X : Type} {cells : Tr → Cells} (hL : Lends5 W₀ Rc ProofFile.Inst X Bk cells Z5)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      maskAnswers Z5 ν₅ mask row place = true →
      (K2.switchMsgTxt 0 D₁ rd closing p n k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩
      (maskLot (Bk := Bk) h x₁ kM hk Z5 ν₅) :=
  covers_mask_switch h D₁ rd closing p fx hnum hn hl h1 hB hN
    fun k w hd hv hl' mask row place q =>
      hS k w hd hv hl' mask row place
        ((maskTxt_isSome hL ν₅ k w (hd.take 0) mask row place).symm.trans q)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ok_of_toOption
#print axioms ProofFile.Honest.K5.agree2_mask_switch
#print axioms ProofFile.Honest.K5.covers_mask_switch
#print axioms ProofFile.Honest.K5.covers_mask_switch_at
