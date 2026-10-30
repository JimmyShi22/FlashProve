-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WordsTiedAtW.lean: the equation WordsAreSent at the words of
which the last thread's item "rows" speaks (wordsAtW, LotWJointAtLastThread.lean), and so WordsTied at
these words: the clause tied of the test's acceptance at the last chain.

  omegaWord         Omega's words in the shared chain's words
  omega_word_rows   these words are the rows of the sending at the head of that chain
  omega_rows_same   the sending at challenge n is the sending at the head where it hears the same
  omega_line        the third line of the equation: wordsAtOwn at Omega's seat
  cut_of_count, rowsLaid_is_member   the cut, and hR₀, hR₁
  far_of_apart      what it takes of a seat, from SharedTenantsApart
  sent_at_W         WordsAreSent at wordsAtW: with words_tied_three, WordsTied at these words

By what. words_first_at_W, wordsAtOwn_at_table, lastWitness_tab_sampled (WordsAtOwnTab.lean);
wordsOn_tableOfWords (Thread/TheFirstThread.lean).

Limits.
- Premises by name. hR₀, hR₁: the sender's rows at its own coins and the challenges in front of it are
  the rows at the test's member: rowsLaid_is_member with members_held; hO: omega_word_rows;
  seats and shapes: the run on shapes. That a stand reaches them is not here.
- NOT IN FRONT OF A LAW OVER COINS.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsAtOwnTab
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsTiedW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Statement OracleShape Oracle ceilLog2)
open OnBytes.Slice (GE rdE frS)
open OnBytes.Means (Words wordsOn realRows tableSize)
open VerifiableInference.Desc.Shared (Msg2)
open VerifiableInference.Desc.Third (S₃)
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest (OnlineProverWithDescription Coins Local State)
open ProofFile.Honest.K14 (Ask)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtOwn wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders lastWitness sharedTable sharedShape tableOfWords wordsOn_tableOfWords)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- Omega's words in the shared chain's words, at that chain's input and challenges. -/
def omegaWord (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) : OnBytes.Part → Nat → GE :=
  fun part i =>
    _root_.Desc.K14.Honest.words2 (VerifiableInference.Desc.K1.qAt A.Z h.places)
      (ProofFile.Honest.FirstThread.sentFirstOf A.Z h.places)
      (_root_.Desc.K14.first (VerifiableInference.Desc.K1.qAt A.Z h.places).codes (A.H.key w.x))
      (ProofFile.Honest.K14.firstRv (heard.drop (ProofFile.Honest.declsTo h.description.first.blocksInOrder
              h.description.first.blocksInOrder.length).length))
      (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights reads.rand
        k ⟨w.w₀, w.rc, A.H.key w.x⟩)
      (ProofFile.Honest.K14.num .oOmega) part i

/-- **Omega's words read as the sending's rows**: rowsO_read, and the shared chain's words at Omega's
number. hO of omega_line at the sending at the head of that chain. -/
theorem omega_word_rows (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) (a : Ask) (hd : List Fmt.Drawn)
    (cs : Array OnBytes.E)
    (hsz : (ProofFile.Honest.K14.jobOmega ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩).Q.sent.size = 2)
    (hs0 : ((ProofFile.Honest.K14.jobOmega ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩).Q.sent.getD 0
      default).shape = (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.omega)
    (hs1 : ((ProofFile.Honest.K14.jobOmega ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩).Q.sent.getD 1
      default).shape = (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.sharedSplit)
    (hV : ProofFile.Honest.K14.VecShape (VerifiableInference.Desc.K1.qAt A.Z h.places).codes
      (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.omega)
    (hno : (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.sharedSplit.mainRows = 0)
    (hp : ProofFile.Honest.K14.elems (ProofFile.Honest.heardFrom
              ({ input := a, heard := hd, own := () } : State Ask Unit) 0 1) =
      Desc.K14.drawn (ProofFile.Honest.K14.firstRv (heard.drop (ProofFile.Honest.declsTo
              h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length)))
    (hpt : (Desc.K14.drawn (ProofFile.Honest.K14.firstRv (heard.drop (ProofFile.Honest.declsTo
              h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))).length =
      (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.kCol)
    (hRw : ∀ r j, (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights
      reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩).Rw r j = rdE.val (a.rows r j))
    (hcO : (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights
        reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩).cOmega =
      ProofFile.Honest.K14.readCoins (VerifiableInference.Desc.K1.qAt A.Z h.places).codes
        (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.omega
        (ProofFile.Honest.K14.msgCoins (ProofFile.Honest.K14.jobOmega
                ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩) cs 0))
    (hcS : (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights
        reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩).cSp =
      ProofFile.Honest.K14.readCoins (VerifiableInference.Desc.K1.qAt A.Z h.places).codes
        (VerifiableInference.Desc.K1.qAt A.Z h.places).par.S.sharedSplit
        (ProofFile.Honest.K14.msgCoins (ProofFile.Honest.K14.jobOmega
                ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩) cs 1))
    (pt : OnBytes.Part) (i : Nat) :
    omegaWord h reads k w heard pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf
        (ProofFile.Honest.K14.jobOmega ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩).Q.sent
        ((ProofFile.Honest.K14.jobOmega ⟨VerifiableInference.Desc.K1.qAt A.Z h.places, 0⟩).rows
          { input := a, heard := hd, own := () } cs) 0 pt i) := by
  rw [ProofFile.Honest.K14.rowsO_read _
    (_root_.Desc.K14.first (VerifiableInference.Desc.K1.qAt A.Z h.places).codes (A.H.key w.x)) _ _ a
    hd cs (by rw [hsz]) hs0 hs1 hV hno hp hpt hRw hcO hcS 0 (by rw [hsz]; decide) pt i]
  show (if 0 + 2 ≤ 2 ∧ 2 < 0 + 2 +
      (Desc.K14.Law.parO (VerifiableInference.Desc.K1.qAt A.Z h.places)).sent.size then _ else _) = _
  rw [if_pos ⟨Nat.le_refl _, by
    have e : (Desc.K14.Law.parO (VerifiableInference.Desc.K1.qAt A.Z h.places)).sent.size = 2 := hsz
    rw [e]
    decide⟩]
  rfl

/-- **The sending read from challenge n on is the sending at the head, where it hears the same.** So
omega_word_rows serves the member of a test behind n challenges. -/
theorem omega_rows_same (Q : Desc.K14.P14) (n : Nat) (a : Ask) (hd hd' : List Fmt.Drawn)
    (cs : Array OnBytes.E) (k : Nat)
    (h : ProofFile.Honest.heardFrom ({ input := a, heard := hd', own := () } : State Ask Unit) n 1 =
      ProofFile.Honest.heardFrom ({ input := a, heard := hd, own := () } : State Ask Unit) 0 1) :
    (ProofFile.Honest.K14.jobOmega ⟨Q, n⟩).rows { input := a, heard := hd', own := () } cs k =
      (ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).rows { input := a, heard := hd, own := () } cs k := by
  have e : (ProofFile.Honest.K14.jobOmega ⟨Q, n⟩).data { input := a, heard := hd', own := () } k =
      (ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).data { input := a, heard := hd, own := () } k := by
    show Desc.K14.Honest.omegaAtE Q.S (ProofFile.Honest.K14.elems (ProofFile.Honest.heardFrom _ n 1)) a.rows =
      Desc.K14.Honest.omegaAtE Q.S (ProofFile.Honest.K14.elems (ProofFile.Honest.heardFrom _ 0 1)) a.rows
    rw [h]
  unfold ProofFile.Honest.K14.SendJob.rows
  rw [e]
  rfl

/-- **The third line of the equation**: at Omega's seat the last thread's words are the shared
chain's words of Omega, read as the sending's rows. -/
theorem omega_line (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc)
    (hA : Function.Injective (fun m : Msg2 => P5J.At.arr A.Z (h.sharedNumbers.tenant m).1
      (h.sharedNumbers.tenant m).2)) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) (codes : OnBytes.Codes) (t₁ t₂ : Nat)
    (s : S₃) (o : Nat) (x : Oracle)
    (hseat : VerifiableInference.Desc.Sound.seatBy
      (VerifiableInference.Desc.Sound.noLast t₁ t₂ s.loc.firstTree) s.book o =
        some ((h.sharedNumbers.tenant .oOmega).1, (h.sharedNumbers.tenant .oOmega).2))
    (hx : s.st.oracles[o]? = some x) (hsh : x.shape = sharedShape A.Z h.places .oOmega)
    (J : ProofFile.Honest.K14.SendJob) (t : State Ask Unit) (cs : Array OnBytes.E) (n : Nat)
    (hJs : (J.Q.sent.getD n default).shape = x.shape)
    (hO : ∀ pt i, omegaWord h reads k w heard pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf J.Q.sent (J.rows t cs) n pt i))
    (pt : OnBytes.Part) (i : Nat) :
    wordsAtOwn codes (P5J.At.arr A.Z) t₁ t₂ s (lastWitness h first reads k w heard) o pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf J.Q.sent (J.rows t cs) n pt i) := by
  rw [wordsAtOwn_at_table codes (P5J.At.arr A.Z) t₁ t₂ s _ o _ _ x hseat hx _
    (lastWitness_tab_sampled h first reads k w heard hA .oOmega codes x.shape) pt i]
  have hxs : (s.st.oracles[o]?).map (·.shape) =
      some ({ shape := sharedShape A.Z h.places .oOmega } : OnBytes.OracleNotice).shape := by
    rw [hx, ← hsh]
    rfl
  by_cases hr : i % 2 ^ s.st.rowBits o pt < realRows s.st o pt
  · show wordsOn s.st (fun _ => tableOfWords (sharedShape A.Z h.places .oOmega)
      (omegaWord h reads k w heard)) o pt i = _
    exact (wordsOn_tableOfWords hxs _ pt i hr).trans (hO pt i)
  · have hb : s.st.rowBits o pt = ceilLog2 (x.shape.rows pt) := by
      rw [ProofFile.Honest.K12.Light.rowBits_shape, Array.getD_eq_getD_getElem?, hx]
      rfl
    have hq : realRows s.st o pt = x.shape.rows pt := by
      unfold realRows
      rw [hx]
    rw [hb, hq] at hr
    have e0 : wordsOn s.st (fun _ => sharedTable h reads k ⟨w.w₀, w.rc, A.H.key w.x⟩
        (heard.drop (ProofFile.Honest.declsTo h.description.first.blocksInOrder
          h.description.first.blocksInOrder.length).length) .oOmega) o pt i = 0 := by
      unfold wordsOn
      rw [hb, hq, if_neg hr]
    rw [e0]
    unfold ProofFile.Honest.K14.wordsOf
    dsimp only
    rw [hJs]
    cases pt with
    | main =>
      have hr' : ¬ i % 2 ^ ceilLog2 x.shape.mainRows < x.shape.mainRows := hr
      show _ = rdE.val (if i % 2 ^ ceilLog2 x.shape.mainRows < x.shape.mainRows then _ else _)
      rw [if_neg hr']
      exact rdE.zero.symm
    | mask =>
      have hr' : ¬ i % 2 ^ ceilLog2 x.shape.maskRows < x.shape.maskRows := hr
      show _ = rdE.val (if i % 2 ^ ceilLog2 x.shape.maskRows < x.shape.maskRows then _ else _)
      rw [if_neg hr']
      exact rdE.zero.symm

/-- **What sent_at_W takes of a seat, from the sentence on the tenants at a tree of the first chain.**
The hash build's sharedTenantsApart (K14/WordsAtLastWitness.lean) has that sentence under the head. -/
theorem far_of_apart (h : HeadAtReturn files A) (hA : ProofFile.Honest.FirstThread.SharedTenantsApart h)
    (j t : Nat) (hj : j < h.description.t₁) (m : Msg2) :
    P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 ≠
      P5J.At.arr A.Z j t ∧ h.sharedNumbers.tenant m ≠ (j, t) :=
  ⟨(hA.2 m j t hj).symm, fun e => hA.2 m j t hj (by rw [e])⟩

/-- **The cut of a K1 sender's coins, from its count in the book.** hd: K1Seated's field hasCoins. -/
theorem cut_of_count {Wj Xj : Type} {Bk : ProofFile.Honest.ProverCoinCounts} (J : ProofFile.Honest.K1.SendJob Wj Xj)
    (hd : ProofFile.Honest.dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = ProofFile.Honest.K1.dueR J.P J.ride)
    (k : Coins Bk) :
    ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨J.P.place, 0⟩ (ProofFile.Honest.K1.dueR J.P J.ride) = some c := by
  have cov : ProofFile.Honest.K1.bookCovers Bk 0 ⟨J.P.place, 0⟩ (ProofFile.Honest.K1.dueR J.P J.ride) = true := by
    unfold ProofFile.Honest.K1.bookCovers
    rw [hd]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  have is := ProofFile.Honest.K1.lentCut_isSome k 0 (by decide) ⟨J.P.place, 0⟩
    (ProofFile.Honest.K1.dueR J.P J.ride)
  rw [cov] at is
  exact Option.isSome_iff_exists.1 is

/-- **The sender's rows at its own coins are the member's rows at the stretch it is carried.** hd: the
data at the two fronts, K1Seated's field heardOnly where what was heard is one; hf, he: members_held. -/
theorem rowsLaid_is_member {Wj Xj : Type} (J : ProofFile.Honest.K1.SendJob Wj Xj) (own₀ : Xj)
    (c : ProofFile.Honest.Cs (ProofFile.Honest.K1.dueR J.P J.ride)) (x : Wj) (heard : List Fmt.Drawn) (n : Nat)
    (hn : n < J.P.sent.size) (fr : ProofFile.Honest.Front Xj) (St : Stretch)
    (hd : J.data x { heard := heard, own := own₀, seen := .bare [] } = J.data x fr)
    (hf : ∀ i, i < (ProofFile.Honest.K1.dueMsg J.P.codes (Johnson.Prover.Send.shapeAt J.P n) (J.ride n)).f →
      ProofFile.Honest.K1.cf c ((ProofFile.Honest.K1.startR J.P J.ride n).f + i) = St.f i)
    (he : ∀ i, i < (ProofFile.Honest.K1.dueMsg J.P.codes (Johnson.Prover.Send.shapeAt J.P n) (J.ride n)).e →
      ProofFile.Honest.K1.ce c ((ProofFile.Honest.K1.startR J.P J.ride n).e + i) = St.e i) :
    ProofFile.Honest.K1.rowsLaid J own₀ c x heard n =
      ProofFile.Honest.K1.rowsR J.P J.ride (J.data x fr)
        (csAt _ (ProofFile.Honest.K1.startR J.P J.ride n) St) n := by
  unfold ProofFile.Honest.K1.rowsLaid
  rw [hd]
  exact (rowsR_csAt J.P J.ride _ n hn St c hf he).symm

/-- **The equation at the last thread's words.** Two K1 senders of the first chain, Omega's sending. -/
theorem sent_at_W {Wa Xa Wb Xb : Type} (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc)
    (hA : Function.Injective (fun m : Msg2 => P5J.At.arr A.Z (h.sharedNumbers.tenant m).1
      (h.sharedNumbers.tenant m).2))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Na Nb : Nat) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (hw : Vd w) (heard : List Fmt.Drawn) (hNa : Na ≤ heard.length)
    (hNb : Nb ≤ heard.length) (s : S₃)
    (wa : Local W₀ Rc ProofFile.Inst Tr → Wa) (Ja : ProofFile.Honest.K1.SendJob Wa Xa) (owna : Xa)
    (fa na ja ta : Nat)
    (hfa : ∀ m, P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 ≠
      P5J.At.arr A.Z ja ta ∧ h.sharedNumbers.tenant m ≠ (ja, ta))
    (hma : ProofFile.Honest.FirstThread.OwnMsgs first.script Vd Na (P5J.At.arr A.Z ja ta) fa
      (ProofFile.Honest.K1.msgTxt 0 wa Ja owna na))
    (hpa : ProofFile.Honest.FirstThread.OwnPads first.script Vd ja ta
      (fun k _ => ProofFile.Honest.K1.padTxt 0 Ja na k))
    (ca : ProofFile.Honest.Cs (ProofFile.Honest.K1.dueR Ja.P Ja.ride))
    (hca : ProofFile.Honest.K1.lentCut k 0 ⟨Ja.P.place, 0⟩ (ProofFile.Honest.K1.dueR Ja.P Ja.ride) = some ca)
    (oa : Nat) (xa : Oracle)
    (hsa : VerifiableInference.Desc.Sound.seatBy (VerifiableInference.Desc.Sound.noLast
      ((dpZ files).at frS.P.T.a).t₁ ((dpZ files).at frS.P.T.a).t₂ s.loc.firstTree) s.book oa =
        some (ja, ta))
    (hxa : s.st.oracles[oa]? = some xa) (hha : xa.shape = Johnson.Prover.Send.shapeAt Ja.P na)
    (hcoa : Ja.P.codes = (ToldDesc.p14At A.Z).codes)
    (wb : Local W₀ Rc ProofFile.Inst Tr → Wb) (Jb : ProofFile.Honest.K1.SendJob Wb Xb) (ownb : Xb)
    (fb nb jb tb : Nat)
    (hfb : ∀ m, P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 ≠
      P5J.At.arr A.Z jb tb ∧ h.sharedNumbers.tenant m ≠ (jb, tb))
    (hmb : ProofFile.Honest.FirstThread.OwnMsgs first.script Vd Nb (P5J.At.arr A.Z jb tb) fb
      (ProofFile.Honest.K1.msgTxt 0 wb Jb ownb nb))
    (hpb : ProofFile.Honest.FirstThread.OwnPads first.script Vd jb tb
      (fun k _ => ProofFile.Honest.K1.padTxt 0 Jb nb k))
    (cb : ProofFile.Honest.Cs (ProofFile.Honest.K1.dueR Jb.P Jb.ride))
    (hcb : ProofFile.Honest.K1.lentCut k 0 ⟨Jb.P.place, 0⟩ (ProofFile.Honest.K1.dueR Jb.P Jb.ride) = some cb)
    (ob : Nat) (xb : Oracle)
    (hsb : VerifiableInference.Desc.Sound.seatBy (VerifiableInference.Desc.Sound.noLast
      ((dpZ files).at frS.P.T.a).t₁ ((dpZ files).at frS.P.T.a).t₂ s.loc.firstTree) s.book ob =
        some (jb, tb))
    (hxb : s.st.oracles[ob]? = some xb) (hhb : xb.shape = Johnson.Prover.Send.shapeAt Jb.P nb)
    (hcob : Jb.P.codes = (ToldDesc.p14At A.Z).codes)
    (R₀ R₁ : Johnson.Prover.Send.Rows)
    (hR₀ : ProofFile.Honest.K1.rowsLaid Ja owna ca (wa w) (heard.take fa) na = R₀)
    (hR₁ : ProofFile.Honest.K1.rowsLaid Jb ownb cb (wb w) (heard.take fb) nb = R₁)
    (oc : Nat) (xc : Oracle)
    (hsc : VerifiableInference.Desc.Sound.seatBy (VerifiableInference.Desc.Sound.noLast
      ((dpZ files).at frS.P.T.a).t₁ ((dpZ files).at frS.P.T.a).t₂ s.loc.firstTree) s.book oc =
        some ((h.sharedNumbers.tenant .oOmega).1, (h.sharedNumbers.tenant .oOmega).2))
    (hxc : s.st.oracles[oc]? = some xc) (hhc : xc.shape = sharedShape A.Z h.places .oOmega)
    (J : ProofFile.Honest.K14.SendJob) (t : State Ask Unit) (cs : Array OnBytes.E) (n : Nat)
    (hJs : (J.Q.sent.getD n default).shape = xc.shape)
    (hO : ∀ pt i, omegaWord h reads k w heard pt i =
      rdE.val (ProofFile.Honest.K14.wordsOf J.Q.sent (J.rows t cs) n pt i)) :
    WordsAreSent s.st (wordsAtW h first reads s k w heard) oa ob oc R₀ R₁
      (Johnson.Prover.Send.shapeAt Ja.P na) (Johnson.Prover.Send.shapeAt Jb.P nb) J t cs n where
  first := fun pt i _ => by
    have e := words_first_at_W h first reads Vd Na wa Ja owna fa na ja ta hfa hma hpa k ca hca w hw
      heard hNa _ _ s oa xa hsa hxa hha pt i
    rw [hcoa, hR₀] at e
    exact e
  second := fun pt i _ => by
    have e := words_first_at_W h first reads Vd Nb wb Jb ownb fb nb jb tb hfb hmb hpb k cb hcb w hw
      heard hNb _ _ s ob xb hsb hxb hhb pt i
    rw [hcob, hR₁] at e
    exact e
  third := fun pt i _ =>
    omega_line h first reads hA k w heard _ _ _ s oc xc hsc hxc hhc J t cs n hJs hO pt i

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.cut_of_count
#print axioms ProofFile.Honest.K12.AtProof.rowsLaid_is_member
#print axioms ProofFile.Honest.K12.AtProof.far_of_apart
#print axioms ProofFile.Honest.K12.AtProof.sent_at_W
#print axioms ProofFile.Honest.K12.AtProof.omega_word_rows
#print axioms ProofFile.Honest.K12.AtProof.omega_rows_same
#print axioms ProofFile.Honest.K12.AtProof.omega_line
