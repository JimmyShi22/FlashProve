-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/IdnAtThread.lean: THE OUTPUT HEAD'S OWN ROUNDS, AT A CHAIN'S
THREAD: THE CELLS THAT THE LAW READS OFF THE THREAD'S WITNESS (Johnson/Desc/Kinds/Law/K6Cut.lean:
compCut) MEET THE ROW'S SEVENTEEN IDENTITIES AT EVERY POSITION, AND THE MEAN'S AND THE COUNT'S FORMS
ARE 0 THERE, AT EVERY CONTINUATION: the field "idn" of K6Script (Honest/K6/Law/OutAtThread.lean) at
that reader: from the thread's own item constr 24 idn, which this member's row takes in.
WHAT IT IS NOT. CONDITIONAL ON ONE MORE STRUCTURE OF PREMISES, K6IdnLetters, WHICH IS SHOWN HERE OF
NO THREAD, on "request" and on "words". THE ITEM IS ITSELF CONDITIONAL (Johnson/P5J/MeansQ.lean:
constrQAt): it speaks only where THE COMMITTED TABLE DECODES to the cells of an index: that is paid
here from the fields "dec" and "inRange"; it is not had of the item. Nothing on the two guests at
the corners: the item that says that of the witness's cells is shut one member in front. Nothing on
soundness, on completeness or on what a proof hides. No example.
  K6IdnLetters   no state of a run stands in it:
       opened    the item is open at the border: the table's own rows.
       means     what the thread's item says gives the composed meaning's constr 24 idn: at the
                 first chain's thread by unfolding.
       fits      the composed meaning's parameters are the head's (Law/K6AtMgAll.lean: MgFitsK6), at
                 valid inputs: as Share.lean's K6ShareLetters asks.
       put       laying a token into a request leaves its two positions (Law/HeadCutsK6.lean:
                 PutKeeps).
       dec       the data's decoder answers, at every state and all strings, with the witness's
                 cells: so the first chain's letters lay it (a constant: the Script's cells; Sound/
                 MgAll.lean: oneDec reads the data's decT alone): there by unfolding. ITS LEFT SIDE
                 NAMES NEITHER THE COINS NOR THE LIST: so it forces the witness's cells to be one
                 and the same at all coins and all lists; at a thread whose witness's cells hang on
                 the challenges the field has no member.
       inRange   the witness's cells are those of an index (InRange: "there is an index that
                 holds"): on the input's validity. K6KeysLetters has the same field.
  hw ("words")   from the pair ThrS T Said: the state's two positions are the request's, as the
                 table's reader gives it.
  hreq ("request")   from the same pair: the small input's request is the one that the head's text
                 reads at the state: one third of K6Script's field keyTie: neither the token nor the
                 lookup's points are asked.
  idn_at_thread  THE TOP.
CALLED, of the library: headPartK6_at, idnPlain_req, parts_of_plain, holds_of_rows.
OF THE FOLDER Johnson/Goal/ it names Meaning.sizesOf, as an argument of the library's compCut;
nothing else of that folder is called.

-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.Ask
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.Kinds.Law.K6AtMgAll
import Johnson.Desc.Kinds.Law.HeadPartsAtX
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Desc.Kinds.Law.IdnPlain
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll)
open ProofFile.Honest (Thread ThrS ProverCoinCounts Coins Local Mid)
open ProofFile.Honest.K6 (HeadAsk)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb Xi P Tok : Type} {rows cols nR : ℕ}
  {Wp : OnBytes.Model.Verify.Public}

/-- **WHAT THE THREAD'S LETTERS ARE ASKED TO MEET, FOR "idn".** iI: the thread's item for constr 24
idn. A definition: a premise's form. Nothing is claimed of it. -/
structure K6IdnLetters
    (T : Thread Bk S Claim (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb) (b : Nat)
    (iI : T.ι)
    (toP : T.P → P) (toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (Dof : Local W₀ Rc ProofFile.Inst Tr → MgData Xi P Tok rows cols nR Wp)
    (Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ) : Prop where
  opened : iI ∈ T.opened b
  means : ∀ w a y v, T.means w iI a y v →
    (mgAll (Dof w) Mg₀).constr 24 .idn (toP a.1, a.2) y (toW v)
  fits : ∀ w, T.valid w → ∃ tokV req dec hN hG tab tokH,
    MgFitsK6 (Dof w) lay6 num n rb tokV req dec hN hG tab tokH
  put : ∀ w, T.valid w → PutKeeps (Dof w).put
  dec : ∀ k w hd a y, T.valid w →
    (Sound.oneDec (Dof w).decT (Dof w).H).dec a y = some (toW (T.wit k w hd)).cells
  inRange : ∀ k w hd, T.valid w →
    VerifiableInference.OnPublicFiles.Flat.InRange (toW (T.wit k w hd)).cells

variable {T : Thread Bk S Claim (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {b : Nat} {iI : T.ι}
  {toP : T.P → P} {toW : T.Wt → Wit (Fin rows → Fin cols → GE) Tok MsgT}
  {Dof : Local W₀ Rc ProofFile.Inst Tr → MgData Xi P Tok rows cols nR Wp}
  {Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {lay6 : ReqLayout} {num : ℕ → ℕ → ℕ} {n rb : ℕ}

/-- **THE CELLS READ OFF THE THREAD'S WITNESS MEET "idn"**, at the prover's letters, at every
continuation. hreq: the small input's request is the one that the head's text reads at the state.
hw: the state's two positions are the request's. -/
theorem idn_at_thread (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk)
    (L : K6IdnLetters T b iI toP toW Dof Mg₀ lay6 num n rb)
    (hw : ∀ k s m E, ThrS T Said b k s m E →
      s.rowR = ((Dof m.st.input).H.req (toP (T.seat k m s).1, s)).val.r ∧
        s.rowE = ((Dof m.st.input).H.req (toP (T.seat k m s).1, s)).val.e)
    (hreq : ∀ k s m E, ThrS T Said b k s m E →
      (wit m.st.input).request = (seatAt Wp.hS (readsOf Wp)).request s) :
    ∀ k s m E, ThrS T Said b k s m E → ∀ ds,
      (letI : Given := (wit m.st.input).given (parOf Wp.hS (workOf Wp)) m.st.heard
       (dataOf (compCut (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
         (Dof m.st.input).N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n rb)
         (toW (T.wit k m.st.input (m.st.heard ++ ds)))).1).Holds ∧
       meanAt (compCut (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
         (Dof m.st.input).N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n rb)
         (toW (T.wit k m.st.input (m.st.heard ++ ds)))).1.toCells = 0 ∧
       countAt (compCut (Dof m.st.input).cs (Dof m.st.input).arr (Dof m.st.input).ms
         (Dof m.st.input).N (Meaning.sizesOf Wp) (seatLay Wp lay6 num) Wp (plAt n rb)
         (toW (T.wit k m.st.input (m.st.heard ++ ds)))).1.toCells = 0) := by
  intro k s m E hT ds
  have hv : T.valid m.st.input := hT.1.2.2.2.2.2.2
  obtain ⟨tokV, req, dec, hN, hG, tab, tokH, F⟩ := L.fits _ hv
  have h1 : P5J.constrQAt (VerifiableInference.OnPublicFiles.headLink Wp) (Dof m.st.input).put
      (Sound.oneDec (Dof m.st.input).decT (Dof m.st.input).H) (Dof m.st.input).headPart
      (Dof m.st.input).digitsPart 24 .idn (toP (T.seat k m s).1, s) (T.strs E)
      (toW (T.wit k m.st.input (m.st.heard ++ ds))) :=
    L.means _ _ _ _ (hT.1.2.2.2.1 ds iI L.opened)
  rw [F.seg] at h1
  unfold P5J.constrQAt at h1
  rw [if_neg (by decide)] at h1
  obtain ⟨i, hi⟩ := L.inRange k m.st.input (m.st.heard ++ ds) hv
  have h2 := h1.2 _ i (L.dec k m.st.input (m.st.heard ++ ds) _ _ hv) hi
  rw [if_pos rfl, F.head, Came.headPartK6_at _ _ _ _ _ _ _ _ _ _ _ _ .idn (by decide)] at h2
  obtain ⟨w1, w2⟩ := hw k s m E hT
  obtain ⟨p1, p2, p3⟩ := L.put _ hv
    ((Sound.oneDec (Dof m.st.input).decT (Dof m.st.input).H).req (toP (T.seat k m s).1, s))
    ((Sound.oneDec (Dof m.st.input).decT (Dof m.st.input).H).hid
      (toW (T.wit k m.st.input (m.st.heard ++ ds)))).tok
  have e3 : ((wit m.st.input).given (parOf Wp.hS (workOf Wp)) m.st.heard).request =
      (seatAt Wp.hS (readsOf Wp)).request s := hreq k s m E hT
  have h3 := Came.idnPlain_req _ _ _
    ((wit m.st.input).given (parOf Wp.hS (workOf Wp)) m.st.heard).request
    (by rw [e3]; exact p2.trans w1.symm) (by rw [e3]; exact p3.trans w2.symm) _ h2
  letI : Given := (wit m.st.input).given (parOf Wp.hS (workOf Wp)) m.st.heard
  obtain ⟨⟨m1, m2⟩, hrows⟩ := Came.parts_of_plain _ h3
  exact ⟨holds_of_rows _ hrows, m1, m2⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.idn_at_thread
