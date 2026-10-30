-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/SecondWords.lean: the linear claim's second part ("K14, second
part", the first member of a proof file's last chain): ExchangeS (Honest/Thread/PaysS.lean) AT THE
MEMBER 0 OF THE LAST CHAIN's THREAD, AT THE LIBRARY's CLOSED FAMILY OF READERS OF A WITNESS's WORDS
(wordsLast, omWW, wvW and the fence OkW: Johnson/Desc/Third/Law/Row0AtWords.lean;
Johnson/Desc/Sound/WordsAt.lean), where the witness's type is the library's Wit. These readers find
a message by the state's own book of trees. Beside hPL and hblk (the form is fillZ; the member's
text stands at the number 0), second_exchangeS (Honest/K14/SecondFour.lean) has five premises that
tie the letters to words. Two of the five are shown here: Reads is the library's reads_atWords, and
the fence follows from fillZ's test at border 0.

  started_of_fillZ      where fillZ's test at border 0 says yes, the state is the start's of what
                        was handed (Started, Row0AtWords.lean)
  fence_of_fillZ        there the library's fence OkW holds of the two states on both sides of a yes
  second_exchangeS_atWords   **ExchangeS at that family**: beside hPL and hblk THREE PREMISES ARE
                             LEFT, each on one letter
  codes_of_fillZ        where fillZ's test at border 1 says yes, the state's table of codes is the
                        plan's
  rowsOpen_of_there     there RowsThere at wordsLast's words gives the library's closed sentence
                        rowsOpen (Johnson/LLT25R/LastRowsOpen.lean): the premise hRows at that value
                        of the letter ML
  second_exchangeS_atOpen   **ExchangeS at that family and that value of ML** (the equation hML):
                            beside hPL, hblk and hML TWO PREMISES ARE LEFT

THE THREE PREMISES. hEv and hDot are asked where fillZ's test at border 0 says yes, hRows where its
test at border 1 does. hEv: the item ev gives that every open row of the own group in front holds of
wordsLast's words. hDot: the item dot gives the semantic (Dot) (DotSem) at Omega's and W's readers.
hRows: that the own group is there behind, has an open row, and every open row of it holds of
wordsLast's words (RowsThere), gives the item rows. hEv is the converse of the field ev of the
library's RowZeroAtWords; hDot of the field dot of its RowZeroLeft
(Johnson/Desc/Third/Law/Row0AtTable.lean); hRows of the field rows, with RowsThere for RowsHold. hEv
IS MORE THAN "(Eval) HOLDS": it says it of every open row that lies in front.

TWO LIMITS (Honest/K14/SecondFour.lean's head has them at length). (1) NEITHER THIS FILE NOR ANY
FILE THAT IT IMPORTS SHOWS THE ITEMS ev AND dot, which ExchangeS takes from the invariant in front
of the member. (2) THE THEOREMS HOLD
VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE, and neither this file nor any file that it
imports evaluates that test at a state.

What is not claimed. That hEv and hDot hold at any letters. That the thread's invariant holds at any
state. That arr, t₁, t₂ are the file's own numbers. That the member accepts. Nothing on
completeness, soundness or hiding. Terms. letter, border: lean/GLOSSARY.md. A thread is the
invariant along a chain with its parameters (Honest/Thread/Thr.lean). A member is a sub-protocol of
a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondFour
import Johnson.Desc.Third.Law.Row0AtWords
import Johnson.LLT25R.LastRowsOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound (MsgT wordsLast)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart firstOfS startAtEnds start₃F sharedOfEnd)
open VerifiableInference.Desc.Third.Law (RowsHold DotSem RowsThere OkW omWW wvW reads_atWords
  Started fence_atWords)
open VerifiableInference.Desc.Last (fillZ shapeAt_of_fill started_of_shape firstOfS_parts
  behindOk_of_one MeaningL)
open VerifiableInference.Desc.Book (placed_of_fits)
open Desc.K14 (St)

section family
variable {P S₁ : Type} {p : P₁₄} {R : List Fmt.DeclaredRound}
  {fs : P × S₁ → VerifiableInference.Desc.First.S}

/-- Where fillZ's test at border 0 says yes, the state is the start's of what was handed. -/
theorem started_of_fillZ {a : P × S₁} {e : St} {s : S₃}
    (h : (fillZ p R fs).shape 0 a e s = true) :
    Started p fs ((((a.1, a.2, e), s), ()) : ((P × S₁ × St) × S₃) × Unit) := by
  obtain ⟨f, o, hf, ho, hs⟩ := shapeAt_of_fill p R _ _ h
  obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.1 ho
  refine ⟨e', he, ?_⟩
  unfold startAtEnds start₃F
  have hf' : firstOfS (fs (a.1, a.2)) = some f := hf
  show (match firstOfS (fs (a.1, a.2)) with
    | none => (.error "the first chain's end names no W" : Except String S₃)
    | some f => VerifiableInference.Desc.Third.start₃E p.codes p.S f.st f.book f.roots f.w f.own
        f.mask f.pending (sharedOfEnd e')) = .ok s
  rw [hf']
  exact (started_of_shape hs).1

/-- There the library's fence holds of the two states on both sides of a yes of the member. -/
theorem fence_of_fillZ {Cl : Type} {a : P × S₁} {e : St} {s s' : S₃}
    (h : (fillZ p R fs).shape 0 a e s = true)
    (hy : ∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide s rs gs = .ok s') :
    OkW fs (a.1, a.2, e) s s' := by
  obtain ⟨f, o, hf, ho, hs⟩ := shapeAt_of_fill p R _ _ h
  obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.1 ho
  have H := (started_of_shape hs).2.1
  have hf' : firstOfS (fs (a.1, a.2)) = some f := hf
  refine fence_atWords (Y := Unit) (a := (((a.1, a.2, e), s), ())) (started_of_fillZ h) hy
    (fun i q hq => ?_) (fun q hq => ?_)
  · have hq' : (fs (a.1, a.2)).book.place[i]? = some q := hq
    rw [← (firstOfS_parts hf').2.1] at hq' ⊢
    exact placed_of_fits H.fits₁ i q hq'
  · have t := H.tenant
    rw [VerifiableInference.Desc.Third.Law.sharedOfEnd_ended e e' he] at t
    exact t q hq

end family

section atWords
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P S₁ Cells Tok : Type}
  (L : LastThread.Letters Bk St S₃ Cl W₀ Rc Xi Tr X (P × S₁) (Wit Cells Tok MsgT)) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (fs : P × S₁ → VerifiableInference.Desc.First.S)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)

/-- **ExchangeS at the member 0, at the library's closed family of readers.** It takes the items ev
and dot from the invariant in front, and holds vacuously wherever fillZ's test at border 0 is false.
hEv: ev gives that every open row of the own group in front holds of wordsLast's words. hDot: dot
gives the semantic (Dot) at Omega's and W's readers. hRows: where fillZ's test at border 1 says yes,
RowsThere gives the item rows. -/
theorem second_exchangeS_atWords (hPL : L.PL = fillZ p R fs)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hEv : ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (L.Mg inp).ev a y v →
      RowsHold OnBytes.Model.Reading.gl s (wordsLast arr t₁ t₂ s v))
    (hDot : ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (L.Mg inp).dot a e y v →
      DotSem OnBytes.Model.Reading.gl p (omWW arr t₁ p fs (a.1, a.2, e)) (wvW arr p fs a) s v)
    (hRows : ∀ a e s' v, (fillZ p R fs).shape 1 a e s' = true →
      RowsThere OnBytes.Model.Reading.gl s' (wordsLast arr t₁ t₂ s' v) → L.ML.rows s' v) :
    ExchangeS L.thread Said 0 :=
  second_exchangeS L p R fs Said OnBytes.Model.Reading.gl (wordsLast arr t₁ t₂)
    (fun u => OkW fs (u.1.1, u.1.2, u.2)) (fun u => omWW arr t₁ p fs (u.1.1, u.1.2, u.2))
    (fun u => wvW arr p fs u.1) hPL hblk (fun u => reads_atWords arr t₁ t₂ p fs (u.1.1, u.1.2, u.2))
    (fun _ _ _ _ h hy => fence_of_fillZ h hy) hEv hDot hRows

/-- Where fillZ's test at border 1 says yes, the state's table of codes is the plan's. -/
theorem codes_of_fillZ {a : P × S₁} {e : St} {s' : S₃}
    (h : (fillZ p R fs).shape 1 a e s' = true) : s'.st.codes = p.codes := by
  obtain ⟨_, _, _, _, hs⟩ := shapeAt_of_fill p R _ _ h
  obtain ⟨s₀, B⟩ := behindOk_of_one hs
  obtain ⟨_, _, _, _, Ld⟩ := B.laid
  obtain ⟨f, _, hst⟩ := VerifiableInference.Desc.Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨c1, _, e0⟩ := VerifiableInference.Desc.Third.Law.start₃_inv _ _ _ _ hst
  rw [Ld.codes, e0]
  exact c1

/-- **There RowsThere at wordsLast's words gives the library's closed sentence rowsOpen.** -/
theorem rowsOpen_of_there {a : P × S₁} {e : St} {s' : S₃}
    (h1 : (fillZ p R fs).shape 1 a e s' = true) (v : Wit Cells Tok MsgT)
    (h : RowsThere OnBytes.Model.Reading.gl s' (wordsLast arr t₁ t₂ s' v)) :
    LLT25.rowsOpen p.codes arr t₁ t₂ s' v := by
  have hc := codes_of_fillZ p R fs h1
  refine ⟨VerifiableInference.Desc.Third.Law.ownT s', rfl, fun i r hr => ?_⟩
  obtain ⟨G, hG, hi⟩ := OnBytes.Means.rowAt_iff.1 hr
  have hm : r ∈ G.rows.toList :=
    List.mem_iff_getElem?.2 ⟨i, by rw [Array.getElem?_toList]; exact hi⟩
  rw [← hc]
  exact VerifiableInference.Desc.Third.Law.rowsHold_of_there OnBytes.Model.Reading.gl s' _ h G hG r
    hm

/-- **ExchangeS at the member 0, at the library's closed family of readers, where the letter ML is
the library's closed sentence rowsOpen.** It takes the items ev and dot from the invariant in front,
and holds vacuously wherever fillZ's test at border 0 is false. hEv: ev gives that every open row of
the own group in front holds of wordsLast's words. hDot: dot gives the semantic (Dot) at Omega's and
W's readers. -/
theorem second_exchangeS_atOpen (hPL : L.PL = fillZ p R fs)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hML : L.ML = ⟨LLT25.rowsOpen p.codes arr t₁ t₂⟩)
    (hEv : ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (L.Mg inp).ev a y v →
      RowsHold OnBytes.Model.Reading.gl s (wordsLast arr t₁ t₂ s v))
    (hDot : ∀ inp a e s y v, (fillZ p R fs).shape 0 a e s = true → (L.Mg inp).dot a e y v →
      DotSem OnBytes.Model.Reading.gl p (omWW arr t₁ p fs (a.1, a.2, e)) (wvW arr p fs a) s v) :
    ExchangeS L.thread Said 0 :=
  second_exchangeS_atWords L p R fs Said arr t₁ t₂ hPL hblk hEv hDot fun _ _ s' v h1 h => by
    rw [hML]
    exact rowsOpen_of_there p R fs arr t₁ t₂ h1 v h

end atWords

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.started_of_fillZ
#print axioms ProofFile.Honest.K14.fence_of_fillZ
#print axioms ProofFile.Honest.K14.second_exchangeS_atWords
#print axioms ProofFile.Honest.K14.codes_of_fillZ
#print axioms ProofFile.Honest.K14.rowsOpen_of_there
#print axioms ProofFile.Honest.K14.second_exchangeS_atOpen
