-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/WordsUsers.lean: THE WORDS READ THROUGH A RECORD
(Johnson/Desc/Sound/WordsAt.lean),
IN THE FORMS THAT THEIR USERS ASK. Theorems with their proofs; one definition of Prop.

  `words_laid`, `words_other`: for `LaidBy` (Johnson/Desc/Sound/WordsLaw.lean): where the
    members' components are laid from a tuple of messages, the words at a member's number are
    `wordsOn S T` for every family of tables T that has the member's message there; a message whose
    seat and number are no member's keeps its words. PREMISES: the message's seat under seatAt is
    the member's (`seatOf x`) and its shape in S is the member's: named, not paid.
  `words_for_omega_rows_back`, **`omega_rows_back_at`**: `omega_rows_back`
    (Johnson/Desc/Third/Law/Back.lean) ITSELF, spent at the term: its premises "codes" and "words"
    are paid by the fence; "alone" stays.
  `padded_wordsBy`: `Padded` (Johnson/Desc/Means/Says.lean).
  `FrontOk`, `atStart_of_front`, `frontOk_of_start`: the fence `AtStart` (ReadsAt.lean) cut in two:
    what is asked of the record in front alone (for a promise in front of the block), and what the
    block's own yes gives (`bookSays_k14Second`, `sharp_k14Second`, Johnson/Desc/Third/Law/).

Limits. Nothing on soundness or on hiding. NO MEMBER: no record is shown at which the fence holds.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (Statement TreeBook Tree Part)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open OnBytes.Means (Words wordsOn)
open VerifiableInference.Desc.Third (S₃ SharedOut Border P₁₄ batchLinearConstraintsSecondPart start₃E)
open VerifiableInference.Desc.Third.Law (Says bookSays_k14Second sharp_k14Second)

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **(W3), of the words: WHERE THE MEMBERS' COMPONENTS ARE LAID FROM A TUPLE OF MESSAGES, THE WORDS
AT A MEMBER's NUMBER ARE THOSE OF ITS MESSAGE's TABLE.** T: any family of tables that has the
member's
message at o. -/
theorem words_laid (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (mine : List Mem)
    (c : (x : Mem) → ((sigOf S.codes x.1.l).om x.2).Msg) (w w' : Wit Cells Tok MsgT)
    (h : LaidBy S.codes arr mine c w w') (x : Mem) (hx : x ∈ mine) (o : ℕ)
    (hs : seatAt o = some (seatOf x))
    (hsh : (S.oracles[o]?).map (·.shape) = some (x.1.l.get x.2).1) (T : ℕ → MsgT)
    (hT : T o = toMsgT S.codes x.1.l x.2 (c x)) (part : Part) (i : ℕ) :
    wordsBy arr seatAt S w' o part i = wordsOn S T o part i := by
  unfold wordsBy
  exact wordsOn_congr S S T _ o o rfl
    ((tab_laid S.codes arr seatAt S mine c w w' h x hx o hs hsh).trans hT.symm) part i

/-- A message whose seat and number are no member's keeps its words. -/
theorem words_other (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (mine : List Mem)
    (c : (x : Mem) → ((sigOf S.codes x.1.l).om x.2).Msg) (w w' : Wit Cells Tok MsgT)
    (h : LaidBy S.codes arr mine c w w') (o : ℕ)
    (hs : ∀ q, seatAt o = some q → q ∉ mine.map seatOf ∧ arr q.1 q.2 ∉ mine.map (numOf arr))
    (part : Part) (i : ℕ) :
    wordsBy arr seatAt S w' o part i = wordsBy arr seatAt S w o part i := by
  unfold wordsBy
  exact wordsOn_congr S S _ _ o o rfl (tab_other S.codes arr seatAt S mine c w w' h o hs) part i

/-- **The premise "words" of `omega_rows_back`** (Johnson/Desc/Third/Law/Back.lean), at
m' := the words through the record behind and m := the words through the shared chain's end. -/
theorem words_for_omega_rows_back (t₁ t₂ : ℕ) (p : P₁₄) (o : SharedOut) (s s' : S₃)
    (h : Says p s s') (hB : BookedLast o s s') (w : Wit Cells Tok MsgT) :
    ∀ b, s.loc.border = some b → ∀ pt i,
      wordsLast arr t₁ t₂ s' w s.st.oracles.size pt i =
        wordsShared arr t₁ o.st o.book w b.shared.omega pt i := by
  intro b hb pt i
  obtain ⟨g, hg⟩ := hB.border
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans hb)
  exact words_omega arr t₁ t₂ p o s s' h hB w pt i

/-- **`omega_rows_back` ITSELF, SPENT AT THE TERM**: if all sample rows of Omega's copy
hold
of the words through the record behind, all of Omega's sample rows hold, in the border's copy of the
shared statement, of the words through the shared chain's end. Its premises "codes" and "words" are
paid by the fence; "alone" stays. -/
theorem omega_rows_back_at (ρ : OnBytes.Model.Reading GE) (t₁ t₂ : ℕ) (p : P₁₄) (o : SharedOut)
    (s s' : S₃) (h : Says p s s') (hB : BookedLast o s s') (w : Wit Cells Tok MsgT)
    (alone : ∀ b y, s.loc.border = some b → b.shared.st.oracles[b.shared.omega]? = some y →
      ∀ r ∈ y.sampleRows.toList, ∀ x ∈ r.oracles, x = b.shared.omega)
    (hs : ∀ x', s'.st.oracles[s.st.oracles.size]? = some x' →
      OnBytes.Means.AllSay ρ s'.st x'.sampleRows.toList (wordsLast arr t₁ t₂ s' w)) :
    ∃ b y, s.loc.border = some b ∧ b.shared.st.oracles[b.shared.omega]? = some y ∧
      OnBytes.Means.AllSay ρ b.shared.st y.sampleRows.toList (wordsShared arr t₁ o.st o.book w) :=
  VerifiableInference.Desc.Third.Law.omega_rows_back ρ p s s' h _ _
    (fun b hb => by
      obtain ⟨g, hg⟩ := hB.border
      obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans hb)
      exact hB.codes)
    alone (words_for_omega_rows_back arr t₁ t₂ p o s s' h hB w) hs

/-- The words are 0 on the rows beyond the real ones (`Padded`). -/
theorem padded_wordsBy (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (w : Wit Cells Tok MsgT) :
    OnBytes.Means.Padded S (wordsBy arr seatAt S w) :=
  OnBytes.Means.padded_wordsOn S _

end

/-! ## The fence, cut in two: what is asked of the record in front; what the block's yes gives -/

/-- **THE PART OF THE FENCE THAT SPEAKS OF THE RECORD IN FRONT ALONE**: for the promise in front of
the
block. -/
structure FrontOk (st₁ : Statement) (book₁ : TreeBook) (w₁ : ℕ) (o : SharedOut) (s : S₃) :
    Prop where
  border : ∃ g, s.loc.border = some ⟨g, o⟩
  first : s.book.trees.size + 1 = s.loc.firstTree
  codes : o.st.codes = s.st.codes
  placed : ∀ (i : ℕ) (q : ℕ × ℕ), s.book.place[i]? = some q → q.1 < s.book.trees.size
  tenant : ∀ q : ℕ × ℕ, o.book.place[o.omega]? = some q → q.2 = 0
  st : s.st = st₁
  book : s.book = book₁
  w : s.loc.w = w₁
  there : w₁ < st₁.oracles.size

/-- The rest of the fence is the block's own yes (`bookSays_k14Second`, `sharp_k14Second`). -/
theorem atStart_of_front {Cl : Type} (p : P₁₄) (st₁ : Statement) (book₁ : TreeBook) (w₁ : ℕ)
    (o : SharedOut) (s s' : S₃) (hF : FrontOk st₁ book₁ w₁ o s) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    AtStart st₁ book₁ w₁ o s s' :=
  ⟨⟨hF.border, hF.first, hF.codes, bookSays_k14Second p s s' rs gs h,
    sharp_k14Second p s s' rs gs h, hF.placed, hF.tenant⟩, hF.st, hF.book, hF.w, hF.there⟩

/-- The start's record has it, given the two named premises on the two books. -/
theorem frontOk_of_start (codes : OnBytes.Codes) (S : OnBytes.Params.LinShape) (st₁ : Statement)
    (book₁ : TreeBook) (roots₁ w₁ own₁ : ℕ) (mask₁ : Option ℕ) (pile₁ : List OnBytes.TensorRow)
    (o : SharedOut) (s : S₃)
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s)
    (placed : ∀ (i : ℕ) (q : ℕ × ℕ), book₁.place[i]? = some q → q.1 < book₁.trees.size)
    (tenant : ∀ q : ℕ × ℕ, o.book.place[o.omega]? = some q → q.2 = 0) :
    FrontOk st₁ book₁ s.loc.w o s := by
  obtain ⟨e₁, e₂, hb, hf, hc, hw⟩ := startIs codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s h₀
  exact ⟨hb, hf, hc, by rw [e₂]; exact placed, tenant, e₁, e₂, rfl, hw⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.atStart_of_front
#print axioms VerifiableInference.Desc.Sound.frontOk_of_start
#print axioms VerifiableInference.Desc.Sound.words_laid
#print axioms VerifiableInference.Desc.Sound.words_other
#print axioms VerifiableInference.Desc.Sound.words_for_omega_rows_back
#print axioms VerifiableInference.Desc.Sound.omega_rows_back_at
#print axioms VerifiableInference.Desc.Sound.padded_wordsBy
