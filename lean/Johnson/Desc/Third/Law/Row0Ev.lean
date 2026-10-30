-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Ev.lean: THE FIELD ev OF WHAT IS LEFT AT ROW 0 OF THE LAST CHAIN's TABLE
(RowZeroLeft, Johnson/Desc/Third/Law/Row0AtTable.lean; at the closed family of
Johnson/Desc/Third/Law/Row0AtWords.lean), PAID AT A FILLING OF THE TABLE's LETTER: Mg.ev := "the row
(Eval) says its claim" (WRow, Johnson/Desc/K13/Law/Letters.lean) at the first chain's last record,
of the words that the witness gives through that record's own book (wordsFirst).
One definition, theorems.

HOW. Where the record in front is the start's of what was handed, its statement, book and own
group's number are the first chain's last record's. EvalLaid
(Johnson/Desc/K13/Law/Laid.lean) says that the row (Eval) lies among the own group's open rows
there. So RowsHold gives that it says its claim, of the words through the last chain's record: which
are the first chain's own, for the first chain's messages.

OBJECT   startAtEnds · First.S.firstEnd? · linAt (the texts). EvalLaid is what rowsB's yes leaves
         from FrontOk, AT THE RECORD BEHIND THAT BLOCK (rowsB_lays).
USER     the field ev of RowZeroAtWords (ev_field). BEHIND Mg.ev: claim_of_wrow
         (Johnson/Desc/K13/Law/Letters.lean) and rowsTrue_iff_wrow (K13/Law/ClaimBack.lean: not
         in this library) spend WRow with EvalLaid beside: at the shared chain's point.
LETTERS  Pw : K13's Where · arr, t₁, t₂ · fs. At tiedMeaning GET MQ MgS the letter is the
         first table's wrow: MQ.wrow := fun a _ w => WRow Pw a.2 (wordsFirst arr a.2.st a.2.book w)
         (there the link ev of Row0AtFillings.lean is the identity), fs := fun q => (GET q).2.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  linAt_of_firstEnd    what goes on to the last chain is what K13's law reads.
  start_own · started_own   the own group's number in the start's record.
  words_first_at       through the start's record a message has the first chain's own words:
                       words_first (Johnson/Desc/Sound/WordsAt.lean), from its two clauses that are
                       spent (placed · first).
  evI                  the filling.
  ev_atWords           **the link.**   ev_field: RowZeroAtWords' field.
What is not claimed. (1) THAT THE FIRST CHAIN's LAST RECORD HAS EvalLaid INSIDE THE PROMISE: a
premise. Its road, by reading: the promise holds Oc and "no mark"; at Oc := ocEnd, ocEnd_laid
(TieEnd.lean) hands the Bool Mg₁.pub .evalLaid under two tests on the promise's table at the last
border (not run); evalLaidB_iff (Johnson/Desc/K13/Law/Bools.lean) makes that Bool EvalLaid. That
blocks behind rowsB keep EvalLaid is claimed by no file. (2) NOTHING TIES Pw.lin TO p.S: (Eval) is
made at W's layout under Pw.lin, (Dot)'s reader of W reads at W's layout under p.S: one equation at
the plan, owed to whoever spends ev and dot together. (3) THE WORDS ARE THE LAST RECORD's OWN: K13's
laws ALONG the first chain have their reader of words as one letter in front of all records: that it
meets wordsFirst at the last record's book is owed by K13's files. (4) Where a message has no place
in the book the words are the zero table's, on both sides alike: placed does not say that W and the
masks' message HAVE a place. wordsFirst seats a message by its tree's number; the first table's pins
by the tree's place in the book: that ev's W is pinV's W is said nowhere. (5) What (Eval) MEANS is
claim_of_wrow's matter. No member. No soundness of a verifier.

-/
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.K13.Law.Laid
import Johnson.Desc.Third.Law.Row0AtWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open OnBytes.Maker OnBytes.Flat Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid WRow linAt)
open _root_.Desc.K14 (St)
open _root_.Run.PQ (CK)

/-- What goes on to the last chain is what K13's law reads. -/
theorem linAt_of_firstEnd (s : First.S) (e : Proof.FirstEnd) (h : s.firstEnd? = some e) :
    linAt s = some e.lin := by
  unfold First.S.firstEnd? at h
  unfold linAt
  split at h
  · rename_i a hs
    rw [hs]
    show a.lin = some e.lin
    cases hl : a.lin with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      have h' : (if l.w != noId then some (⟨s.st, s.book, l⟩ : Proof.FirstEnd) else none) =
          some e := h
      split at h'
      · obtain rfl := Option.some.inj h'
        rfl
      · cases h'
  · cases h

/-- The own group's number in the record that the start returns is the number that it was handed. -/
theorem start_own (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) : s₀.loc.own = own₁ := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨_, _, _, ho, _⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨_, _, e0⟩ := start₃_inv _ _ _ _ hst
  subst e0
  exact ho

/-- Through a record whose book's places name trees that are there, and whose first own tree's
number counts just one tree more, a message has the words that it has through the first chain's own
reading of that book. -/
theorem words_first_at {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (s : S₃)
    (placed : ∀ (i : ℕ) (q : ℕ × ℕ), s.book.place[i]? = some q → q.1 < s.book.trees.size)
    (first : s.book.trees.size + 1 = s.loc.firstTree) (w : Wit Cells Tok MsgT) (n : ℕ)
    (part : OnBytes.Part) (i : ℕ) :
    wordsLast arr t₁ t₂ s w n part i = wordsFirst arr s.st s.book w n part i := by
  unfold wordsLast wordsFirst
  refine wordsBy_congr arr _ _ s.st s.st w n n rfl ?_ rfl part i
  exact seat_older t₁ t₂ s.loc.firstTree s.book s.book n rfl (fun _ _ => rfl)
    fun q _ hq _ => by have := placed n q hq; omega

section
variable {P S₁ Cells Tok : Type} {p : P₁₄} {fs : P × S₁ → First.S}

/-- In the start's record: the first chain's statement and book; the own group's number that K13's
law reads; the first own tree's number. -/
theorem started_own {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a) :
    a.1.2.st = (fs (a.1.1.1, a.1.1.2.1)).st ∧ a.1.2.book = (fs (a.1.1.1, a.1.1.2.1)).book ∧
      a.1.2.book.trees.size + 1 = a.1.2.loc.firstTree ∧
      ∃ l, linAt (fs (a.1.1.1, a.1.1.2.1)) = some l ∧ a.1.2.loc.own = l.own := by
  obtain ⟨e, _, hs⟩ := h
  unfold startAtEnds start₃F at hs
  cases hf : firstOfS (fs (a.1.1.1, a.1.1.2.1)) with
  | none => rw [hf] at hs; cases hs
  | some f =>
    rw [hf] at hs
    have hs' : start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending (sharedOfEnd e) =
        .ok a.1.2 := hs
    obtain ⟨h1, h2, _, h4, _, _⟩ := startIs _ _ _ _ _ _ _ _ _ _ _ hs'
    have ho := start_own _ _ _ _ _ _ _ _ _ _ _ hs'
    unfold firstOfS at hf
    cases hx : (fs (a.1.1.1, a.1.1.2.1)).firstEnd? with
    | none => rw [hx] at hf; cases hf
    | some x =>
      rw [hx] at hf
      obtain rfl := Option.some.inj hf
      exact ⟨h1, h2, h4, x.lin, linAt_of_firstEnd _ x hx, ho⟩

variable (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)

/-- **The filling of the table's letter Mg.ev**: the row (Eval) says its claim, at the first chain's
last record, of the words through that record's own book. -/
def evI (Pw : Where) (fs : P × S₁ → First.S) : P × S₁ → Strs → Wit Cells Tok MsgT → Prop :=
  fun q _ w => WRow Pw (fs q) (wordsFirst arr (fs q).st (fs q).book w)

variable {arr t₁ t₂}

/-- **The link**: the own group's open rows in front give that (Eval) says its claim. -/
theorem ev_atWords {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (Pw : Where) (h : Started p fs a)
    (hL : EvalLaid Pw (fs (a.1.1.1, a.1.1.2.1)))
    (placed : ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
      q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size)
    (w : Wit Cells Tok MsgT)
    (hr : RowsHold OnBytes.Model.Reading.gl a.1.2 (wordsLast arr t₁ t₂ a.1.2 w)) :
    WRow Pw (fs (a.1.1.1, a.1.1.2.1))
      (wordsFirst arr (fs (a.1.1.1, a.1.1.2.1)).st (fs (a.1.1.1, a.1.1.2.1)).book w) := by
  obtain ⟨e1, e2, e3, l₀, hl₀, ho⟩ := started_own h
  obtain ⟨l, row, r, G, hlin, hrow, _, hrr, hG, hmem, _⟩ := hL
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hlin)
  intro l' r' hl' hr'
  obtain rfl : l₀ = l' := Option.some.inj (hlin.symm.trans hl')
  rw [hrow, hrr] at hr'
  obtain rfl := Option.some.inj hr'
  have hS := hr G (by rw [ho, e1]; exact hG) r hmem
  have hS' := (says_congr OnBytes.Model.Reading.gl a.1.2.st r _ _ fun o _ part i =>
    words_first_at arr t₁ t₂ a.1.2 (by rw [e2]; exact placed) e3 w o part i).1 hS
  rw [e1, e2] at hS'
  exact hS'

end

/-- **RowZeroAtWords' field ev, at that filling.** -/
theorem ev_field {P S₁ Cells Tok : Type} {Fr : Frame} (N : NumbersS)
    (Mg : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (PL : PromMeaningL St S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (Pw : Where)
    (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (fs : P × S₁ → First.S) (hMg : Mg.ev = evI arr Pw fs)
    (started : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a → Started p fs a)
    (laid : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
      EvalLaid Pw (fs (a.1.1.1, a.1.1.2.1)))
    (placed : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
      ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
        q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size) :
    ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
      RowsHold OnBytes.Model.Reading.gl a.1.2 (wordsLast arr t₁ t₂ a.1.2 w) →
      Mg.ev (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w := by
  intro a w ha hr
  rw [hMg]
  exact ev_atWords Pw (started a ha) (laid a ha) (placed a ha) w hr

end VerifiableInference.Desc.Third.Law
