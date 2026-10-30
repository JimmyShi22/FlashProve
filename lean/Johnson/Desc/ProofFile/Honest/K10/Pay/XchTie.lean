-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTie.lean: the closing of a segment (K10): the equation of the field tie of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean), "the group's tables made of the witness's words are the tables made of the
prover's own rows", from a sentence on the group's members one by one: the witness's table of each member holds, row by
row and place by place, the prover's own entry, and 0 from the code's message length on.

Why that is enough. The group's three tables (`tablesOf`, Johnson/Desc/Means/Says.lean) read words through weights that
are 0 at every message that is no member of the layout. So two lists of words that agree at the members make the same
tables, at all numbers. The witness's words (`wordsFirst`, Johnson/Desc/Sound/WordsAt.lean) are 0 at a row beyond the real
rows; the prover's (`rowWords`, Honest/K10/Xch/Shown.lean) there and from the code's message length on.

  `tablesOf_members`   two lists of words that agree at every member of a layout make the same tables
  `tie_of_words`       so at the closing's layout and the prover's own rows' words
  `realRows_extends`   a later statement has the same real rows at a message that was there
  `ellAt`, `rowsSel`, `rowWords_part`   the prover's words, with the table (main or mask) as a letter
  **`tie_of_tabs`**      from tables T, one for each message, that hold the prover's entries at each member
  **`tie_of_tabAt`**     the same at the witness's own tables (`tabAt`, Johnson/Desc/Sound/TabAt.lean): its end is the end of
                    the field tie, at a witness v as a letter

Limits. The sentence on the members is a premise, shown here of no witness. No head, no thread and no prover is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Shown
import Johnson.Desc.ProofFile.Honest.K10.AskLaw
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement GroupLayout E)
open OnBytes.Means (Words wordsOn realRows Extends extends_begun mem_of_find)
open OnBytes.Slice (readE rdE)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- Two lists of words that agree at every member of a layout make the same tables. -/
theorem tablesOf_members {K : Type} [CommRing K] (S : Statement) (L : GroupLayout) (m m' : Words K)
    (h : ∀ o i, L.find o = some i → ∀ part j, m o part j = m' o part j) :
    OnBytes.Means.tablesOf S L m = OnBytes.Means.tablesOf S L m' := by
  have h1 : (OnBytes.Means.tablesOf S L m).main = (OnBytes.Means.tablesOf S L m').main := by
    funext J
    simp only [OnBytes.Means.tablesOf]
    refine Finset.sum_congr rfl fun o _ => ?_
    cases hf : L.find o with
    | none => rw [(weights_none (K := K) (S := S) hf J).1, zero_mul, zero_mul]
    | some i => rw [h o i hf]
  have h2 : (OnBytes.Means.tablesOf S L m).mask = (OnBytes.Means.tablesOf S L m').mask := by
    funext J
    simp only [OnBytes.Means.tablesOf]
    refine Finset.sum_congr rfl fun o _ => ?_
    cases hf : L.find o with
    | none => rw [(weights_none (K := K) (S := S) hf J).2.1, zero_mul, zero_mul]
    | some i => rw [h o i hf]
  have h3 : (OnBytes.Means.tablesOf S L m).kept = (OnBytes.Means.tablesOf S L m').kept := by
    funext o j
    show OnBytes.keptWeight (K := K) L o * m o .main j = OnBytes.keptWeight (K := K) L o * m' o .main j
    cases hf : L.find o with
    | none => rw [(weights_none (K := K) (S := S) hf 0).2.2, zero_mul, zero_mul]
    | some i => rw [h o i hf]
  calc OnBytes.Means.tablesOf S L m = ⟨(OnBytes.Means.tablesOf S L m).main, (OnBytes.Means.tablesOf S L m).mask, (OnBytes.Means.tablesOf S L m).kept⟩ := rfl
    _ = ⟨(OnBytes.Means.tablesOf S L m').main, (OnBytes.Means.tablesOf S L m').mask, (OnBytes.Means.tablesOf S L m').kept⟩ := by rw [h1, h2, h3]
    _ = OnBytes.Means.tablesOf S L m' := rfl

/-- Words that agree with the prover's own rows' words at the group's members make the same tables. -/
theorem tie_of_words {r : Rec} {D : BaseData} {R : GroupData} {v : Words Cb.Gl.E}
    (h : ∀ o ∈ D.G.members.toList, ∀ part j, v o part j = rowWords D r R o part j) :
    OnBytes.Means.tablesOf (D.S1 r) (Own.layoutOf r.st D.G) v = OnBytes.Means.tablesOf (D.S1 r) (Own.layoutOf r.st D.G) (rowWords D r R) :=
  tablesOf_members _ _ _ _ fun o _ hf => h o (by
    have e := mem_of_find hf
    rwa [layoutOf_members] at e)

/-- A later statement has the same real rows at a message that was there. -/
theorem realRows_extends {S S' : Statement} (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : OnBytes.Part) :
    realRows S' o part = realRows S o part := by
  obtain ⟨x', hx', e⟩ := h.shape o _ (Array.getElem?_eq_getElem ho)
  unfold realRows
  rw [hx', Array.getElem?_eq_getElem ho]
  dsimp only
  rw [e]

/-- The message length of the code of a table's rows. -/
def ellAt (R : GroupData) : OnBytes.Part → Nat
  | .main => R.base.ell
  | .mask => R.zk.ell

/-- A member's rows of a table. -/
def rowsSel : OnBytes.Part → MemberRows → Nat → Nat → E
  | .main => (·.main)
  | .mask => (·.mask)

/-- The prover's own rows' words, with the table as a letter. -/
theorem rowWords_part (D : BaseData) (r : Rec) (R : GroupData) (o : Nat) (part : OnBytes.Part) (i : Nat) :
    rowWords D r R o part i = readE (wordAt (D.S1 r) (ellAt R part) (rowsAt D.G R (rowsSel part)) o part i) := by
  cases part <;> rfl

/-- **The field tie's equation, from tables that hold the prover's entries at each member.** -/
theorem tie_of_tabs {r : Rec} {D : BaseData} {R : GroupData} {T : Nat → Bool → Nat → Nat → Cb.Gl.E}
    (hth : ∀ o ∈ D.G.members.toList, o < r.st.oracles.size)
    (hT : ∀ o ∈ D.G.members.toList, ∀ (part : OnBytes.Part) (b j : Nat), b < realRows r.st o part →
      T o (part == .mask) b j =
        if j < ellAt R part then readE (rowsAt D.G R (rowsSel part) o b j) else 0) :
    OnBytes.Means.tablesOf (D.S1 r) (Own.layoutOf r.st D.G) (wordsOn r.st T) =
      OnBytes.Means.tablesOf (D.S1 r) (Own.layoutOf r.st D.G) (rowWords D r R) := by
  refine tie_of_words fun o ho part i => ?_
  have hs := hth o ho
  have hE : Extends r.st (D.S1 r) := extends_begun r.st r.frame.group D.G
  rw [rowWords_part]
  unfold wordsOn wordAt
  rw [hE.rowBits hs, realRows_extends hE hs]
  by_cases c : i % 2 ^ r.st.rowBits o part < realRows r.st o part
  · rw [if_pos c, hT o ho part _ _ c]
    by_cases c2 : i / 2 ^ r.st.rowBits o part < ellAt R part
    · simp [c, c2]
    · simp only [c, c2, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
      exact rdE.zero.symm
  · rw [if_neg c]
    simp only [c, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
    exact rdE.zero.symm

/-- **The same at a witness's own tables**: the end is the end of the field tie. -/
theorem tie_of_tabAt {Cells Tok : Type} (arr : Nat → Nat → Nat) {s : First.S} {D : BaseData} {R : GroupData}
    {v : Wit Cells Tok MsgT}
    (hth : ∀ o ∈ D.G.members.toList, o < s.st.oracles.size)
    (hT : ∀ o ∈ D.G.members.toList, ∀ (part : OnBytes.Part) (b j : Nat), b < realRows s.st o part →
      tabAt s.st.codes arr (seatBy noFirst s.book) s.st v o (part == .mask) b j =
        if j < ellAt R part then readE (rowsAt D.G R (rowsSel part) o b j) else 0) :
    OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (wordsFirst arr s.st s.book v) =
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R) :=
  tie_of_tabs (r := K9.recOf s) (T := tabAt s.st.codes arr (seatBy noFirst s.book) s.st v) hth hT

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.tablesOf_members
#print axioms ProofFile.Honest.K10.tie_of_words
#print axioms ProofFile.Honest.K10.realRows_extends
#print axioms ProofFile.Honest.K10.ellAt
#print axioms ProofFile.Honest.K10.rowsSel
#print axioms ProofFile.Honest.K10.rowWords_part
#print axioms ProofFile.Honest.K10.tie_of_tabs
#print axioms ProofFile.Honest.K10.tie_of_tabAt
