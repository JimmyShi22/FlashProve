-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamWords.lean: **THE SEAM's CORE, ITS PART ON THE WORDS (s5): K12's FILES' WORDS OF A TUPLE (wordsT, Johnson/Desc/K12/Law/TupleWords.lean) AND K14's FILES' (wordsT, Johnson/Desc/K14/Law/LedgerSay.lean) ARE ONE AT THE GROUP's MEMBERS, AND THE ROWS THAT A TEST TAKES IN READ NO OTHER.** Statements and proofs.
  rdK_tabP        the filling of the reader (rdK, Johnson/Desc/K14/Law/LedgerReader.lean) IS K12's files' two tables of a message (tabP, Johnson/Desc/K12/Law/TupleWords.lean), at every index.
  tabP_heq        tabP crosses an equation of shapes.
  words_member    at a member's number: wordsT D c' (K12's files': by the layout's find) = wordsT cs mem rd c (K14's files': by the plan's mem), where the layout finds the number at the member's place, the plan's mem lays a member of the list there whose
                  entry has the member's shape, and c at it is c' at the place, up to the types' equation.
  run_agree       the rows that a proximity test takes in (the group's open rows; its members' sample rows), said at a statement that has grown out of one in order, read the group's members' words alone: by says_agree.
Limits. AT ANOTHER NUMBER THE TWO PART: K12's files' words are 0 there, K14's files' need not be. NO SOUNDNESS.

-/
import Johnson.Desc.K14.Law.LedgerReader
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.K12.Law.TupleWords
import Johnson.Desc.Means.ItemsRead
import Johnson.Desc.Means.GrowsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Johnson.Pack Cb
open OnBytes.Means (Words AllSay InOrder RowIn says_agree extends_of_grows mem_samples)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Sound
open H2K.First (Plain)
open _root_.Desc.K14.Law (rdK)

/-- **The two readers of a typed message are one.** -/
theorem rdK_tabP (cs : Codes) (x : Mem) (m : ((sigOf cs x.1.l).om x.2).Msg) (part : Part) (i : ℕ) :
    rdK cs x m part i = H2K.Pin.tabP cs (x.1.l.get x.2).1 m part i := by
  cases part
  · show (if i % 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (x.1.l.get x.2).1.mainRows then
        (if h : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (x.1.l.get x.2).1.mainRows ∧
            i / 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (pMain cs (x.1.l.get x.2).1).ell then
          m (.inl (⟨_, h.1⟩, ⟨_, h.2⟩)) else 0) else 0) =
      (if h : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (x.1.l.get x.2).1.mainRows ∧
          i / 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (pMain cs (x.1.l.get x.2).1).ell then
        m (.inl (⟨_, h.1⟩, ⟨_, h.2⟩)) else 0)
    by_cases h1 : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (x.1.l.get x.2).1.mainRows
    · rw [if_pos h1]
    · rw [if_neg h1, dif_neg fun h => h1 h.1]
  · show (if i % 2 ^ ceilLog2 (x.1.l.get x.2).1.maskRows < (x.1.l.get x.2).1.maskRows then
        (if h : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.maskRows < (x.1.l.get x.2).1.maskRows ∧
            i / 2 ^ ceilLog2 (x.1.l.get x.2).1.maskRows < (pMask cs (x.1.l.get x.2).1).ell then
          m (.inr (⟨_, h.1⟩, ⟨_, h.2⟩)) else 0) else 0) =
      (if h : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.maskRows < (x.1.l.get x.2).1.maskRows ∧
          i / 2 ^ ceilLog2 (x.1.l.get x.2).1.maskRows < (pMask cs (x.1.l.get x.2).1).ell then
        m (.inr (⟨_, h.1⟩, ⟨_, h.2⟩)) else 0)
    by_cases h1 : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.maskRows < (x.1.l.get x.2).1.maskRows
    · rw [if_pos h1]
    · rw [if_neg h1, dif_neg fun h => h1 h.1]

/-- tabP crosses an equation of shapes. -/
theorem tabP_heq (cs : Codes) (sh sh' : OracleShape) (e : sh' = sh)
    (m' : (portCode cs sh').J → GE) (m : (portCode cs sh).J → GE) (h : HEq m' m) (part : Part)
    (i : ℕ) : H2K.Pin.tabP cs sh' m' part i = H2K.Pin.tabP cs sh m part i := by
  subst e
  rw [eq_of_heq h]

/-- **At a member's number K12's and K14's files' words of a tuple are one.** -/
theorem words_member (D : Plain)
    (c' : ∀ j : Fin D.mems.length, (portCode D.st.codes (D.mems.get j).sh).J → GE)
    (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf D.st.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = H2K.Pin.tabP D.st.codes (x.1.l.get x.2).1 m part i)
    (c : (x : Mem) → ((sigOf D.st.codes x.1.l).om x.2).Msg) (j : Fin D.mems.length) (o : ℕ)
    (hfind : D.L.find o = some j.val) (x : Mem) (hm : mem o = some x)
    (he : (x.1.l.get x.2).1 = (D.mems.get j).sh) (hc : HEq (c x) (c' j)) (part : Part) (i : ℕ) :
    H2K.Pin.wordsT D c' o part i = _root_.Desc.K14.Law.wordsT D.st.codes mem rd c o part i := by
  unfold H2K.Pin.wordsT _root_.Desc.K14.Law.wordsT
  rw [hfind, hm]
  show (if h : j.val < D.mems.length then
      H2K.Pin.tabP D.st.codes (D.mems.get ⟨j.val, h⟩).sh (c' ⟨j.val, h⟩) part i else 0) =
    rd x (c x) part i
  rw [dif_pos j.isLt, hrd]
  exact (tabP_heq D.st.codes _ _ he (c x) (c' j) hc part i).symm

/-- **The rows that a test takes in read the group's members' words alone.** -/
theorem run_agree (S T : Statement) (hI : InOrder S) (gr : Grows S T) (g : ℕ) (G0 : Group)
    (hG : S.groups[g]? = some G0) (W W' : Words GE)
    (h : ∀ o ∈ G0.members.toList, ∀ part i, W o part i = W' o part i)
    (hs : AllSay OnBytes.Model.Reading.gl T (runRows S G0).toList W) :
    AllSay OnBytes.Model.Reading.gl T (runRows S G0).toList W' := by
  intro r hr
  have hr0 := hr
  unfold runRows at hr
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
  have open_ : ∀ r ∈ G0.rows.toList, OnBytes.Means.Says OnBytes.Model.Reading.gl T r W →
      OnBytes.Means.Says OnBytes.Model.Reading.gl T r W' := fun r hr' hs' =>
    (says_agree OnBytes.Model.Reading.gl
      (RowIn.extends (extends_of_grows gr) (fun _ c => c) (hI.rows g G0 hG r hr')) h).1 hs'
  rcases hr with (c | c) | c
  · exact open_ r c.1 (hs r hr0)
  · rw [← Array.foldl_toList] at c
    rcases mem_samples S r _ _ c with c' | ⟨o, ho, x, hx, hr'⟩
    · simp at c'
    · refine (says_agree OnBytes.Model.Reading.gl
        (RowIn.extends (extends_of_grows gr) (fun _ c => c) (hI.samples o x hx r hr'))
        fun o' ho' part i => ?_).1 (hs r hr0)
      have e : o' = o := by simpa using ho'
      rw [e]
      exact h o ho part i
  · exact open_ r c.1 (hs r hr0)

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.run_agree
#print axioms Desc.K14.Law.Fence.rdK_tabP
#print axioms Desc.K14.Law.Fence.words_member
