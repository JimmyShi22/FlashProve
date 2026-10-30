-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerReader.lean: THE TABLE's FIXED READER OF A WITNESS AND THE READER THAT IS
HANDED THE RECORD SAY THE SAME OF A MESSAGE, INSIDE THE MESSAGE's RANGE. The ledger's clauses at the
shared chain read a witness's words by rgOf (Johnson/Desc/K14/Law/LedgerPins.lean): at the member
that the plan's letter mem lays at a number, through the typed message msgsOf, by a letter rd. The
last chain's first block pays (Dot)'s equation at wordsShared arr t₁ d.st d.book w
(Johnson/Desc/Sound/WordsAt.lean): the seat is read off the record's own book. HERE rd IS FILLED,
and the two are one at every index whose place lies below the code's message length.

  rdK             **the filling of rd**: wordsOn's own cut of an index into row and place
                  (Johnson/Desc/Means/ItemsTab.lean), at the member's shape, through toMsgT.
  wordsSh         wordsShared, unfolded (one term, by rfl: wordsSh_is,
                  Johnson/Desc/K14/Law/LedgerReaderAt.lean): WordsAt.lean and the fence
                  (Johnson/Desc/Sound/Fence.lean) each declare a structure Sound.Booked: no module
                  can import both, and the ledger stands over the fence.
  rg_is_shared    **the tie**, at a message's main table.
  same_omega      so at the indices that (Dot)'s equation reads of o_omega (the layout's index of y,
                  y below the matrix's rows): SameOmega's body
                  (Johnson/Desc/K14/Law/ClaimsRead.lean).
WHY "INSIDE THE RANGE". wordsOn reads the witness's table at EVERY place; beyond the message's
length that is pinned by nothing (Wit.tab). A typed message has the places below the length alone:
no filling of rd sees the rest. At all indices the two readers part.
WHAT STAYS, AND WHOSE. hm (the plan's mem, at the number that the record notes) · hc (the record's
codes are the plan's) · hx, hs (the record's shape at the number is the member's) · hseat (the seat
that the record's book gives the number is the member's) · hin (the layout's indices lie in range: a
test on the plan). At the shared chain's last border hc, hx, hs, hseat and the number are had from
what stands beside shapeK: omega_at_last, Johnson/Desc/K14/Law/LedgerLast.lean.
What is not claimed. No member. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerPins
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open OnBytes.Means (Words wordsOn realRows)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound

/-- **The filling of rd**: a typed message as words: row i % 2 ^ b, place i / 2 ^ b, b the bits of
the member's rows; 0 on the rows beyond the real ones. -/
def rdK (cs : OnBytes.Codes) (x : Mem) (m : ((sigOf cs x.1.l).om x.2).Msg) (part : Part) (i : ℕ) :
    GE :=
  if i % 2 ^ ceilLog2 ((x.1.l.get x.2).1.rows part) < (x.1.l.get x.2).1.rows part then
    toMsgT cs x.1.l x.2 m (part == .mask) (i % 2 ^ ceilLog2 ((x.1.l.get x.2).1.rows part))
      (i / 2 ^ ceilLog2 ((x.1.l.get x.2).1.rows part))
  else 0

variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem)

/-- **The reader that is handed the record**: wordsShared arr t₁ st book w
(Johnson/Desc/Sound/WordsAt.lean), UNFOLDED: that file and the fence (Johnson/Desc/Sound/Fence.lean)
each declare a structure Sound.Booked, so no module can import both; the ledger stands over the
fence. wordsSh_is (Johnson/Desc/K14/Law/LedgerReaderAt.lean): the two are one term, by rfl. -/
abbrev wordsSh (t₁ : ℕ) (st : Statement) (book : TreeBook) (w : Wit Cells Tok MsgT) : Words GE :=
  wordsOn st (VerifiableInference.Desc.Sound.tabAt st.codes arr (seatBy (noShared t₁) book) st w)

/-- **The tie**, at the main table of the message number o. -/
theorem rg_is_shared (t₁ : ℕ) (d : St) (w : Wit Cells Tok MsgT) (o : ℕ) (x : Mem) (X : Oracle)
    (hm : mem o = some x) (hc : d.st.codes = cs) (hx : d.st.oracles[o]? = some X)
    (hs : X.shape = (x.1.l.get x.2).1)
    (hseat : seatBy (noShared t₁) d.book o = some (x.1.seat x.2)) (i : ℕ)
    (hi : i / 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (pMain cs (x.1.l.get x.2).1).ell) :
    wordsSh arr t₁ d.st d.book w o .main i = rgOf cs arr mem (rdK cs) w o .main i := by
  subst hc
  have hb : d.st.rowBits o .main = ceilLog2 (x.1.l.get x.2).1.mainRows := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (X.shape.rows .main) = _
    rw [hs]
    rfl
  have hr : realRows d.st o .main = (x.1.l.get x.2).1.mainRows := by
    unfold realRows
    rw [hx]
    show X.shape.rows .main = _
    rw [hs]
    rfl
  have eR : rgOf d.st.codes arr mem (rdK d.st.codes) w o .main i =
      rdK d.st.codes x (msgsOf d.st.codes x.1.l x.1.seat arr w x.2) .main i := by
    unfold rgOf
    rw [hm]
  rw [eR]
  unfold wordsSh wordsOn rdK
  rw [hb, hr]
  show _ = if i % 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (x.1.l.get x.2).1.mainRows then _ else 0
  by_cases h : i % 2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (x.1.l.get x.2).1.mainRows
  · rw [if_pos h, if_pos h]
    unfold VerifiableInference.Desc.Sound.tabAt toMsgT
    rw [hseat, hx]
    show w.tab d.st.codes X.shape _ _ _ _ _ _ = _
    rw [hs]
    show _ = if h' : _ ∧ _ then _ else 0
    rw [dif_pos ⟨h, hi⟩]
    rfl
  · rw [if_neg h, if_neg h]

/-- **At the indices that (Dot)'s equation reads of o_omega.** -/
theorem same_omega (t₁ : ℕ) (S : LinShape) (d : St) (w : Wit Cells Tok MsgT) (x : Mem) (X : Oracle)
    (hm : mem d.loc.oOmega = some x) (hc : d.st.codes = cs)
    (hx : d.st.oracles[d.loc.oOmega]? = some X) (hs : X.shape = (x.1.l.get x.2).1)
    (hseat : seatBy (noShared t₁) d.book d.loc.oOmega = some (x.1.seat x.2))
    (hin : ∀ y < S.matrixRows, (linLayOmega d.st.codes S).index y /
      2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (pMain cs (x.1.l.get x.2).1).ell) :
    ∀ y < S.matrixRows,
      wordsSh arr t₁ d.st d.book w d.loc.oOmega .main ((linLayOmega d.st.codes S).index y) =
        rgOf cs arr mem (rdK cs) w d.loc.oOmega .main ((linLayOmega d.st.codes S).index y) :=
  fun y hy => rg_is_shared cs arr mem t₁ d w _ x X hm hc hx hs hseat _ (hin y hy)

end Desc.K14.Law

#print axioms Desc.K14.Law.rg_is_shared
#print axioms Desc.K14.Law.same_omega
