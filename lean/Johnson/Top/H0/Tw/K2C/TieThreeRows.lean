-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeRows.lean: code switching (the kind K2): THE SECOND CLAUSE OF WHAT
STANDS BEHIND THE SWITCH (RowsHoldT, Johnson/Top/H0/K2Hands/TieT.lean: every row that the switch's
group has gained holds of the new messages), AT THE TYPED WITNESS MADE OF A WITNESS OF THE TABLE
OF JOINTS (wtMade, K2Caller/BehindSig.lean), FROM THE TABLE's TWO ITEMS ON CLASSES OF ROWS. A
joining, for the tie t3. NO BLOCK IMPORTS THIS FILE.
  AtYes.behind    what AtYes says of the state behind reads that state's statement alone, and of
                  it the tables and the switch's group's rows: so it holds at every state s''
                  whose statement has the same tables and the same rows there (a quiet step behind
                  the switch)
  rows_behind     AtYes p t s' … x … rows … · KeptPos x.T · the new group was empty · N.groupAt m
                  is its number · the two debts «carried» | «position» · the items «row m carried»
                  and «row m position» at (z, s'), at the table's own reader of words
                  (wordsAtFirst arr) · the book behind seats message n0 + i at seat i · each laid
                  row has no coefficient inside the tables but at a typed entry (hOnly) · ZeroAsks
                  · SlotsAll · at every front fx of the state a' : the same number of messages,
                  the same group, no row in it yet ⟹ RowsHoldT … p a' s' ‹the messages of wtMade
                  iJ iQ seat arr w›
CALLED: rowsHoldT_of_words | words_at_new_paid
(K2Caller/WordsNamesAt.lean · IdxReadsPaid.lean) · yes_rows_say (K2C/RowsSayAll.lean).
WHO PAYS WHAT IS LEFT: hOnly: K2Hands.only_at_rows (K2C/OnlyAtRows.lean), under what hands_of_plan
(K2Hands/TiePaid.lean) makes at an accept · the seats: seat_by_new (K2C/WordsAtNew.lean) with «the
piece's base is the first tree's number plus the own trees sent so far» · the numbers at a' : the
law's condition in front (OnTop) fixes all three. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.WordsNamesAt
import Johnson.Top.H0.K2Caller.IdxReadsPaid
import Johnson.Top.H0.K2Caller.BehindSig
import Johnson.Top.H0.Tw.K2C.RowsSayAll
import Johnson.Desc.First.Close.Law.FillRowFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

theorem AtYes.behind {p : P2} {s s' s'' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hT : SameTables s'.st s''.st)
    (hR : (s''.st.groups[x.f.group]?).map (·.rows) = (s'.st.groups[x.f.group]?).map (·.rows)) :
    AtYes p s s'' r₁ r₂ gs x y S3 Y rows G c :=
  { A with kept := hR.trans A.kept, tables := A.tables.trans hT }

end VerifiableInference.Desc.First.K2

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open OnBytes.Means (Words Says)
open VerifiableInference.Desc (FileDescription Strs Wit)
open VerifiableInference.Desc.Sound (MsgT msgsOf seatBy noFirst wordsFirst)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (seat : Fin r.l.length → ℕ × ℕ)

set_option maxHeartbeats 1000000 in
theorem rows_behind {P Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) {p : K2.P2}
    {t s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (A : K2.AtYes p t s' r₁ r₂ gs x y S3 Y rows Gg c) (hk : K2.KeptPos x.T) (hf : Gg.rows = #[])
    (N : Numbers) (m : ℕ) (z : P) (yy : Strs) (hg : N.groupAt m = x.f.group)
    (hc : ∀ W₀, K2.frameAt x = some W₀ → N.rowsAt m .carried = (0, 1 + K2.keptSamples x W₀))
    (hp : ∀ W₀, K2.frameAt x = some W₀ → N.rowsAt m .position =
      (1 + K2.keptSamples x W₀, r₂.drawn.poss.length * (1 + K2.targetRows x.T + 2)))
    (i1 : rowSays N (wordsAtFirst (P := P) arr) m .carried (z, s') yy w)
    (i2 : rowSays N (wordsAtFirst (P := P) arr) m .position (z, s') yy w)
    (hseat : ∀ i : Fin r.l.length,
      seatBy noFirst s'.book (x.st.oracles.size + i.val) = some (seat i))
    {W₀ : SwitchFrame} {mem row : (selR (Letters.plain r H)).Kp → ℕ}
    {pl : (selR (Letters.plain r H)).Kp → KeptPlace}
    (hOnly : ∀ ρ ∈ rows, OnlyAt r.cs r.l (fun i => x.st.oracles.size + i)
      (Inside (selR (Letters.plain r H)).s W₀ pl) ρ)
    (Q : ZeroAsks (selR (Letters.plain r H)) r.cs r.l iJ iQ W₀ mem row pl x.st.oracles.size
      s'.st)
    (Aall : SlotsAll (selR (Letters.plain r H)).Kp W₀ mem row pl) (a' : Rec)
    (hnum : ∀ fx, K2.frontAt p a' = some fx → fx.st.oracles.size = x.st.oracles.size ∧
      fx.f.group = x.f.group) :
    RowsHoldT (selR (Letters.plain r H))
      (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ
        (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
      (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l iJ iQ
      (baseCount r.set .request r.g) (Letters.plain r H).w₀ p a' s'
      ((selLoc (Letters.plain r H) iJ iQ).S.msgs (wtMade iJ iQ seat arr w).1) := by
  obtain ⟨G', hG', hGr, hsay⟩ := K2.yes_rows_say N (wordsAtFirst (P := P) arr) m z yy w A hk hf hg
    hc hp i1 i2
  refine rowsHoldT_of_words (selR (Letters.plain r H)) _ _ _ _ _ r.cs r.l iJ iQ _ _ p a' s' _ arr w
    (W := W₀) (mem := mem) (row := row) (pl := pl) ?_ ?_ ?_ Aall
  · intro fx hfx n
    rw [(hnum fx hfx).1]
    exact K2.words_at_new_paid r.cs r.l seat arr w s'.st s'.book x.st.oracles.size Q.shapes.codes
      hseat Q.shapes.shape n
  · intro fx hfx G0 G'' _ h1 ρ hρ
    rw [(hnum fx hfx).2, hG'] at h1
    obtain rfl : G' = G'' := Option.some.inj h1
    have hm : ρ ∈ G'.rows.toList := List.mem_of_mem_drop hρ
    rw [(hnum fx hfx).1]
    refine ⟨hsay ρ hm, hOnly ρ ?_⟩
    rw [hGr] at hm
    exact hm
  · intro fx hfx
    rw [(hnum fx hfx).1]
    exact Q

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2.AtYes.behind
#print axioms VerifiableInference.Desc.First.K2Caller.rows_behind
