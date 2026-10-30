-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamWordAt.lean: **THE CLAUSE s1 OF CoreFacts (Johnson/Desc/Sound/SeamFacts.lean): A MEMBER's WORD OFF THE ACTING PART's PLAIN STRINGS IS "THE WORD AS SENT" OFF THE WRITTEN ORACLE, AT A BORDER OF THE SHARED CHAIN.** Statements; each proof is calls of what lies in three
groups of files. NO NEW MATHEMATICS.
  col_act        the acting part's strings at border k and the whole strings have one column at a tree whose number lies from lo on and below the first tree that is not yet sent there.
  **word_at**    for a member x of the list whose tree so lies, and a seat m of the kind's data: HEq (strOf cs sh e0 (layOf m) (W0 Fr no book a.2 m.t).1 (W0 …).2) (wordsOf G cs x.1.l x.1.seat (strsOfAct Fr ((actQ N f l k).2 a)) x.2): s1, TO THE LETTER.
By: wordsOf_col (Johnson/Desc/Sound/ReadsTreeAt.lean) · the row words_are_committed's lemma on the two frames (Johnson/Desc/Sound/FramesMeet.lean), which stands on hM_at | hZ_at.
PREMISES: the tree's number in the window · SeatFits (a test on the plan) · ShownAt at the whole strings (in that row's promise) · SeatIs (at the two tests: seatIs_nine_X | seatIs_ten_X, Johnson/Desc/K12/Coin/SeatIsAtLaw.lean) · the depth's premise (depth_at_desc) · the
member's entry is (sh, e0).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.FramesMeet
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Desc.Sound.BordersSharedQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Maker Johnson.Pack Cb
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Pin (strOf layOf)
open H2K.First (Seat1)

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (f : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))

/-- One column, inside the window. -/
theorem col_act (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) (j : ℕ) (hlo : N.lo ≤ j) (hhi : j < hiAt k f l)
    (x : ℕ) : (strsOfAct Fr ((actQ N f l k).2 a)).col j x = (strsOf Fr a.2).col j x := by
  show ((if N.lo ≤ j ∧ j < hiAt k f l then (posL Fr.all j x).map a.2.2 else none).getD []) =
    ((posL Fr.all j x).map a.2.2).getD []
  rw [if_pos ⟨hlo, hhi⟩]

/-- **s1, to the letter.** -/
theorem word_at (cs : Codes) {Xi : Type} (G : FileDescription Xi) (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str)
    (x : Mem) (m : Seat1) (no : ℕ → ℕ) (book : TreeBook) (hlo : N.lo ≤ (x.1.seat x.2).1)
    (hhi : (x.1.seat x.2).1 < hiAt k f l) (hF : SeatFits G cs x.1.l x.1.seat)
    (hS : ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2)
    (hI : ∀ o, G.oracleAt (x.1.seat x.2).1 = some o →
      SeatIs no book m (x.1.seat x.2).1 (x.1.seat x.2).2 o)
    (hd : ∀ o, G.oracleAt (x.1.seat x.2).1 = some o →
      ∀ e ∈ Fr.all, e.no = (x.1.seat x.2).1 → e.a ≤ o.logLength)
    (sh : OracleShape) (e0 : ℕ) (he : x.1.l.get x.2 = (sh, e0)) :
    HEq (strOf cs sh e0 (layOf m) (W0 Fr no book a.2 m.t).1 (W0 Fr no book a.2 m.t).2)
      (wordsOf G cs x.1.l x.1.seat (strsOfAct Fr ((actQ N f l k).2 a)) x.2) := by
  rw [wordsOf_col G cs x.1.l x.1.seat (strsOf Fr a.2) _ x.2 (col_act N f l k a _ hlo hhi),
    wordsOf_is_strOf cs G x.1.l x.1.seat Fr no book a.2 x.2 m hF hS hI hd]
  have key : ∀ p : OracleShape × ℕ, p = (sh, e0) →
      HEq (strOf cs sh e0 (layOf m) (W0 Fr no book a.2 m.t).1 (W0 Fr no book a.2 m.t).2)
        (strOf cs p.1 p.2 (layOf m) (W0 Fr no book a.2 m.t).1 (W0 Fr no book a.2 m.t).2) := by
    rintro _ rfl
    exact HEq.rfl
  exact key _ he

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.col_act
#print axioms Desc.K14.Law.Fence.word_at
