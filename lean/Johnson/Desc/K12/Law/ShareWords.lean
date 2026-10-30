-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ShareWords.lean: the words that a witness's own tables hold are, at a member's
entries, the member's share of the witness. Statements and proofs.

It works towards the premise hS of Johnson/Desc/K12/Law/NoneNearCand.lean. One limit comes first:
`answers_of_says` below speaks of the row that `Send.form` returns, whose target is the default 0;
the record holds { row with target := the answer }. So it can be called at no real row. It is
overtaken by `answers_of_says_t` (Johnson/Desc/K12/Law/SampleAt.lean) and `answers_of_says_g`
(Johnson/Desc/K12/Law/FormTake.lean). `words_share` and `tabBack_group` stand as they are. What was
meant: of a near witness, "the member's sample row holds of the witness's own words" gives "the
member's share has the sample's answer". No frame and no view stands in this file, and there is no
new mathematics: indices.
Main names:
  `tabBack_group`: one table back (`tabBack`, Johnson/Desc/K12/Law/RInSays.lean), read where the
    program's `groupIndex` puts a member's entry: the entry (row r, place c) of a member whose block
    begins at the row "first" is the message's entry at the vertex of the row first + r and the
    place c.
  `words_share`: wordsOf S L (tabOf s w) o (partZ j) (locZ j) = w ((seat).atJ j): the words that a
    witness's own tables hold are, at a member's entries, the member's share of the witness. Of
    every message w, near or not.
  `answers_of_says` (overtaken: see above): hS at the own row of `Send.form`: from `s.Sized`, e <
    s.d, `LayFacts`, `RowsBlank` of y, the witness within e positions of y, and the premises of
    `words_share` and of `says_sample`: Says rdE S r (the witness's own words) → (portOmZ S.codes
    x.shape e0).Z.val (the seed read, β) (the share) = fun _ => readE r.target. By `blank_of_near`
    and `padded_wordsOf` (Johnson/Desc/K12/Law/TabWords.lean: `Padded`, for near witnesses alone),
    `says_sample` (Johnson/Desc/K12/Law/SaysSample.lean) and `words_share`.
The premises on the seat and the layout (hpM, hpZ: the seat is by numbers; hrM, hrZ: room; hf, hk,
hm, hz: the layout finds the member, not kept, its blocks beginning at these numbers; hLk, hLh) are
the content of the library's `Gp.Numbered` and of `SeatsAre`
(Johnson/Desc/K12/Law/RowsBlankWord.lean) at one member.
Limits: that these premises hold together at some member is not shown here.
Johnson/Desc/K12/Law/RowsBlankGp.lean shows `Numbered` and `SeatsAre` of the law's own group `gpG`
(from `Good` and `Made`), whose members' formats are not those of `mbOfShape` (limit (1) of
Johnson/Desc/K12/Law/ShareNear.lean): the two groups again. No verifier stands in these statements,
so there is no degenerate verifier to try them on; the risk is emptiness, and it is named.
Still owed for hS at a real member: that r, the member's sample row in the record
(`Oracle.sampleRows`), is that of `Send.form` at a seed with hzl and hβ, and stands among the rows
that the batching takes. The record keeps the rows, not the seeds: it is for the law of the sending
to pay.
No soundness is claimed, and nothing is said on hiding.
On names: `wordsOf` is written out as `H2K.ClaimSays.wordsOf` where Lean cannot pick by type: the
library has an `OnBytes.Slice.wordsOf`.
Lemmas called (none runs in a context of `verify-on-bytes`): `le_two_pow_ceilLog2`
(OnBytes/Slice/ProgCodes.lean); `blank_of_near`, `padded_wordsOf`, `says_sample`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.NoneNearCand
import Johnson.Desc.K12.Law.SaysSample
import Johnson.Desc.K12.Law.RowsBlankWord

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice Johnson.Pack
open OnBytes.Means H2K.ClaimSays

/-- One table back, read where the program's groupIndex puts a member's entry: the entry (row r,
place c) of a member whose block begins at the row first is the message's entry at the vertex of the
row first + r and the place c. -/
theorem tabBack_group (k l : ℕ) (w : (Fin k → Bool) × Fin l → GE) (first r c rb : ℕ) (hr : r < 2 ^
    rb)
    (hroom : first + r < 2 ^ k) (hc : c < l) :
    tabBack k l w (groupIndex (r + 2 ^ rb * c) rb first k) = w (vtx k (first + r), ⟨c, hc⟩) := by
  have h1 : (r + 2 ^ rb * c) % 2 ^ rb = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : (r + 2 ^ rb * c) / 2 ^ rb = c := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos rb), Nat.div_eq_of_lt hr, Nat.zero_add]
  unfold groupIndex
  rw [h1, h2]
  have h3 : (first + r + c * 2 ^ k) / 2 ^ k = c := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hroom, Nat.zero_add]
  have h4 : (first + r + c * 2 ^ k) % 2 ^ k = first + r := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hroom]
  unfold tabBack
  rw [dif_pos (by rw [h3]; exact hc)]
  congr 1
  refine Prod.ext ?_ (Fin.ext h3)
  funext t
  show ((first + r + c * 2 ^ k) % 2 ^ k).testBit t.val = (first + r).testBit t.val
  rw [h4]

/-- Join (ii): the words that a witness's own tables hold are, at a member's entries, the member's
share of the witness. sh: the member's shape; its seat in the stage is by numbers (main rows from
the row oM on, mask rows from oZ on), with room; the statement holds it as the oracle message o; the
layout finds o, not kept, with its blocks beginning at oM and oZ; the layout's numbers of row
variables are the stage's. -/
theorem words_share (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) {s : Sg}
    (σs : Site s (mbOfShape cs sh e0)) (oM oZ : ℕ)
    (hpM : ∀ r, σs.pM r = vtx _ (oM + r.val)) (hpZ : ∀ r, σs.pZ r = vtx _ (oZ + r.val))
    (hrM : oM + sh.mainRows ≤ 2 ^ (s.h + s.g)) (hrZ : oZ + sh.maskRows ≤ 2 ^ s.h)
    (S : Statement) (L : GroupLayout) (o n : ℕ) (x : Oracle) (hx : S.oracles[o]? = some x)
    (hsh : x.shape = sh) (hf : L.find o = some n) (hk : L.kept.getD n false = false)
    (hm : 0 < sh.mainRows → L.mainFirst.getD n none = some oM)
    (hz : 0 < sh.maskRows → L.maskFirst.getD n none = some oZ)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h) (w : s.cIn.J → GE) (j : (portCode cs sh).J) :
    wordsOf S L (tabOf s w) o (partZ cs sh j) (locZ cs sh j) = w (σs.atJ j) := by
  subst hsh
  rcases j with y | y
  · have h0 : 0 < x.shape.mainRows := lt_of_le_of_lt (Nat.zero_le _) y.1.isLt
    have hb : S.rowBits o .main = k1 x.shape := by
      unfold Statement.rowBits
      rw [hx]
      rfl
    have hl : (cMain cs x.shape).l = s.C.l := congrArg Fmt.M1.Code.l (σs.hC y.1)
    have hc : y.2.val < s.C.l := hl ▸ y.2.isLt
    have e1 : ∀ idx, wordsOf S L (tabOf s w) o .main idx =
        (tabOf s w).main (groupIndex idx (S.rowBits o .main) oM L.k) := fun idx => by
      simp only [H2K.ClaimSays.wordsOf, hf, hk, hm h0, Bool.false_eq_true, if_false]
    show wordsOf S L (tabOf s w) o .main (locZ cs x.shape (.inl y)) = _
    rw [e1, hb, hLk]
    show tabBack (s.h + s.g) s.C.l (fun z => w (.inl z))
      (groupIndex (y.1.val + 2 ^ k1 x.shape * y.2.val) (k1 x.shape) oM (s.h + s.g)) = _
    rw [tabBack_group _ _ _ oM y.1.val y.2.val (k1 x.shape)
      (lt_of_lt_of_le y.1.isLt (le_two_pow_ceilLog2 _))
      (lt_of_lt_of_le (Nat.add_lt_add_left y.1.isLt _) hrM) hc]
    show w (.inl (vtx _ (oM + y.1.val), ⟨y.2.val, hc⟩)) = w (.inl (σs.pM y.1, _))
    rw [hpM]
    rfl
  · have h0 : 0 < x.shape.maskRows := lt_of_le_of_lt (Nat.zero_le _) y.1.isLt
    have hb : S.rowBits o .mask = k2 x.shape := by
      unfold Statement.rowBits
      rw [hx]
      rfl
    have hl : (cMask cs x.shape).l = s.Z.l := congrArg Fmt.M1.Code.l (σs.hZ y.1)
    have hc : y.2.val < s.Z.l := hl ▸ y.2.isLt
    have e1 : ∀ idx, wordsOf S L (tabOf s w) o .mask idx =
        (tabOf s w).mask (groupIndex idx (S.rowBits o .mask) oZ L.h) := fun idx => by
      simp only [H2K.ClaimSays.wordsOf, hf, hz h0]
    show wordsOf S L (tabOf s w) o .mask (locZ cs x.shape (.inr y)) = _
    rw [e1, hb, hLh]
    show tabBack s.h s.Z.l (fun z => w (.inr z))
      (groupIndex (y.1.val + 2 ^ k2 x.shape * y.2.val) (k2 x.shape) oZ s.h) = _
    rw [tabBack_group _ _ _ oZ y.1.val y.2.val (k2 x.shape)
      (lt_of_lt_of_le y.1.isLt (le_two_pow_ceilLog2 _))
      (lt_of_lt_of_le (Nat.add_lt_add_left y.1.isLt _) hrZ) hc]
    show w (.inr (vtx _ (oZ + y.1.val), ⟨y.2.val, hc⟩)) = w (.inr (σs.pZ y.1, _))
    rw [hpZ]
    rfl

/-- hS paid: of a witness within e positions of y, whose own words the member's sample row holds
of, the member's share has the sample's answer under the library's sample map. S: the statement
behind the batching; it holds the member as the oracle message o with the shape x.shape; r: the row
that the program makes for it at the seed (Send.form); the seat and the layout as in words_share; y
has blank rows (RowsBlank). -/
theorem answers_of_says {s : Sg} (hs : s.Sized) (e : ℕ) (he : e < s.d) (S : Statement) (G' : Group)
    (L : GroupLayout) (F : LayFacts S G' L) (y : s.cIn.Word) (hy : RowsBlank s S L y) (o n : ℕ)
    (x : Oracle) (hx : S.oracles[o]? = some x) (e0 : ℕ)
    (σs : Site s (mbOfShape S.codes x.shape e0)) (oM oZ : ℕ)
    (hpM : ∀ r, σs.pM r = vtx _ (oM + r.val)) (hpZ : ∀ r, σs.pZ r = vtx _ (oZ + r.val))
    (hrM : oM + x.shape.mainRows ≤ 2 ^ (s.h + s.g)) (hrZ : oZ + x.shape.maskRows ≤ 2 ^ s.h)
    (hf : L.find o = some n) (hk : L.kept.getD n false = false)
    (hm : 0 < x.shape.mainRows → L.mainFirst.getD n none = some oM)
    (hz : 0 < x.shape.maskRows → L.maskFirst.getD n none = some oZ)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h)
    (seed : SampleSeed) (r : Row) (h : Send.form S.codes x.shape o seed 0 = some r)
    (h1 : x.shape.answers = 1) (hc : CaseE x.shape ∨ CaseF x.shape)
    (hzl : seed.z.length = bitsZ S.codes x.shape) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (w : s.cIn.N.Wit) (hn : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e)
    (hS : Says rdE S r (H2K.ClaimSays.wordsOf S L (tabOf s w.1))) :
    (portOmZ S.codes x.shape e0).Z.val (readP (bitsZ S.codes x.shape) seed.z, β)
      (fun j => w.1 (σs.atJ j)) = fun _ => readE r.target := by
  have hP := padded_wordsOf F _ (blank_of_near s hs e he S L y hy w hn)
  have h2 := (says_sample S o x hx seed r h h1 hc hzl β hβ hlM hlZ _ hP).1 hS
  have h3 : (fun j => H2K.ClaimSays.wordsOf S L (tabOf s w.1) o (partZ S.codes x.shape j)
      (locZ S.codes x.shape j)) = fun j => w.1 (σs.atJ j) :=
    funext fun j => words_share S.codes x.shape e0 σs oM oZ hpM hpZ hrM hrZ S L o n x hx rfl hf hk
        hm hz
      hLk hLh w.1 j
  rw [h3] at h2
  exact h2

end H2K.Pin

#print axioms H2K.Pin.words_share
#print axioms H2K.Pin.answers_of_says
