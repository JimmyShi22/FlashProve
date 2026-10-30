-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SaysSample.lean: the row that `Send.form` returns for an oracle message's
sample says its claim of words just if the message that the words hold there has the sample's answer
under the library's sample map. Statements and proofs.

Two limits come first. (a) The row is the one that `Send.form` returns: its target is the default 0.
The verifier's record holds { row with target := the answer }. So `says_sample`, true as typed, can
be called at no record's row whose answer is not 0: for the record's row see `says_sample_t`
(Johnson/Desc/K12/Law/SampleAt.lean) and `says_sample_ge` (Johnson/Desc/K12/Law/FormTake.lean).
`value_sample` stands (a row's value reads no target). (b) The premise on the seed's point is an
equality of lengths: by the program's own text a real seed's point is as long as the largest cube of
its round, so at a round that sends messages with cubes of two sizes it is false at the smaller;
`form_take` and `says_sample_ge` (Johnson/Desc/K12/Law/FormTake.lean) have the form with "at most".
`Says` is that of Johnson/Desc/Means/Says.lean; the sample map is `portZ` (Johnson/Pack/PortZ.lean).
There is no new mathematics: sums re-indexed, and `form_portZ`
(Johnson/Desc/K12/Law/FormPortZE.lean) coefficient by coefficient.
Main names:
  `sum_tab`: a table of 2^k rows and l = 2^e places whose entries vanish on the rows from R on,
    summed index by index, is summed over the R real rows and the places.
  `onTable_entries`: one table of the words under a row (`onTable`, Johnson/Desc/Means/Says.lean) is
    the sum over the message's entries of that table: from `Padded` (the words are 0 beyond the real
    rows) and "the code's message length is a power of two".
  `onTable_other`: the sample row of the message o reads no other message (the library's
    `coefAt_form_other`).
  `value_sample`: value rdE S row m = (portZ S.codes x.shape).val (the seed's point read, β) (fun j
    => m o (j's table) (j's index)) ().
  `says_sample`: `Says rdE S row m` holds just where that answer is the row's target, read.
Premises: the statement holds the message o with the shape x.shape; row is that of `Send.form` at
S.codes, that shape, o, the seed and answer number 0; one answer; `CaseE ∨ CaseF` (what the
library's `MeetsAt` asks); the seed's point has as many coordinates as the cube has bits; β a unit
whose value is the seed's factor, read; each code of which the shape has rows has a message length
that is a power of two (every run tests it of a statement's codes: `powerOfTwo`); `Padded S m`.
With Johnson/Desc/K12/Law/TabWords.lean (`Padded` comes from the code) and
Johnson/Desc/K12/Law/ShareNear.lean (the premise ha of `decs_of_group`): where all the batched rows
hold of a near witness's own words, each sampled member's share has its sample's answer.
Limits: that join is not typed here. It wants (i) that the member's sample row stands among the rows
that the batching takes, with the sample's seed and answer as the record holds them; (ii) that "m o
(partZ j) (locZ j)" at m := wordsOf S' L (tabOf s w.1) is the member's share "w.1 ((seat i).atJ j)"
(`groupIndex` against the vertices of `Site.byNo`); (iii) the two groups (limit (1) of
Johnson/Desc/K12/Law/ShareNear.lean). No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `coefAt_form_other`
(OnBytes/Slice/BlkSend.lean), `le_two_pow_ceilLog2` (OnBytes/Slice/ProgCodes.lean), `sum_rowNo`
(OnBytes/Slice/Cells.lean); `sum_table` (Johnson/Desc/K12/Law/ClaimSays.lean), `form_portZ`
(Johnson/Desc/K12/Law/FormPortZE.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.FormPortZE
import Johnson.Desc.K12.Law.ClaimSays

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Slice Cb Cb.Ood Johnson.Pack
open OnBytes.Means H2K.ClaimSays

/-- A table of 2^k rows and l = 2^e places whose entries vanish on the rows from R on, summed index
by index, is summed over the R real rows and the places. -/
theorem sum_tab {M : Type} [AddCommMonoid M] (k e l R : ℕ) (hl : 2 ^ e = l) (hR : R ≤ 2 ^ k) (f : ℕ
    → M)
    (h0 : ∀ r c, R ≤ r → r < 2 ^ k → f (r + 2 ^ k * c) = 0) :
    ∑ J ∈ Finset.range (2 ^ (k + e)), f J = ∑ x : Fin R × Fin l, f (x.1.val + 2 ^ k * x.2.val) := by
  rw [sum_table k e l hl f, Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sum_rowNo k (fun r => f (r + 2 ^ k * y.val))]
  show _ = ∑ x : Fin R, f (x.val + 2 ^ k * y.val)
  rw [Fin.sum_univ_eq_sum_range (fun r => f (r + 2 ^ k * y.val)) R]
  refine (Finset.sum_subset (Finset.range_subset_range.2 hR) fun r hr hn => ?_).symm
  exact h0 r y.val (Nat.le_of_not_lt fun q => hn (Finset.mem_range.2 q)) (Finset.mem_range.1 hr)

/-- One table of the words under the sample row: the sum over the table's indices is the sum over
the message's entries of that table. rows, ell: the shape's rows of that kind and the code's message
length. -/
theorem onTable_entries (S : Statement) (row : Row) (m : Words GE) (o : Nat) (part : Part) (R ell :
    ℕ)
    (hR : realRows S o part = R) (hb : S.rowBits o part = ceilLog2 R)
    (hp : 0 < R → S.placeBits o part = ceilLog2 ell) (hh : S.has o part = decide (0 < R))
    (hl : 0 < R → 2 ^ ceilLog2 ell = ell) (hP : Padded S m) :
    onTable rdE S row m o part =
      ∑ x : Fin R × Fin ell, coefAt row o part (x.1.val + 2 ^ ceilLog2 R * x.2.val) *
        m o part (x.1.val + 2 ^ ceilLog2 R * x.2.val) := by
  unfold onTable tableSize
  rw [hh]
  by_cases h0 : 0 < R
  · rw [if_pos (by simpa using h0)]
    unfold Statement.tableBits
    rw [hb, hp h0]
    refine sum_tab (ceilLog2 R) (ceilLog2 ell) ell R (hl h0) (le_two_pow_ceilLog2 R)
      (fun i => rdE.val (row.coefficient o part i) * m o part i) fun r c h1 h2 => ?_
    have : m o part (r + 2 ^ ceilLog2 R * c) = 0 := by
      apply hP
      rw [hR, hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
      exact h1
    show _ * m o part (r + 2 ^ ceilLog2 R * c) = 0
    rw [this, mul_zero]
  · rw [if_neg (by simpa using h0)]
    have hz : R = 0 := by omega
    subst hz
    simp

theorem onTable_other (S : Statement) (cs : Codes) (sh : OracleShape) (o : ℕ) (seed : SampleSeed)
    (row : Row)
    (h : Send.form cs sh o seed 0 = some row) (m : Words GE) (o' : ℕ) (ho : o' ≠ o) (part : Part) :
    onTable rdE S row m o' part = 0 := by
  unfold onTable
  refine Finset.sum_eq_zero fun i _ => ?_
  have : rdE.val (row.coefficient o' part i) = 0 := coefAt_form_other cs sh o seed 0 row h o' ho
      part i
  rw [this, zero_mul]

/-- The sample row's value on words is the library's sample map's answer. S: a statement that
holds the oracle message number o with the shape x.shape; row: the row that the program makes for it
at the seed (Send.form); m: words that are 0 beyond the real rows. Then the row's value on the words
("value") is (portZ …).val at the seed read, of the message that the words hold at
o's entries. -/
theorem value_sample (S : Statement) (o : ℕ) (x : Oracle) (hx : S.oracles[o]? = some x)
    (seed : SampleSeed) (row : Row) (h : Send.form S.codes x.shape o seed 0 = some row)
    (h1 : x.shape.answers = 1) (hc : CaseE x.shape ∨ CaseF x.shape)
    (hz : seed.z.length = bitsZ S.codes x.shape) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (m : Words GE) (hP : Padded S m) :
    value rdE S row m =
      (portZ S.codes x.shape).val (readP (bitsZ S.codes x.shape) seed.z, β)
        (fun j => m o (partZ S.codes x.shape j) (locZ S.codes x.shape j)) () := by
  have ho : o < S.oracles.size := by
    rcases Nat.lt_or_ge o S.oracles.size with q | q
    · exact q
    · rw [Array.getElem?_eq_none q] at hx
      cases hx
  unfold value
  rw [Finset.sum_eq_single o
    (fun o' _ hne => by
      rw [onTable_other S _ _ o seed row h m o' hne, onTable_other S _ _ o seed row h m o' hne,
          add_zero])
    (fun hn => absurd (Finset.mem_range.2 ho) hn)]
  rw [onTable_entries S row m o .main x.shape.mainRows (pMain S.codes x.shape).ell
      (by unfold realRows; rw [hx]; rfl) (by unfold Statement.rowBits; rw [hx]; rfl)
      (fun h0 => by
        unfold Statement.placeBits
        rw [hx]
        show (if (x.shape.mainRows == 0) = true then 0 else _) = _
        rw [if_neg (by simpa using Nat.pos_iff_ne_zero.1 h0)]
        rfl)
      (by unfold Statement.has; rw [hx]; rfl) hlM hP,
    onTable_entries S row m o .mask x.shape.maskRows (pMask S.codes x.shape).ell
      (by unfold realRows; rw [hx]; rfl) (by unfold Statement.rowBits; rw [hx]; rfl)
      (fun h0 => by
        unfold Statement.placeBits
        rw [hx]
        show (if (x.shape.maskRows == 0) = true then 0 else _) = _
        rw [if_neg (by simpa using Nat.pos_iff_ne_zero.1 h0)]
        rfl)
      (by unfold Statement.has; rw [hx]; rfl) hlZ hP]
  unfold Sample.val
  rw [Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [← form_portZ S.codes x.shape o seed row h h1 hc hz β hβ (.inl y)]
    rfl
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [← form_portZ S.codes x.shape o seed row h h1 hc hz β hβ (.inr y)]
    rfl

/-- (β) the answers: the sample row says its claim of the words just if the message that the
words hold at o has the answer that the row's target reads, at the seed. -/
theorem says_sample (S : Statement) (o : ℕ) (x : Oracle) (hx : S.oracles[o]? = some x)
    (seed : SampleSeed) (row : Row) (h : Send.form S.codes x.shape o seed 0 = some row)
    (h1 : x.shape.answers = 1) (hc : CaseE x.shape ∨ CaseF x.shape)
    (hz : seed.z.length = bitsZ S.codes x.shape) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (m : Words GE) (hP : Padded S m) :
    Says rdE S row m ↔
      (portZ S.codes x.shape).val (readP (bitsZ S.codes x.shape) seed.z, β)
        (fun j => m o (partZ S.codes x.shape j) (locZ S.codes x.shape j)) = fun _ => readE
            row.target := by
  unfold Says
  rw [value_sample S o x hx seed row h h1 hc hz β hβ hlM hlZ m hP]
  constructor
  · intro e
    funext u
    cases u
    exact e
  · intro e
    exact congrFun e ()

end H2K.Pin

#print axioms H2K.Pin.value_sample
#print axioms H2K.Pin.says_sample
