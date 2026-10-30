-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/SevenAt.lean: THE SEVEN CLAUSES UNDER WHICH THE DESCRIPTION'S DECISION AT THE
LINK IS SHOWN TO GIVE "true", AT THIS FOLDER'S TERMS, AT ALL SIZES UNDER `Agree` AND S.P.cut ≤ cut:
two stored strings made of `encAt`'s columns at ONE table of plain entries and two values of the
coins; two tables of coefficients `polysAt`; two typed OOD samples made of them. Definitions,
statements and proofs; general in the sizes.

Why. `Johnson.Prover.Link.link_yes` (Johnson/Prover/Link/LinkJoinF.lean) has one premise, the
relation `Meant` (Johnson/Prover/Link/LinkYesStm.lean): seven clauses between an instance, two
stored strings and two tables of coefficients. The library pays them at its own typed encoder
(`FlashProve.meant_obj`, Johnson/Goal/Conditions/LinkMeant.lean). Here they are paid at the column
of the stand-in committer on byte strings (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean), which is
what `encAt` calls, by three laws on `OnBytes.Slice.honestTab` that `meant_obj` itself spends
(`tab_honest`, `lt_honestTab`, `table_honestTab`), by `same_honest`, on which its fourth rests, and
by the library's law on one sample for each row. Two inputs are spoken of below: the goals' (a
matrix of cells, pads and tails on finite ranges: what the library's typed encoder takes) and the
frame's (functions of two plain numbers: what the frame for an honest prover hands out).

Main names (namespace `Bind.ForProver`).
   `strAt S sh entry ρ`: a stored string: at a position its number and `encAt`'s column there,
      written as words.
   `recAt S Zs sh entry ρ σ`: a typed OOD sample: the seed σ and the sample map's answers at the
      message part of `polysAt`.
   `code_eq`: under `Bind.Column.Agree` the shape's code is the sizes'.
   **`strAt_eq_honestTab`**: under `Agree`: `strAt` is the library's table of code words
      (`honestTab`) at the stand-in committer's own lists: a row's message and a row's tail.
   **`honestPolys_twin`**: under `Agree`: the library's honest polynomials at these lists are
      `polysAt`.
   `val_view`: the sample map, one sample for each row, on the message part of M is the one row's
      sum: OF EVERY M.
   `recAt_msgK`: under `Agree`: the answers of `recAt` are the sample map's at `msgK`
      (Johnson/Bind/ForProver/RecRows.lean).
   **`seven_at_ours`**: THE SEVEN, a conjunction in the order of `meant_obj`: rec0, rec1, tab0,
      tab1, same, words, wide.
Limits. NO MAP OF THE TIE BETWEEN THE FRAME'S INPUT AND THE GOALS' IS NAMED: no `cellsOfF`, no
`qOf`, no matrix, no premise that a matrix fits; the three protocols and their provers, which are
letters of `meant_obj`, are not read. THE PLAIN ENTRIES ARE A LETTER: any function of two numbers
into the words, an index's packing or not, below the prime or not. THE SAMPLE MAP Zs IS A LETTER:
any sample map on the sizes' entries; no premise ties it to the shape's s or to `recZ`; at the full
size `meant_ours` lays `frZ`. `strAt` and `recAt` take the sizes S and the shape sh apart, as
`polysAt` does. In `strAt` and `polysAt` S gives the types and sh the text. `recAt`'s text names S
as well: `(S.ixR Zs).ZR.val` and `(S.ixR Zs).view`, and that view reads the message part from the
sizes' r on (`pl`, OnBytes/Slice/LinkAt.lean), while the coefficients branch at sh's r. That the two
agree is the premise `Agree` of the laws. THE FIRST TWO CLAUSES HOLD OF EVERY M, BY `recAt`'S
DEFINITION AND `val_view`: they say nothing on `polysAt`. What gives them content is what `recAt`
is: `recAt_msgK` here. The third and fourth clause say that a column of the stand-in committer is,
row by row, the generator matrix's value at `polysAt`; the fifth that the two tables agree before
the library's cut, which is so because ONE table of plain entries is laid under both coins: BY THE
STATEMENT'S FORM. The sixth holds of whatever `encAt` gives, by `strAt`'s text; that the words are
the committer's own is `words_columnOf` (Johnson/Bind/ForProver/Laws.lean). The seventh is a fact on
`encAt`. The position's number is read by none of the seven. THE SEVEN TIE THESE TERMS TO EACH OTHER
ALONE: three terms that read no plain entry (columns of 0, coefficients 0, answers 0) would meet
them all. That the terms read the plain entries is said by `strAt_eq_honestTab` here and
`strAt_readers` (Johnson/Bind/ForProver/SevenReaders.lean), not by `seven_at_ours`. TWO TABLES STAND
SIDE BY SIDE, AND ALL FOUR OF ρ, σ, ρ', σ' ARE BARE LETTERS: (ρ, σ) stand where the link reads the
committed table (its item 0), (ρ', σ') where it reads a second table (its item 1). That ρ, σ are the
coins and the seed of the run that makes the commitment ID (its salts, tree, root and name; σ
sampled at that name), and that ρ', σ' are a copy's own, sampled apart, with a copy's tree, name and
root: NEITHER is said here. Nothing here says that each table's randomness has one seed, that the
two tables' randomness is sampled apart, or that the second table's is the one at which a session
runs. `Agree` and S.P.cut ≤ cut are premises; at the full size they are theorems without premises
(`Bind.Column.agree_full`, Johnson/Bind/ColumnSizes.lean; `OnBytes.Slice.fr_cut`,
OnBytes/Slice/FullRecSz.lean), and `meant_ours` (Johnson/Bind/ForProver/MeantOurs.lean) spends them:
so the premises are met there. Under `Agree` and the premise that the matrix's cells fit a row's
message before the pads: at the plain readers of any input of the goals' type the three terms are
the library's own encoding, sample and polynomials at that input
(Johnson/Bind/ForProver/SevenReaders.lean, Johnson/Bind/ForProver/PolysReaders.lean); beside it, at
the packing of a matrix they are the library's own at an input that is made of the frame's by two
definitions (Johnson/Bind/ForProver/SevenTied.lean). Nothing on the link's decision here. No hash
function, no query, no coin's law. This file writes no honest prover. Nothing on completeness, on
index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Polys

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (Sz GF GE toF ofF honestPolys honestMsgs honestTab)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape message tailOf)
open Bind.Column (Agree)
open _root_.Run.PQ (SgX)
open _root_.Iop (twoExternalStrings)
open VerifiableInference.Desc (fieldPrimeWord)

/-! ## The terms -/

/-- **A stored string made of `encAt`'s columns**: at a position its number and the column there,
written as words; no word where `encAt` gives nothing. -/
def strAt (S : Sz) (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) : S.Pos → SgX :=
  fun x => (x.val, ((encAt sh entry ρ x.val).getD []).map ofF)

/-- **A typed OOD sample made of `polysAt`**: the seed, and the sample map's answers, one sample for
each row, at the message part of `polysAt`. -/
def recAt (S : Sz) (Zs : Cb.Ood.Sample GE S.En) (sh : Shape) (entry : ℕ → ℕ → UInt64)
    (ρ : TableRand) (σ : Zs.D) : (S.ixR Zs).Rec :=
  (σ, (S.ixR Zs).ZR.val σ ((S.ixR Zs).view (polysAt S sh entry ρ)))

/-! ## The stand-in committer's lists under the library's honest table -/

section
variable {S : Sz} {sh : Shape} {cut : ℕ}

/-- Under `Agree` the shape's code is the sizes'. -/
theorem code_eq (h : Agree sh S cut) : sh.code = S.P.T := by
  have e : (⟨sh.a, sh.l, sh.r⟩ : Fmt.M1.Code) = ⟨S.P.T.a, S.P.T.l, S.P.T.r⟩ := by
    rw [h.a, h.l, h.r]
  exact e

/-- **The stored string is the library's table of code words at the committer's own lists.** -/
theorem strAt_eq_honestTab (h : Agree sh S cut) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) :
    strAt S sh entry ρ =
      honestTab S (message sh (tableOfRand entry ρ)) (tailOf sh (tableOfRand entry ρ)) := by
  funext x
  have hx : x.val < 2 ^ sh.a := by
    rw [h.a]
    exact x.isLt
  unfold strAt encAt
  rw [if_pos hx, Option.getD_some, words_columnOf, Bind.Twin.columnOf_laid, code_eq h]
  show (x.val, (List.range (2 ^ sh.v)).map fun b =>
      Fmt.M1.symF S.P.T x.val (message sh (tableOfRand entry ρ) b)
        (tailOf sh (tableOfRand entry ρ) b)) =
    (x.val, (List.range (2 ^ S.P.v)).map fun b =>
      Fmt.M1.symF S.P.T x.val (message sh (tableOfRand entry ρ) b)
        (tailOf sh (tableOfRand entry ρ) b))
  rw [h.v]

/-- **The library's honest polynomials at the committer's own lists are `polysAt`.** -/
theorem honestPolys_twin (h : Agree sh S cut) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) :
    honestPolys S (message sh (tableOfRand entry ρ)) (tailOf sh (tableOfRand entry ρ)) =
      polysAt S sh entry ρ := by
  funext β k
  show honestPolys S (message sh (tableOfRand entry ρ)) (tailOf sh (tableOfRand entry ρ)) β k =
    algebraMap GF GE (rowCoefF sh entry ρ (Sz.rowNo β) k.val)
  by_cases hk : k.val < S.P.T.r
  · have hk' : k.val < sh.r := by
      rw [h.r]
      exact hk
    rw [polys_below S _ _ β k hk, toF_tailOf sh entry ρ _ _ hk', rowCoefF_tail sh entry ρ _ _ hk']
  · have hj : k.val - S.P.T.r < S.P.T.l := by
      have h5 := k.isLt
      omega
    have hj' : k.val - S.P.T.r < sh.l := by
      rw [h.l]
      exact hj
    have e1 : rowCoefF sh entry ρ (Sz.rowNo β) k.val =
        rowMsgF sh entry ρ (Sz.rowNo β) (k.val - S.P.T.r) := by
      unfold rowCoefF
      rw [h.r, if_neg hk]
    rw [polys_from S _ _ β k hk hj, e1]
    show algebraMap GF GE
      (toF ((message sh (tableOfRand entry ρ) (Sz.rowNo β)).getD (k.val - S.P.T.r) 0)) = _
    rw [toF_message sh entry ρ _ _ hj']

end

/-! ## The sample -/

/-- **Of every table of coefficients M**: the sample map, one sample for each row, on the message
part of M is the one row's sum. The library's law on "one sample for each row". -/
theorem val_view (S : Sz) (Zs : Cb.Ood.Sample GE S.En) (M : (S.ixR Zs).Row → S.Co → GE)
    (σ : Zs.D) (β : (S.ixR Zs).Row) (s : Zs.S) :
    (S.ixR Zs).ZR.val σ ((S.ixR Zs).view M) (β, s) =
      ∑ j, Zs.mat σ s j * M β ((S.ixR Zs).pl j) :=
  Cb.ood_val_rows_same GE S.En (Fin S.P.v → Bool) Zs σ ((S.ixR Zs).view M) β s

/-- **Under `Agree` the answers of `recAt` are the sample map's at the rows' messages.** -/
theorem recAt_msgK {S : Sz} (Zs : Cb.Ood.Sample GE S.En) {sh : Shape} {cut : ℕ}
    (h : Agree sh S cut) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (σ : Zs.D) :
    (recAt S Zs sh entry ρ σ).2 =
      (S.ixR Zs).ZR.val σ fun n => msgK sh entry ρ (Sz.rowNo n.1) n.2.val := by
  have e : (S.ixR Zs).view (polysAt S sh entry ρ) =
      fun n => msgK sh entry ρ (Sz.rowNo n.1) n.2.val :=
    funext fun n => view_polysAt S h entry ρ n
  show (S.ixR Zs).ZR.val σ ((S.ixR Zs).view (polysAt S sh entry ρ)) = _
  rw [e]

/-! ## The seven -/

/-- **THE SEVEN, at this folder's terms, at all sizes**: at one table of plain entries, two values
of the coins and two seeds. Under `Agree sh S cut` and S.P.cut ≤ cut. In the order rec0, rec1, tab0,
tab1, same, words, wide. The first two hold of every table of coefficients, by `recAt`'s definition.
No map between two inputs is named. -/
theorem seven_at_ours {S : Sz} (Zs : Cb.Ood.Sample GE S.En) {sh : Shape} {cut : ℕ}
    (h : Agree sh S cut) (hc : S.P.cut ≤ cut) (entry : ℕ → ℕ → UInt64) (ρ ρ' : TableRand)
    (σ σ' : Zs.D) :
    (∀ β s, (recAt S Zs sh entry ρ σ).2 (β, s) =
      ∑ j, Zs.mat (recAt S Zs sh entry ρ σ).1 s j * polysAt S sh entry ρ β ((S.ixR Zs).pl j)) ∧
    (∀ β s, (recAt S Zs sh entry ρ' σ').2 (β, s) =
      ∑ j, Zs.mat (recAt S Zs sh entry ρ' σ').1 s j *
        polysAt S sh entry ρ' β ((S.ixR Zs).pl j)) ∧
    ((S.lkR Zs).tab (strAt S sh entry ρ) =
      fun β => (S.ixR Zs).G.mulVec (polysAt S sh entry ρ β)) ∧
    ((S.lkR Zs).tab (strAt S sh entry ρ') =
      fun β => (S.ixR Zs).G.mulVec (polysAt S sh entry ρ' β)) ∧
    (S.lwR Zs).SameOn ((S.ixR Zs).view (polysAt S sh entry ρ))
      ((S.ixR Zs).view (polysAt S sh entry ρ')) ∧
    (∀ p, (((twoExternalStrings (2 ^ S.P.T.a) SgX).rd (strAt S sh entry ρ, strAt S sh entry ρ') p).2.all
      (· < fieldPrimeWord)) = true) ∧
    (∀ (b : Bool) (x : ℕ) (hx : x < 2 ^ S.P.T.a),
      ((twoExternalStrings (2 ^ S.P.T.a) SgX).rd (strAt S sh entry ρ, strAt S sh entry ρ')
        (if b then .inr ⟨x, hx⟩ else .inl ⟨x, hx⟩)).2.length = 2 ^ S.P.v) := by
  have hcut : cut + 3 * sh.s = sh.l := h.cut
  have hp : sh.plain = cut := by
    show sh.l - 3 * sh.s = cut
    omega
  have t0 := Johnson.Prover.Link.tab_honest S Zs (message sh (tableOfRand entry ρ))
    (tailOf sh (tableOfRand entry ρ))
  have t1 := Johnson.Prover.Link.tab_honest S Zs (message sh (tableOfRand entry ρ'))
    (tailOf sh (tableOfRand entry ρ'))
  have sm := Johnson.Prover.Link.same_honest S Zs (message sh (tableOfRand entry ρ))
    (tailOf sh (tableOfRand entry ρ)) (message sh (tableOfRand entry ρ'))
    (tailOf sh (tableOfRand entry ρ')) fun r e he => by
      have h1 : e < sh.plain := by
        rw [hp]
        exact lt_of_lt_of_le he hc
      have h2 : e < sh.l := lt_of_lt_of_le h1 (Nat.sub_le _ _)
      rw [toF_message sh entry ρ _ _ h2, toF_message sh entry ρ' _ _ h2]
      unfold rowMsgF
      rw [if_pos h1, if_pos h1]
  rw [← strAt_eq_honestTab h entry ρ, honestPolys_twin h entry ρ] at t0
  rw [← strAt_eq_honestTab h entry ρ', honestPolys_twin h entry ρ'] at t1
  rw [honestPolys_twin h entry ρ, honestPolys_twin h entry ρ'] at sm
  refine ⟨fun β s => val_view S Zs _ σ β s, fun β s => val_view S Zs _ σ' β s, t0, t1, sm,
    fun p => ?_, fun b x hx => ?_⟩
  · rw [strAt_eq_honestTab h entry ρ, strAt_eq_honestTab h entry ρ']
    cases p with
    | inl x => exact Johnson.Prover.Link.lt_honestTab S _ _ x
    | inr x => exact Johnson.Prover.Link.lt_honestTab S _ _ x
  · rw [strAt_eq_honestTab h entry ρ, strAt_eq_honestTab h entry ρ']
    cases b
    · exact (Johnson.Prover.At.table_honestTab S _ _ ⟨x, hx⟩).2.2
    · exact (Johnson.Prover.At.table_honestTab S _ _ ⟨x, hx⟩).2.2

end Bind.ForProver

end

#print axioms Bind.ForProver.code_eq
#print axioms Bind.ForProver.strAt_eq_honestTab
#print axioms Bind.ForProver.honestPolys_twin
#print axioms Bind.ForProver.val_view
#print axioms Bind.ForProver.recAt_msgK
#print axioms Bind.ForProver.seven_at_ours
#print axioms Bind.ForProver.strAt
#print axioms Bind.ForProver.recAt
