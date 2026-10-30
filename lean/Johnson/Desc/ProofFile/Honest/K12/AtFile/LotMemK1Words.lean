-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotMemK1Words.lean: the words that a proximity test's job
makes of its own rows at a member which is a message of a sending of the kind K1 (`memK1`,
K12/AtProof/JobW.lean) are that sending's rows (`K1.rowsR`, Honest/K1/Coins.lean), read as a table
(`Rows.word`, Johnson/Prover/Send/Core.lean). The twin of `wordsAt_member`
(K12/WordsOfMember.lean), which speaks of a member made by `memOfSending`. General in the job, the
sending, the place, the statement and the file.

  `lst_tabG_inside`, `lst_tabG_beyond`   a table of lists, read: inside its entry, beyond a row's end 0
  `EndsAtCodeLengths`   rows that are 0 from their code's message length on, by name
  `rowsR_ends_at_code_lengths`   `K1.rowsR`'s rows are such, at every data and every purse
  `wordsAt_of_laid_rows`   at a member whose lists are `psOfRows` of such rows V: `wordsAt` is V.word
  `wordsAt_of_first_kind_member`   THE TWIN: at a member `memK1 J lift at_ k fs`
  `wordsAt_of_first_kind_member_at_purse`   the same at a sender's own purse c and data d, where the
      purse agrees with the member's stretch on the message's own coins (`rowsR_csAt`) and the job's
      data at the test's front is d
  `wordsAt_of_first_kind_member_held`   the same as the library's held words (`held`, Core.lean) at
      the message's number first + k

By what. `getD_range`, `lst_range` (K12/RunByTab.lean), `rowBits_shape` (K12/PubNear.lean),
`clog_eq`, `held_new` (Johnson/Prover/Send/Held.lean), `rowsR_csAt` (K12/AtProof/JobW.lean).

Hypotheses. hn: the job's member number n is that `memK1`. hf: the layout finds the message o at n.
hy, hsh: the statement holds at o a message of the sending's shape at k. No more: NO BOUND ON THE
INDEX and no premise on codes: both sides are 0 from the code's message length on and on the rows
from the real ones on.

Limits.
- The right side still reads the job's data AT THE TEST's FRONT, whole, and the member's stretch of
  the coins lent to the test. That the data is what the sender had at its own front, and that the
  stretch holds the sender's coins, are premises of the second law (hd, hcf, hce) and are paid
  nowhere here.
- hf, hy, hsh are a caller's, at a state on entry.
- No run, no book, no thread is named. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K12.ManyFits
import Johnson.Desc.ProofFile.Honest.K12.PubNear
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import Johnson.Desc.K12.Honest.LaidState
import Johnson.Prover.Send.Held

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes (Statement GroupLayout Oracle OracleShape ceilLog2)
open OnBytes.Slice (GE GF ofE toE lst)
open OnBytes.Means (realRows Words)
open Johnson.Prover.Send (Rows shapeAt held)
open ProofFile.Honest (Addr Front Cs Due)
open ProofFile.Honest.K12 (TestCoins Stretch)
open ProofFile.Honest.K12.Light (ManyJob memRows plainMany)
open ProofFile.Honest.K12.AtProof (tabG psOfRows memK1 csAt)

/-- A table of lists, read inside: its entry. -/
theorem lst_tabG_inside (r n : ℕ) (f : ℕ → ℕ → GE) (i j : ℕ) (hi : i < r) (hj : j < n) :
    lst ((tabG r n f).getD i []) j = f i j := by
  unfold tabG
  rw [ProofFile.Honest.K12.Light.getD_range r _ _ i hi, ProofFile.Honest.K12.Light.lst_range n _ j hj]
  exact OnBytes.Slice.toE_ofE _

/-- A table of lists, read beyond a row's end: 0, at every row. -/
theorem lst_tabG_beyond (r n : ℕ) (f : ℕ → ℕ → GE) (i j : ℕ) (hj : n ≤ j) :
    lst ((tabG r n f).getD i []) j = 0 := by
  by_cases hi : i < r
  · unfold tabG
    rw [ProofFile.Honest.K12.Light.getD_range r _ _ i hi]
    unfold lst
    rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; exact hj)]
    exact OnBytes.Slice.lst_nil 0
  · have e : (tabG r n f).getD i [] = [] :=
      List.getD_eq_default _ _ (by
        unfold tabG
        rw [List.length_map, List.length_range]
        exact Nat.le_of_not_lt hi)
    rw [e]
    exact OnBytes.Slice.lst_nil j

/-- **Rows that end at their codes' message lengths**: message number k's rows V are 0 at every
place from the row's code's message length on, in the main table and in the mask table: what
`Rows`' own head asks of a caller (Johnson/Prover/Send/Core.lean). -/
structure EndsAtCodeLengths (P : VerifiableInference.Desc.K1.Par) (k : ℕ) (V : Rows) : Prop where
  main : ∀ r j, (P.codes.base.getD (shapeAt P k).code default).ell ≤ j →
    V.main ((shapeAt P k).mainDeg == 3) r j = 0
  mask : ∀ r j, (P.codes.mask.getD (shapeAt P k).maskCode default).ell ≤ j → V.mask r j = 0

/-- **`K1.rowsR`'s rows end at their codes' message lengths**, at every data and every purse. -/
theorem rowsR_ends_at_code_lengths (P : VerifiableInference.Desc.K1.Par)
    (ride : ℕ → Option K1.Ride) (data : ℕ → ℕ → ℕ → Option (GF ⊕ GE))
    (c : Cs (K1.dueR P ride)) (k : ℕ) : EndsAtCodeLengths P k (K1.rowsR P ride data c k) := by
  refine ⟨fun r j h => ?_, fun r j h => ?_⟩
  · unfold Johnson.Prover.Send.Rows.main
    have eE : (K1.rowsR P ride data c k).mainE r j = 0 := by
      show (if (_ || _ || decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j)) = true
        then (0 : GE) else _) = 0
      rw [decide_eq_true h, Bool.or_true, if_pos rfl]
    have eF : (K1.rowsR P ride data c k).mainF r j = 0 := by
      show (if (_ || _ || decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j)) = true
        then (0 : GF) else _) = 0
      rw [decide_eq_true h, Bool.or_true, if_pos rfl]
    rw [eE, eF, map_zero, ite_self]
  · have hn : ¬ (r < (shapeAt P k).maskRows ∧
        j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :=
      fun x => absurd x.2 (Nat.not_lt.2 h)
    show (match ride k with
      | some R => if r < (shapeAt P k).maskRows ∧
          j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell then _ else (0 : GE)
      | none => if r < (shapeAt P k).maskRows ∧
          j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell then _ else (0 : GE)) = 0
    split <;> exact if_neg hn

/-- **At a member whose lists are `psOfRows` of rows V that end at their codes' lengths, the words
that the job's own rows make are V's two tables by index.** At every index. -/
theorem wordsAt_of_laid_rows {W X : Type} (P : VerifiableInference.Desc.K1.Par) (k : ℕ) (V : Rows)
    (hV : EndsAtCodeLengths P k V) (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) (n : ℕ)
    (hr : memRows A w fr C n = psOfRows P k V) (S : Statement) (L : GroupLayout) (o : ℕ)
    (hf : L.find o = some n) (y : Oracle) (hy : S.oracles[o]? = some y)
    (hsh : y.shape = shapeAt P k) (pt : OnBytes.Part) (i : ℕ) :
    ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) o pt i = V.word (shapeAt P k) pt i := by
  have hg : (S.oracles.getD o default) = y := by
    rw [Array.getD_eq_getD_getElem?, hy]
    rfl
  have hrb : ∀ p, S.rowBits o p = ceilLog2 ((shapeAt P k).rows p) := fun p => by
    rw [ProofFile.Honest.K12.Light.rowBits_shape, hg, hsh]
  have hrr : ∀ p, realRows S o p = (shapeAt P k).rows p := fun p => by
    unfold realRows
    rw [hy]
    show y.shape.rows p = _
    rw [hsh]
  unfold ProofFile.Honest.K12.wordsAt
  rw [hf]
  cases pt with
  | main =>
    show (if i % 2 ^ S.rowBits o .main < realRows S o .main then
      lst ((memRows A w fr C n).M.getD (i % 2 ^ S.rowBits o .main) []) (i / 2 ^ S.rowBits o .main)
      else 0) = (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then
        V.main ((shapeAt P k).mainDeg == 3) (i % 2 ^ ceilLog2 (shapeAt P k).mainRows)
          (i / 2 ^ ceilLog2 (shapeAt P k).mainRows) else 0)
    rw [hrb, hrr, hr]
    show (if i % 2 ^ ceilLog2 (shapeAt P k).mainRows < (shapeAt P k).mainRows then
      lst ((tabG (shapeAt P k).mainRows (P.codes.base.getD (shapeAt P k).code default).ell
        (V.main ((shapeAt P k).mainDeg == 3))).getD (i % 2 ^ ceilLog2 (shapeAt P k).mainRows) [])
        (i / 2 ^ ceilLog2 (shapeAt P k).mainRows) else 0) = _
    split
    · rename_i hlt
      by_cases hj : i / 2 ^ ceilLog2 (shapeAt P k).mainRows <
          (P.codes.base.getD (shapeAt P k).code default).ell
      · exact lst_tabG_inside _ _ _ _ _ hlt hj
      · rw [lst_tabG_beyond _ _ _ _ _ (Nat.le_of_not_lt hj), hV.main _ _ (Nat.le_of_not_lt hj)]
    · rfl
  | mask =>
    show (if i % 2 ^ S.rowBits o .mask < realRows S o .mask then
      lst ((memRows A w fr C n).W.getD (i % 2 ^ S.rowBits o .mask) []) (i / 2 ^ S.rowBits o .mask)
      else 0) = (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then
        V.mask (i % 2 ^ ceilLog2 (shapeAt P k).maskRows)
          (i / 2 ^ ceilLog2 (shapeAt P k).maskRows) else 0)
    rw [hrb, hrr, hr]
    show (if i % 2 ^ ceilLog2 (shapeAt P k).maskRows < (shapeAt P k).maskRows then
      lst ((tabG (shapeAt P k).maskRows (P.codes.mask.getD (shapeAt P k).maskCode default).ell
        V.mask).getD (i % 2 ^ ceilLog2 (shapeAt P k).maskRows) [])
        (i / 2 ^ ceilLog2 (shapeAt P k).maskRows) else 0) = _
    split
    · rename_i hlt
      by_cases hj : i / 2 ^ ceilLog2 (shapeAt P k).maskRows <
          (P.codes.mask.getD (shapeAt P k).maskCode default).ell
      · exact lst_tabG_inside _ _ _ _ _ hlt hj
      · rw [lst_tabG_beyond _ _ _ _ _ (Nat.le_of_not_lt hj), hV.mask _ _ (Nat.le_of_not_lt hj)]
    · rfl

/-- **THE TWIN OF `wordsAt_member` AT A MEMBER OF THE FIRST KIND.** A: a job on several members, whose
member number n is message number k of the K1 sending J (`memK1`). Where the layout finds the
message o at n and the statement holds at o a message of that shape: at both tables and EVERY index,
the words that the job's own rows make are the two tables, by index, of `K1.rowsR`'s rows at the
job's data at the test's front and at the member's stretch of the test's coins, laid from the
message's start on. -/
theorem wordsAt_of_first_kind_member {Wd W X : Type} (J : K1.SendJob Wd X) (lift : W → Wd)
    (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ) (A : ManyJob W X) (n : ℕ)
    (hn : A.mems[n]? = some (memK1 J lift at_ k fs)) (w : W) (fr : Front X) (C : TestCoins)
    (S : Statement) (L : GroupLayout) (o : ℕ) (hf : L.find o = some n) (y : Oracle)
    (hy : S.oracles[o]? = some y) (hsh : y.shape = shapeAt J.P k) (pt : OnBytes.Part) (i : ℕ) :
    ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) o pt i =
      (K1.rowsR J.P J.ride (J.data (lift w) fr)
        (csAt _ (K1.startR J.P J.ride k) (C.mem n)) k).word (shapeAt J.P k) pt i := by
  refine wordsAt_of_laid_rows J.P k _ (rowsR_ends_at_code_lengths _ _ _ _ _) A w fr C n ?_ S L o hf
    y hy hsh pt i
  unfold memRows
  rw [hn]
  rfl

/-- **The same at a sender's own purse and data.** c: a purse of the sending's whole count that
agrees with the member's stretch on message k's own coins (hcf, hce: `rowsR_csAt`'s premises, to the
letter); d: data that the job's data at the test's front is (hd). -/
theorem wordsAt_of_first_kind_member_at_purse {Wd W X : Type} (J : K1.SendJob Wd X) (lift : W → Wd)
    (at_ : Addr) (k : ℕ) (hk : k < J.P.sent.size) (fs : Option ℕ × Option ℕ) (A : ManyJob W X)
    (n : ℕ) (hn : A.mems[n]? = some (memK1 J lift at_ k fs)) (w : W) (fr : Front X)
    (C : TestCoins) (d : ℕ → ℕ → ℕ → Option (GF ⊕ GE)) (hd : J.data (lift w) fr = d)
    (c : Cs (K1.dueR J.P J.ride))
    (hcf : ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P k) (J.ride k)).f →
      K1.cf c ((K1.startR J.P J.ride k).f + i) = (C.mem n).f i)
    (hce : ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P k) (J.ride k)).e →
      K1.ce c ((K1.startR J.P J.ride k).e + i) = (C.mem n).e i)
    (S : Statement) (L : GroupLayout) (o : ℕ) (hf : L.find o = some n) (y : Oracle)
    (hy : S.oracles[o]? = some y) (hsh : y.shape = shapeAt J.P k) (pt : OnBytes.Part) (i : ℕ) :
    ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) o pt i =
      (K1.rowsR J.P J.ride d c k).word (shapeAt J.P k) pt i := by
  rw [wordsAt_of_first_kind_member J lift at_ k fs A n hn w fr C S L o hf y hy hsh pt i, hd,
    ProofFile.Honest.K12.AtProof.rowsR_csAt J.P J.ride d k hk (C.mem n) c hcf hce]

/-- **The same as the library's held words**: where o is the message's number first + k, whatever
words m₀ were held before. -/
theorem wordsAt_of_first_kind_member_held {Wd W X : Type} (J : K1.SendJob Wd X) (lift : W → Wd)
    (at_ : Addr) (k : ℕ) (hk : k < J.P.sent.size) (fs : Option ℕ × Option ℕ) (A : ManyJob W X)
    (n : ℕ) (hn : A.mems[n]? = some (memK1 J lift at_ k fs)) (w : W) (fr : Front X)
    (C : TestCoins) (d : ℕ → ℕ → ℕ → Option (GF ⊕ GE)) (hd : J.data (lift w) fr = d)
    (c : Cs (K1.dueR J.P J.ride))
    (hcf : ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P k) (J.ride k)).f →
      K1.cf c ((K1.startR J.P J.ride k).f + i) = (C.mem n).f i)
    (hce : ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P k) (J.ride k)).e →
      K1.ce c ((K1.startR J.P J.ride k).e + i) = (C.mem n).e i)
    (S : Statement) (L : GroupLayout) (first : ℕ) (hf : L.find (first + k) = some n) (y : Oracle)
    (hy : S.oracles[first + k]? = some y) (hsh : y.shape = shapeAt J.P k) (m₀ : Words GE)
    (pt : OnBytes.Part) (i : ℕ) :
    Johnson.Prover.Send.held m₀ first J.P (K1.rowsR J.P J.ride d c) (first + k) pt i =
      ProofFile.Honest.K12.wordsAt S L (plainMany A w fr C) (first + k) pt i := by
  rw [Johnson.Prover.Send.held_new m₀ first J.P _ k hk pt i]
  exact (wordsAt_of_first_kind_member_at_purse J lift at_ k hk fs A n hn w fr C d hd c hcf hce S L
    (first + k) hf y hy hsh pt i).symm

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.lst_tabG_inside
#print axioms ProofFile.Honest.K12.AtFile.lst_tabG_beyond
#print axioms ProofFile.Honest.K12.AtFile.rowsR_ends_at_code_lengths
#print axioms ProofFile.Honest.K12.AtFile.wordsAt_of_laid_rows
#print axioms ProofFile.Honest.K12.AtFile.wordsAt_of_first_kind_member
#print axioms ProofFile.Honest.K12.AtFile.wordsAt_of_first_kind_member_at_purse
#print axioms ProofFile.Honest.K12.AtFile.wordsAt_of_first_kind_member_held
