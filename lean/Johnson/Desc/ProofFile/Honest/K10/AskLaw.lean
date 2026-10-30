-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/AskLaw.lean: the law on values of the closing of a segment (K10), at the
prover's own terms: what the closing hands to the fold (`closeAsk`, Honest/K10/Job.lean), read in the field;
and with it: where the rounds send what `foldWords` (Honest/K10/Words.lean) says of these data, the single
rows that the verifier's block's decision lays into the frame are true. Theorems; one definition
(`askWords`).

The yes is not earned by what is sent. Each law below ends "the decision says yes, and the single rows
… are true". The yes comes from the facts on the record in front and the rounds' number and shape alone
(`close_yes_all`, Johnson/Desc/K10/Honest/Base.lean): under these facts the decision refuses no rounds of
the shape, whatever they send. All that these laws say of values is the second clause.

  `read_addUp`, `read_foldl_add`   sums in the program's arithmetic read as sums in the field
  `mainWeight_int`, `maskWeight_int`   the library's weight in the field is 1 where its weight in the integers is 1,
                   else 0
  `askWords`       the entries of the oracle messages' own tables, read in the field, as words
  `askWords_padded`, `wordAt_shapes`, `wordAt_begun`   what `wordAt` makes is 0 on rows that nobody sent; it
                   reads of the statement the oracle messages' shapes alone; so at the statement behind
                   the beginning of the test it makes what it makes at the statement in front
  `rowsFit_length`, `rowsAt_member`, `weights_none`, `layoutOf_members`, `weight_member`, `kept_on_member` `rowsAt`'s
                   default is not read where something is due: where `rowsFit` says yes, at a member's number the rows'
                   member at that member's place is read; a table of the group reads an oracle message only where the
                   library's weight is 1, and there it is a member; each kept form of the batched row is on a member.
                   (That the zeros of `wordAt` stand only where nothing is due is said by no statement here; nor is
                   anything on what a member's rows are outside its shape)
  `vecIn_tables`   the two tables (`closeMain`, `closeMask`) are the stage's message as the words fill it
                   (`msgOf` of `tablesOf`): the tables are laid by `tablesOf`'s own text
  `vecG_written`   the batched row, written out, is the claim's vector of coefficients
  `read_closeKept` `closeKept`'s word reads as the kept forms' value
  `base_row`       what the facts on the record in front (`CloseBase`) give of the batched row
  `tables_law`    the law at tables made of given entries mw, zw: from `CloseBase`, rows that hold of these
                   entries, a fresh table that pairs, rounds of the kind's shape that send
                   `foldSigmaE`'s and `foldRoundE`'s words at the row written out, these tables and
                   `closeKept`'s word: the decision says yes, and the single rows are true
  `ask_of_base`    what `closeAsk` yields under `CloseBase`, where the place's h is the frame's group's,
                   `stAt` yields the record's statement and group, the job's `rows` yields rows and
                   `rowsFit` says yes of them: just these data, at the entries that `wordAt` makes of
                   these rows
  `ask_law`      the two joined: the law at the data that `closeAsk` yields and the words that `foldWords`
                   says of them
  `read_closeMain`, `read_closeMask`, `vec_map`, `idx_lt`, `sigma_cast`, `round_cast`   small steps

By: `close_plays` (Johnson/Desc/K10/Honest/Leaves.lean); `sigma_readsE`, `rounds_show`
(Johnson/Prover/Link/FoldWordsShows.lean), whose named premise `FoldSizes` is shown here;
`Form.writeOut_val` (OnBytes/Iop/DotLaws.lean); `find_of_mem`, `find_some`, `mem_of_find`
(Johnson/Desc/Means/Layout.lean); `batch_rowfits`, `combine_inv`
(Johnson/Desc/K10/Honest/RowFits.lean); `bat_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean).

Limits. Of the block's decision (`Block.decide`) at the kind's own record, not of its step (the step, lifted, wrapped
and guarded: Johnson/Desc/K10/Honest/Step.lean, AtS.lean). That the rounds send these words is a premise: that the
frame's play of the kind's older caller (`foldShell`: `closeAskAt`'s cut, the coefficients off the spent run's coins)
sends them is shown by no theorem of this library; of the row's part (`foldShellT true`, Honest/K10/Sim.lean) this file
says nothing. `CloseBase`, and that `stAt` yields the record's statement, are premises: shown of no honest run. That the
rows hold of the entries is a premise: it is what the parts in front owe. The fresh table φ is a letter, and so are what
was shown and heard in front of "BAT" (seen, front) and the carried coins (ca): nothing ties these three to the record
or to any rounds but the premises on `stAt` and `rows`; φ is asked to pair with the spent run's coefficients, not to be
the table of the oracle message that was sent. That the entries are what was committed to is not spoken of. The clause
that is left stands in the fold's letters (`vecS`, `foldMsg`, `keptVal`): no joining on to a next kind's law is shown.
No premise but `rowsFit`, which `ask_of_base` and `ask_law` take (both lengths powers of two; the statement's group's
codes), asks that the base code's message length is a power of two; `tables_law` does not ask it: the stage's length is
2^logEll. `CloseBase.bits` bounds k + logEll by 63 in all three. In front of `ask_law` seven definitions are marked
irreducible to the end of the section, so that Lean does not unfold them while it compares terms: that turns no
statement, and the kernel reads no such mark. No member is shown here. No property of the protocol is claimed: nothing
is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Words
import Johnson.Prover.Link.FoldWordsShows
import Johnson.Desc.K10.Honest.Leaves
import OnBytes.Iop.DotLaws
import Johnson.Desc.Own.ShapesMean
import Johnson.Desc.Means.Layout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE addE mulE Statement GroupLayout GroupRow KeptForm mainWeight maskWeight mainBack
  maskBack keptWeight)
open OnBytes.Means (Words tableSize)
open OnBytes.Slice (readE rdE readE_add readE_mul formAt readV vec vecIn vecG GE rowNo_lt Sg)
open Johnson.Prover.Link (keptVal FoldSizes)
open H2K.ClaimSays (msgOf)
open ProofFile.Honest.K10.Values (keptLen)
open Cb

/-! ## 1 Sums -/

theorem read_addUp (f : Nat → E) : ∀ n, readE (addUp n f) = ∑ i ∈ Finset.range n, readE (f i)
  | 0 => rdE.zero
  | n + 1 => by
    have ih := read_addUp f n
    unfold addUp at ih ⊢
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    exact readE_add _ _

theorem read_foldl_add {α : Type} (g : α → E) : ∀ (l : List α) (a : E),
    readE (l.foldl (fun s f => addE s (g f)) a) = readE a + (l.map fun f => readE (g f)).sum
  | [], a => by simp
  | f :: l, a => by
    rw [List.foldl_cons, read_foldl_add g l, readE_add, List.map_cons, List.sum_cons, add_assoc]

/-! ## 2 The library's weights: in the field 1 where 1 in the integers, else 0 -/

theorem mainWeight_int (S : Statement) (L : GroupLayout) (o J : Nat) :
    mainWeight (K := GE) S L o J = if mainWeight (K := Int) S L o J = 1 then 1 else 0 := by
  unfold mainWeight
  cases L.find o with
  | none => simp
  | some i =>
    simp only
    by_cases hk : L.kept.getD i false = true
    · simp [hk]
    · simp only [hk, Bool.false_eq_true, if_false]
      cases L.mainFirst.getD i none with
      | none => simp
      | some first =>
        simp only
        split <;> simp

theorem maskWeight_int (S : Statement) (L : GroupLayout) (o J : Nat) :
    maskWeight (K := GE) S L o J = if maskWeight (K := Int) S L o J = 1 then 1 else 0 := by
  have key : ∀ (c : Nat → Prop) [∀ f, Decidable (c f)] (x : Option Nat),
      (match x with
        | none => (0 : GE)
        | some first => if c first then 1 else 0) =
      if (match x with
        | none => (0 : Int)
        | some first => if c first then 1 else 0) = 1 then 1 else 0 := by
    intro c _ x
    cases x with
    | none => simp
    | some f => by_cases h : c f <;> simp [h]
  unfold maskWeight
  cases L.find o with
  | none => simp
  | some i => exact key _ _

/-! ## 3 The tables -/

/-- The entries of the messages' own tables, read in the field, as words. -/
def askWords (mw zw : Nat → Nat → E) : Words GE := fun o part i =>
  match part with
  | .main => readE (mw o i)
  | .mask => readE (zw o i)

/-- The entries that `wordAt` makes are 0 on the rows beyond the real ones: the library's `Padded`. -/
theorem askWords_padded (S : Statement) (lm lz : Nat) (am az : Nat → Nat → Nat → E) :
    OnBytes.Means.Padded S (askWords (fun o => wordAt S lm am o .main) fun o => wordAt S lz az o .mask) := by
  intro o part i h
  have hn : ¬ i % 2 ^ S.rowBits o part < OnBytes.Means.realRows S o part := Nat.not_lt.2 h
  cases part
  · show readE (wordAt S lm am o .main i) = 0
    unfold wordAt
    simp only [hn, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
    exact rdE.zero
  · show readE (wordAt S lz az o .mask i) = 0
    unfold wordAt
    simp only [hn, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
    exact rdE.zero

/-- `wordAt` reads of the statement the oracle messages' shapes alone: at two statements that have, at each
number, the same shape (or both none) it makes the same entries. -/
theorem wordAt_shapes {S S' : Statement}
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : OnBytes.Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : OnBytes.Oracle => x.shape)) (ell : Nat)
    (at_ : Nat → Nat → Nat → E) (o : Nat) (part : OnBytes.Part) (i : Nat) :
    wordAt S' ell at_ o part i = wordAt S ell at_ o part i := by
  have e := hs o
  have e12 : S'.rowBits o part = S.rowBits o part ∧
      OnBytes.Means.realRows S' o part = OnBytes.Means.realRows S o part := by
    unfold OnBytes.Statement.rowBits OnBytes.Means.realRows
    cases h1 : S'.oracles[o]? with
    | none =>
      cases h2 : S.oracles[o]? with
      | none => exact ⟨rfl, rfl⟩
      | some x => rw [h1, h2] at e; cases e
    | some x' =>
      cases h2 : S.oracles[o]? with
      | none => rw [h1, h2] at e; cases e
      | some x =>
        rw [h1, h2] at e
        have e' : x'.shape = x.shape := Option.some.inj e
        show OnBytes.ceilLog2 (x'.shape.rows part) = OnBytes.ceilLog2 (x.shape.rows part) ∧
          x'.shape.rows part = x.shape.rows part
        rw [e']
        exact ⟨rfl, rfl⟩
  unfold wordAt
  rw [e12.1, e12.2]

/-- **At the statement behind the beginning of the test `wordAt` makes the entries that it makes at the
statement in front**: so rows that hold of the words made at the one hold of those made at the other. -/
theorem wordAt_begun (S : Statement) (g : Nat) (G : OnBytes.Group) (ell : Nat)
    (at_ : Nat → Nat → Nat → E) :
    wordAt (OnBytes.Slice.begun S g G) ell at_ = wordAt S ell at_ := by
  funext o part i
  exact wordAt_shapes (OnBytes.Slice.closeLedgers_shape G.members.toList S) ell at_ o part i

/-- What `rowsFit` says of the number of members. -/
theorem rowsFit_length {S : Statement} {G : OnBytes.Group} {R : GroupData} (hf : rowsFit S G R = true) :
    R.members.length = G.members.size := by
  unfold rowsFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  exact hf.1.2

/-- **At a member of the group no default is read**: where the public test `rowsFit` says yes, `rowsAt` at a
member's number reads the rows' member at that member's place in the statement's list. -/
theorem rowsAt_member {S : Statement} {G : OnBytes.Group} {R : GroupData} (hf : rowsFit S G R = true)
    {o : Nat} (ho : o ∈ G.members.toList) :
    ∃ i x, G.members.idxOf? o = some i ∧ R.members[i]? = some x ∧
      ∀ (f : MemberRows → Nat → Nat → E) (b p : Nat), rowsAt G R f o b p = f x b p := by
  obtain ⟨i, hi⟩ := OnBytes.Means.find_of_mem
    (L := { (default : GroupLayout) with members := G.members }) ho
  have hlt : i < G.members.size := (OnBytes.Means.find_some hi).1
  have hi' : G.members.idxOf? o = some i := hi
  have hR : i < R.members.length := (rowsFit_length hf) ▸ hlt
  refine ⟨i, R.members[i], hi', List.getElem?_eq_getElem hR, fun f b p => ?_⟩
  unfold rowsAt
  rw [hi', Option.bind_some, List.getElem?_eq_getElem hR]

/-- At a number that has no place in the layout all three of the library's weights are 0. -/
theorem weights_none {K : Type} [CommRing K] {S : Statement} {L : GroupLayout} {o : Nat}
    (h : L.find o = none) (J : Nat) :
    mainWeight (K := K) S L o J = 0 ∧ maskWeight (K := K) S L o J = 0 ∧
      keptWeight (K := K) L o = 0 := by
  unfold mainWeight maskWeight keptWeight
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- The layout that the verifier's text makes of a group has the group's list of members. -/
theorem layoutOf_members (S : Statement) (G : OnBytes.Group) :
    (VerifiableInference.Desc.Own.layoutOf S G).members = G.members := rfl

/-- **Whatever a table of the group reads is a member's**: `closeMain` and `closeMask` read an oracle message's
entries only where the library's weight, asked in the integers, is 1: there the message is a member of
the group. The like where the library's weight for a kept member is 1 (for `kept_on_member`). -/
theorem weight_member {S S' : Statement} {G : OnBytes.Group} {o J : Nat}
    (h : mainWeight (K := Int) S' (VerifiableInference.Desc.Own.layoutOf S G) o J = 1 ∨
      maskWeight (K := Int) S' (VerifiableInference.Desc.Own.layoutOf S G) o J = 1 ∨
      keptWeight (K := GE) (VerifiableInference.Desc.Own.layoutOf S G) o = 1) :
    o ∈ G.members.toList := by
  cases hf : (VerifiableInference.Desc.Own.layoutOf S G).find o with
  | some i =>
    have := OnBytes.Means.mem_of_find hf
    rwa [layoutOf_members] at this
  | none =>
    rcases h with h | h | h
    · rw [(weights_none (K := Int) hf J).1] at h
      exact absurd h (by decide)
    · rw [(weights_none (K := Int) (S := S') hf J).2.1] at h
      exact absurd h (by decide)
    · rw [(weights_none (K := GE) (S := S') hf J).2.2] at h
      exact absurd h zero_ne_one

theorem read_closeMain (S : Statement) (L : GroupLayout) (mw zw : Nat → Nat → E) (J : Nat)
    (hJ : J < 2 ^ (L.k + L.logEll)) :
    readE ((closeMain S L mw).getD J zeroE) = (OnBytes.Means.tablesOf S L (askWords mw zw)).main J := by
  have e : (closeMain S L mw).getD J zeroE = addUp S.oracles.size fun o =>
      if mainWeight (K := Int) S L o J = 1 then mw o (mainBack S L o J) else zeroE := by
    unfold closeMain
    simp [Array.getD, hJ]
  rw [e, read_addUp]
  show _ = ∑ o ∈ Finset.range S.oracles.size,
    mainWeight (K := GE) S L o J * readE (mw o (mainBack S L o J))
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [mainWeight_int]
  split
  · rw [one_mul]
  · rw [zero_mul]
    exact rdE.zero

theorem read_closeMask (S : Statement) (L : GroupLayout) (mw zw : Nat → Nat → E) (J : Nat)
    (hJ : J < 2 ^ (L.h + L.logEllZk)) :
    readE ((closeMask S L zw).getD J zeroE) = (OnBytes.Means.tablesOf S L (askWords mw zw)).mask J := by
  have e : (closeMask S L zw).getD J zeroE = addUp S.oracles.size fun o =>
      if maskWeight (K := Int) S L o J = 1 then zw o (maskBack S L o J) else zeroE := by
    unfold closeMask
    simp [Array.getD, hJ]
  rw [e, read_addUp]
  show _ = ∑ o ∈ Finset.range S.oracles.size,
    maskWeight (K := GE) S L o J * readE (zw o (maskBack S L o J))
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [maskWeight_int]
  split
  · rw [one_mul]
  · rw [zero_mul]
    exact rdE.zero

/-- An array of the program's elements, as triples, read at an index. -/
theorem vec_map (a : Array E) (i : Nat) : vec (a.map (·.triple)) i = readE (a.getD i zeroE) := by
  unfold vec Fmt.M1.ent readE
  congr 1
  by_cases h : i < a.size
  · simp [Array.getD, h]
  · simp [Array.getD, h]
    rfl

theorem idx_lt {a A b B : Nat} (ha : a < A) (hb : b < B) : a + A * b < A * B := by
  calc a + A * b < A + A * b := by omega
    _ = A * (b + 1) := by ring
    _ ≤ A * B := Nat.mul_le_mul_left _ hb

/-- **The two tables that the closing hands over are the stage's message**, as the words fill it: where the layout's k,
h and two lengths are the stage's (hk, hh, hl, hz). -/
theorem vecIn_tables (st : Sg) (S : Statement) (L : GroupLayout) (mw zw : Nat → Nat → E)
    (hk : L.k = st.h + st.g) (hh : L.h = st.h) (hl : 2 ^ L.logEll = st.C.l)
    (hz : 2 ^ L.logEllZk = st.Z.l) :
    vecIn st ⟨(closeMain S L mw).map (·.triple), (closeMask S L zw).map (·.triple), Fmt.Fld.zeroE⟩ =
      msgOf st (OnBytes.Means.tablesOf S L (askWords mw zw)) := by
  funext j
  rcases j with x | x
  · show vec _ _ = (OnBytes.Means.tablesOf S L (askWords mw zw)).main _
    rw [vec_map, read_closeMain S L mw zw]
    rw [hk, pow_add 2 (st.h + st.g) L.logEll, hl]
    exact idx_lt (rowNo_lt x.1) x.2.isLt
  · show vec _ _ = (OnBytes.Means.tablesOf S L (askWords mw zw)).mask _
    rw [vec_map, read_closeMask S L mw zw]
    rw [hh, pow_add 2 st.h L.logEllZk, hz]
    exact idx_lt (rowNo_lt x.1) x.2.isLt

/-- **The batched row, written out, is the claim's vector of coefficients**: of any group's row whose form on the main
table fits (hf), where the layout's k and main length are the stage's (hk, hl). -/
theorem vecG_written (st : Sg) (L : GroupLayout) (row : GroupRow)
    (hk : L.k = st.h + st.g) (hl : 2 ^ L.logEll = st.C.l)
    (hf : VerifiableInference.Desc.Own.formFits row.c (L.k + L.logEll) = true) :
    vecG st row =
      vecIn st ⟨(row.c.writeOut (L.k + L.logEll)).map (·.triple), row.d.map (·.triple),
        Fmt.Fld.zeroE⟩ := by
  have hv : ∀ v ∈ row.c.tensors, v.vars = L.k + L.logEll := fun v h =>
    (((VerifiableInference.Desc.Own.formFits_iff _ _).1 hf).1 v h).1
  funext j
  rcases j with x | x
  · show formAt row.c _ = vec _ _
    rw [vec_map]
    refine ((OnBytes.Form.writeOut_val rdE row.c _ hv _ ?_).2).symm
    rw [hk, pow_add 2 (st.h + st.g) L.logEll, hl]
    exact idx_lt (rowNo_lt x.1) x.2.isLt
  · show readV row.d _ = vec _ _
    rw [vec_map]
    rfl

/-! ## 4 The kept forms -/

theorem read_closeKept (S : Statement) (Ks : Array KeptForm) (mw : Nat → Nat → E) :
    readE (closeKept S Ks mw) = keptVal (keptLen S) (fun o i => readE (mw o i)) Ks := by
  unfold closeKept keptVal
  rw [read_foldl_add, show readE zeroE = 0 from rdE.zero, zero_add]
  refine congrArg List.sum (List.map_congr_left fun f _ => ?_)
  rw [read_addUp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [readE_mul]
  rfl

/-! ## 5 What the facts on the record in front give of the batched row; the laws -/

section Base
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec kind)
open OnBytes.Means (AllSay GroupOk RowIn extends_begun begun_group layout_eq layoutOf_extends)
open OnBytes.Slice (runRows ptK lst vecS)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase layoutOf_same ShapedAll)
open Johnson.Prover.Link (sentOf drawnOf Pairs foldMsg coefU uOfBook foldSigmaE foldRoundE
  sigma_readsE rounds_show)

/-- Of a row that the batching returns, under the facts in front: its form on the main table fits; its
coefficients on the mask table are as many as the table's entries; each separate form is on a kept
member. -/
theorem base_row {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) {x : E} {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row) :
    Own.formFits row.c ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll) = true ∧
      row.d.size = 2 ^ ((Own.layoutOf s.st D.G).h + (Own.layoutOf s.st D.G).logEllZk) ∧
      ∀ f ∈ row.kept.toList, keptWeight (K := GE) (Own.layoutOf s.st D.G) f.oracle = 1 := by
  have hE := extends_begun s.st s.frame.group D.G
  have hc : (D.S1 s).codes = s.st.codes := hE.codes
  have hG' := begun_group s.st s.frame.group D.G H.there
  have hOk' : GroupOk (D.S1 s) { D.G with inRun := true, rows := #[] } :=
    H.inOrder.extends hE rfl rfl rfl rfl
  have eL := layoutOf_same H.there
  have hL' : (D.S1 s).layout s.frame.group = some (Own.layoutOf s.st D.G) := by
    show (OnBytes.Slice.begun s.st s.frame.group D.G).layout s.frame.group = _
    rw [layout_eq _ _ _ hG', eL,
      layoutOf_extends (G' := { D.G with inRun := true, rows := #[] }) hE H.inOrder rfl rfl rfl rfl]
  have hr' : ∀ r ∈ (runRows s.st D.G).toList,
      RowIn (D.S1 s) { D.G with inRun := true, rows := #[] } r :=
    fun r h => RowIn.extends (G := D.G) hE (fun _ c => c) (H.rowsIn r h)
  have hb : OnBytes.Bat.combine (D.S1 s) s.frame.group
      ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row :=
    (Own.batch_agrees _ _ _ _).trans hrow
  have e2 : ((D.S1 s).codes.mask.getD s.frame.shape.maskCode default).ell =
      2 ^ (Own.layoutOf s.st D.G).logEllZk := by
    rw [hc, H.power, ← H.maskCode]
    rfl
  have e1 : OnBytes.ceilLog2 ((D.S1 s).codes.base.getD s.frame.shape.code default).ell =
      (Own.layoutOf s.st D.G).logEll := by
    rw [hc, ← H.code]
    rfl
  have hfit : Own.foldRowFits (First.Close.spent (D.S1 s) D.m) (D.F s) row = true :=
    RowFit.batch_rowfits hG' hL' hOk' hr' H.termsOk hrow (First.Close.spent (D.S1 s) D.m) rfl
      (fun o ho => (First.Close.spent_extends D.m (D.S1 s)).tableBits (hOk'.there o ho) .main)
      (D.F s) rfl rfl H.kh.1.symm H.kh.2.symm e1 e2 H.bits
  obtain ⟨⟨_, i2⟩, i3⟩ := RowFit.combine_inv hG' hL' hOk' hr'
    (fun r hr'' t ht hp => RowFit.own_of_ok (H.termsOk r hr'' t ht hp)) hb
  refine ⟨?_, i3, fun f hf => ?_⟩
  · unfold Own.foldRowFits at hfit
    simp only [Bool.and_eq_true] at hfit
    have h1 := hfit.1.1
    have ek : (D.F s).layout.k = (Own.layoutOf s.st D.G).k := H.kh.1.symm
    have el : OnBytes.ceilLog2
        ((First.Close.spent (D.S1 s) D.m).codes.base.getD (D.F s).code default).ell =
        (Own.layoutOf s.st D.G).logEll := e1
    rw [ek, el] at h1
    exact h1
  · obtain ⟨⟨i, k1, k2⟩, _⟩ := i2 f hf
    unfold keptWeight
    rw [k1]
    simp [k2]

/-- **Each kept form of the batched row is on a member of the group**: so `closeKept`, which reads the entries
of whatever oracle message a kept form names, reads members alone. -/
theorem kept_on_member {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) {x : E} {row : GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row) :
    ∀ f ∈ row.kept.toList, f.oracle ∈ D.G.members.toList := fun f hf =>
  weight_member (S' := s.st) (J := 0) (.inr (.inr ((base_row H hrow).2.2 f hf)))

/-- **The kind's law on values, at tables made of given entries.** Let the facts `CloseBase P s D` hold of
the record in front, and let st be a stage of the library with the group's four numbers (nk, nh, nl,
nz). mw, zw: the entries of the oracle messages' own main and mask tables, as elements of the program;
let every row that the test takes in hold of them, read in the field. w: the 2 k + 1 coefficients; φ: a
fresh table that pairs with them. rB, rE, rR: rounds of the kind's shape, of which "FOLD epsilon" sends
`foldSigmaE`'s word and the i-th "FOLD round" `foldRoundE`'s two words at these data: the batched row
written out, the two tables that `closeMain` and `closeMask` make of mw and zw, the kept
forms' value by `closeKept`. (That `closeAsk` yields such data: `ask_of_base`.) Then the block's decision
says yes, and the single rows that it lays into the frame are true of the folded message, their kept forms
with them. (The yes hangs on nothing that is sent: this file's head.) -/
theorem tables_law {Cl : Type} {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (st : Sg)
    (nk : D.Gq.k = st.h + st.g) (nh : D.Gq.h = st.h)
    (nl : 2 ^ (Own.layoutOf s.st D.G).logEll = st.C.l)
    (nz : 2 ^ (Own.layoutOf s.st D.G).logEllZk = st.Z.l) (mw zw : Nat → Nat → E)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList (askWords mw zw)) (rB rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    (φ : st.cFr.J → GE) (w : Fin (2 * (st.h + st.g) + 1) → E)
    (hP : Pairs st st.Z.l (coefU (st.h + st.g) (uOfBook (st.h + st.g) fun i => (w i).triple)) φ)
    (hσ : (sentOf rE).getD 0 zeroE = foldSigmaE (st.h + st.g) w)
    (hq : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row → ∀ i (h : i < rR.length),
      (sentOf rR[i]).getD 0 zeroE = (foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          (drawnOf rE) ((rR.take i).map drawnOf)).1 ∧
        (sentOf rR[i]).getD 1 zeroE = (foldRoundE (st.h + st.g) st.h
          (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
          (closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw)
          (closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw) (closeKept (D.S1 s) row.kept mw) w
          (drawnOf rE) ((rR.take i).map drawnOf)).2) :
    ∃ s', ((kind (Cl := Cl)) P).decide s (rB :: rE :: rR) gs = .ok s' ∧
      ∑ j, vecS st s'.frame.rows j *
            foldMsg st (msgOf st
                (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw))) φ
              (sPt 2 (st.h + st.g) (ptK (st.h + st.g) (lst ((rR.map drawnOf).map (·.triple))))) j +
          keptVal (keptLen (D.S1 s))
            (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)).kept
            s'.frame.rows.kept = readE s'.frame.rows.target := by
  have hk : (Own.layoutOf s.st D.G).k = st.h + st.g := H.kh.1.trans nk
  have hh : (Own.layoutOf s.st D.G).h = st.h := H.kh.2.trans nh
  have hlen : rR.length = st.h + st.g := by
    have h1 : rR.length + 2 = 2 + P.k := by simpa using hl
    have h2 : P.k = D.Gq.k := H.stretch
    omega
  refine ProofFile.Honest.K10.Values.close_plays (Cl := Cl) H st nk nh nl nz (askWords mw zw) hs rB rE rR gs
    hl hsh φ _ _ hP (by rw [hσ]; exact sigma_readsE _ w) fun row hrow => ?_
  obtain ⟨f1, f2, f3⟩ := base_row H hrow
  have hV : keptVal (keptLen (D.S1 s))
      (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords mw zw)).kept row.kept =
      readE (closeKept (D.S1 s) row.kept mw) := by
    rw [read_closeKept]
    unfold keptVal
    refine congrArg List.sum (List.map_congr_left fun f hf => ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ * (keptWeight (K := GE) (Own.layoutOf s.st D.G) f.oracle * readE (mw f.oracle i)) = _
    rw [f3 f hf, one_mul]
  have hsz : FoldSizes (st.h + st.g) st.h st.C.l st.Z.l
      ((row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)).map (·.triple))
      (row.d.map (·.triple))
      ((closeMain (D.S1 s) (Own.layoutOf s.st D.G) mw).map (·.triple))
      ((closeMask (D.S1 s) (Own.layoutOf s.st D.G) zw).map (·.triple)) := by
    have hv : ∀ v ∈ row.c.tensors,
        v.vars = (Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll := fun v h =>
      (((Own.formFits_iff _ _).1 f1).1 v h).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Array.size_map, (OnBytes.Form.writeOut_val rdE row.c _ hv 0 (Nat.two_pow_pos _)).1, hk,
        pow_add, nl]
    · unfold closeMain
      rw [Array.size_map, Array.size_ofFn, hk, pow_add, nl]
    · rw [Array.size_map, f2, hh, pow_add, nz]
    · unfold closeMask
      rw [Array.size_map, Array.size_ofFn, hh, pow_add, nz]
  rw [vecG_written st (Own.layoutOf s.st D.G) row hk nl f1,
    ← vecIn_tables st (D.S1 s) (Own.layoutOf s.st D.G) mw zw hk hh nl nz, hV]
  exact rounds_show st _ _ _ _ _ w (drawnOf rE) hsz rR hlen (hq row hrow)

/-- **What `closeAsk` yields, under the facts on the record in front**: where the place's h is the frame's
group's (hh: no fact of `CloseBase` reads the place's h), `stAt` yields the record's statement and group,
the job's `rows` yields the group's rows R and the public test `rowsFit` says yes of them, at a challenge of
"BAT"'s form: the data are the batched row written out, the two tables by `closeMain` and `closeMask` and
the kept forms' value by `closeKept`, at the statement behind the beginning of the test, of the entries
that `wordAt` makes of R's members' rows (`rowsAt`). -/
theorem ask_of_base {W : Type} (J : CloseJob W) {s : Rec} {D : BaseData}
    (H : CloseBase J.pub.par s D) (hh : J.pub.par.h = D.Gq.h) (w : W) (seen : Seen)
    (front : List Fmt.Drawn) (t : Fmt.Ext)
    (hst : J.stAt w seen front = .ok (s.st, s.frame.group)) (u : Fin (2 * J.pub.par.k + 1) → E)
    (ca : CsAll (closeCarries J.pub)) (R : GroupData) (hr : J.rows w front ca = .ok R)
    (hf : rowsFit s.st D.G R = true) :
    ∃ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (E.ofTriple t) = some row ∧
      closeAsk J w seen front ⟨[t], [], [], none⟩ u ca = .ok (some
        { k := J.pub.par.k, h := J.pub.par.h
          c := row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)
          d := row.d
          m := closeMain (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
            wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main
          mu := closeMask (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
            wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask
          keptV := closeKept (D.S1 s) row.kept fun o =>
            wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main
          w := u }) := by
  obtain ⟨D', HF⟩ := ProofFile.Honest.K10.YesFree.closeFront_all H (E.ofTriple t)
  have eb : (D'.input, D'.d) = (⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩,
      { First.Close.onSt s.st with st := D.S1 s }) := by
    have h1 := HF.layout
    unfold Ground.beginRunP at h1
    have hb : Ground.ok (Ground.beginRunL (First.Close.onSt s.st).st s.frame.group) = true :=
      H.beginRun
    have ht' : (First.Close.onSt s.st).st.groups[s.frame.group]? = some D.G := H.there
    rw [if_pos hb, ht'] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨ei, ed⟩ := Prod.mk.inj eb
  obtain ⟨xs, x', u1, _, u3⟩ := ProofFile.Honest.K10.YesFree.heard_made
    (e := ProofFile.Honest.K10.YesFree.eBat J.pub.par) (r := ⟨[], ⟨[t], [], [], none⟩⟩) rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ⟨⟨[], rfl, rfl⟩, ⟨t, rfl⟩, rfl, rfl⟩
  obtain rfl : x' = E.ofTriple t := u3 t rfl
  have hbat : First.Close.bat s.st s.frame.group (ProofFile.Honest.K10.YesFree.eBat J.pub.par)
      ⟨[], ⟨[t], [], [], none⟩⟩ = .ok (D'.row, D'.input.layout, D'.d.st) :=
    (First.Close.bat_iff _ _ _ _ _ _ _).2
      ⟨HF.beginRun, D'.input, D'.d, HF.layout, xs, _, u1, HF.rows, HF.combine, rfl, rfl⟩
  rw [ei, ed] at hbat
  have hrow := HF.combine
  rw [ei, ed] at hrow
  refine ⟨D'.row, hrow, ?_⟩
  have hk1 : ((Own.layoutOf s.st D.G).k != J.pub.par.k ||
      (Own.layoutOf s.st D.G).h != J.pub.par.h) = false := by
    rw [H.kh.1, H.kh.2, H.stretch, hh]
    simp
  have hd1 : (D'.row.d.size !=
      2 ^ ((Own.layoutOf s.st D.G).h + (Own.layoutOf s.st D.G).logEllZk)) = false := by
    rw [(base_row H hrow).2.1]
    simp
  unfold closeAsk
  rw [ProofFile.Honest.K10.YesFree.entries_eq]
  simp only [hst, hbat, hk1, hd1, hr, hf, H.there, Bool.not_true, Bool.false_eq_true, if_false,
    List.head?_cons, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem sigma_cast {k k' : Nat} (e : k = k') (w : Fin (2 * k + 1) → E) :
    foldSigmaE k w = foldSigmaE k' fun i => w (Fin.cast (by rw [e]) i) := by
  subst e
  rfl

theorem round_cast {k k' : Nat} (e : k = k') (h : Nat) (c d m mu : Array E) (V : E)
    (w : Fin (2 * k + 1) → E) (eps : E) (gs : List E) :
    foldRoundE k h c d m mu V w eps gs =
      foldRoundE k' h c d m mu V (fun i => w (Fin.cast (by rw [e]) i)) eps gs := by
  subst e
  rfl

attribute [local irreducible] foldSigmaE foldRoundE closeMain closeMask closeKept wordAt
  OnBytes.Form.writeOut

/-- **The kind's law on values, at the prover's own terms.** J: a job of the place; the facts `CloseBase`
hold of the record s in front; st: a stage of the library with the group's four numbers (nk, nh: its row
variables; nl, nz: the two message lengths); the place's h is the frame's group's (hh); `stAt` yields
that record's statement and group at what was shown and heard in front of "BAT"; the job's `rows` yields
the group's rows R, and the public test `rowsFit` says yes of them. Let every row that the test takes in
hold of the entries of R's members' rows (`wordAt`, `rowsAt`), read in the field; let φ be a
fresh table that pairs with the spent run's coefficients u. Let "BAT" have drawn t, and let the rounds
"FOLD epsilon" and "FOLD round", of the kind's shape, send what `foldWords` says of the data that `closeAsk`
yields. Then the block's decision says yes, and the single rows that it lays into the frame are true of the
folded message, their kept forms with them. -/
theorem ask_law {Cl W : Type} (J : CloseJob W) {s : Rec} {D : BaseData}
    (H : CloseBase J.pub.par s D) (st : Sg) (nk : D.Gq.k = st.h + st.g) (nh : D.Gq.h = st.h)
    (nl : 2 ^ (Own.layoutOf s.st D.G).logEll = st.C.l)
    (nz : 2 ^ (Own.layoutOf s.st D.G).logEllZk = st.Z.l) (hh : J.pub.par.h = D.Gq.h) (w : W)
    (seen : Seen) (front : List Fmt.Drawn) (t : Fmt.Ext)
    (hst : J.stAt w seen front = .ok (s.st, s.frame.group)) (u : Fin (2 * J.pub.par.k + 1) → E)
    (ca : CsAll (closeCarries J.pub)) (R : GroupData) (hr : J.rows w front ca = .ok R)
    (hf : rowsFit s.st D.G R = true)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList (askWords
      (fun o => wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main)
      (fun o => wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask)))
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : rR.length = J.pub.par.k) (hE : ProofFile.Honest.K10.YesFree.Shaped 1 rE)
    (hR : ∀ r ∈ rR, ProofFile.Honest.K10.YesFree.Shaped 2 r) (φ : st.cFr.J → GE)
    (hP : Pairs st st.Z.l (coefU (st.h + st.g) (uOfBook (st.h + st.g) fun i =>
      (u (Fin.cast (by rw [H.stretch, nk]) i)).triple)) φ)
    (hsend : ∀ A, closeAsk J w seen front ⟨[t], [], [], none⟩ u ca = .ok (some A) →
      (sentOf rE).getD 0 zeroE = foldWords.sigma A ∧ ∀ i (h : i < rR.length),
        (sentOf rR[i]).getD 0 zeroE =
            (foldWords.round A (drawnOf rE) ((rR.take i).map drawnOf)).1 ∧
          (sentOf rR[i]).getD 1 zeroE =
            (foldWords.round A (drawnOf rE) ((rR.take i).map drawnOf)).2) :
    ∃ s', ((kind (Cl := Cl)) J.pub.par).decide s (⟨[], ⟨[t], [], [], none⟩⟩ :: rE :: rR) gs =
        .ok s' ∧
      ∑ j, vecS st s'.frame.rows j *
            foldMsg st (msgOf st (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords
                (fun o => wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main)
                (fun o => wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask)))) φ
              (sPt 2 (st.h + st.g) (ptK (st.h + st.g) (lst ((rR.map drawnOf).map (·.triple))))) j +
          keptVal (keptLen (D.S1 s))
            (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (askWords
                (fun o => wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main)
                (fun o => wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask))).kept
            s'.frame.rows.kept = readE s'.frame.rows.target := by
  obtain ⟨row, hrow, hA⟩ := ask_of_base J H hh w seen front t hst u ca R hr hf
  obtain ⟨hσ, hq⟩ := hsend _ hA
  have hσ' : (sentOf rE).getD 0 zeroE = foldSigmaE J.pub.par.k u := hσ
  have ek : J.pub.par.k = st.h + st.g := H.stretch.trans nk
  have eh : J.pub.par.h = st.h := hh.trans nh
  refine tables_law (Cl := Cl) H st nk nh nl nz _ _ hs ⟨[], ⟨[t], [], [], none⟩⟩ rE rR gs
    (by rw [List.length_cons, List.length_cons, hl]; omega)
    ⟨⟨⟨[], rfl, rfl⟩, ⟨t, rfl⟩, rfl, rfl⟩, hE, hR⟩ φ _ hP (hσ'.trans (sigma_cast ek u))
    fun row' h' i h => ?_
  obtain rfl : row = row' := Option.some.inj (hrow.symm.trans h')
  obtain ⟨q1, q2⟩ := hq i h
  have e := round_cast ek J.pub.par.h
    (row.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)) row.d
    (closeMain (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
      wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main)
    (closeMask (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
      wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask)
    (closeKept (D.S1 s) row.kept fun o =>
      wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main)
    u (drawnOf rE) ((rR.take i).map drawnOf)
  have e2 := e.trans (by rw [eh])
  exact ⟨q1.trans (congrArg Prod.fst e2), q2.trans (congrArg Prod.snd e2)⟩

end Base

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.read_addUp
#print axioms ProofFile.Honest.K10.read_foldl_add
#print axioms ProofFile.Honest.K10.mainWeight_int
#print axioms ProofFile.Honest.K10.maskWeight_int
#print axioms ProofFile.Honest.K10.askWords
#print axioms ProofFile.Honest.K10.askWords_padded
#print axioms ProofFile.Honest.K10.wordAt_shapes
#print axioms ProofFile.Honest.K10.wordAt_begun
#print axioms ProofFile.Honest.K10.rowsFit_length
#print axioms ProofFile.Honest.K10.rowsAt_member
#print axioms ProofFile.Honest.K10.weights_none
#print axioms ProofFile.Honest.K10.layoutOf_members
#print axioms ProofFile.Honest.K10.weight_member
#print axioms ProofFile.Honest.K10.read_closeMain
#print axioms ProofFile.Honest.K10.read_closeMask
#print axioms ProofFile.Honest.K10.vec_map
#print axioms ProofFile.Honest.K10.idx_lt
#print axioms ProofFile.Honest.K10.vecIn_tables
#print axioms ProofFile.Honest.K10.vecG_written
#print axioms ProofFile.Honest.K10.read_closeKept
#print axioms ProofFile.Honest.K10.base_row
#print axioms ProofFile.Honest.K10.kept_on_member
#print axioms ProofFile.Honest.K10.tables_law
#print axioms ProofFile.Honest.K10.ask_of_base
#print axioms ProofFile.Honest.K10.sigma_cast
#print axioms ProofFile.Honest.K10.round_cast
#print axioms ProofFile.Honest.K10.ask_law
