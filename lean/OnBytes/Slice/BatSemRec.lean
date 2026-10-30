-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BatSemRec.lean: the batching behind the written link over `Sz.lkR`,
in the field, and with it the hypothesis on the rounds after the fifth (`ClosesR`,
OnBytes/Slice/LinkSoundRec.lean) from the statements of the blocks.

After the link's five rounds the verifier holds rows, linear claims on the two folded rows' oracle
messages. OnBytes/Slice/BatSem.lean lists them over `Sz.lk` (`IsRows`): one equality
row, a sample row for each of the two members, and a row of the tables' generator matrix for each
drawn position. The library's last joint over `Sz.lkR` asks besides THE RECORD'S ROW OF EACH FOLD
(`LdIx.RecRow`, Cb/Ld/LdFoldEq.lean): for each answer s of a row's sample, the sample of the folded
row's message part at the record's seed is the fold of the record's answers. Here they are rows like
the others: the library's form `recF` (Cb/Ld/LdLinkClose.lean) on the member's entries, 0 on the
other member's, with the target `LdIx.tgt`.

THE ROWS' NUMBERS ARE LETTERS (`RowNo`). The proof reads of each row its own equation and never an
order, so nothing is asked but that each number is below the number n of rows that are batched. Two
rows may even have one number, if their equations agree. Whoever ties this to a program takes the
order in which the program hands the rows to its test; `RowNo.port` has that order (a theorem in
OnBytes/Slice/BlkLinkHeadRec.lean: `LinkRanR.runRows_eq`).

The text of `rows_back_semR`, `batErrR`, `sumStmR`, `bat_block_semR` is that of `rows_back_sem`,
`batErr`, `sumStm`, `bat_block_sem` (OnBytes/Slice/BatSem.lean), that of `BatSemR`, `batSemR_of` is
that of `BatSem`, `batSem_of` (OnBytes/Slice/ChainSem.lean), and that of `closes_manyR` is that of
`closes_many` (OnBytes/Slice/ManyCloses.lean), cut by a program: the link over the format with a
sample map for the link, the letters for the rows' numbers, and two new cases for the record's rows
where that proof has "there is no answer".

Main definitions: `RowNo`, `RowNo.port`, `IsRowsR`, `batErrR`, `sumStmR`, `BatSemR`.
Main theorems: `rows_back_semR`, `bat_block_semR`, `batSemR_of`, `closes_manyR`.

Not claimed. THIS IS NO PROOF OF SOUNDNESS. `closes_manyR` asks the blocks' statements
(`Chain.Holds`), that the readings are the rows (`IsRowsR`) and the word (`WordTie`), and that a yes
of the written decision gives the chain's yes in the field (`hsem`): none is shown of any decision,
program or file here. That a program batches the record's rows at all, and in which order, is not
shown here (OnBytes/Slice/ManyBlkWrittenRec.lean and the files beneath it show it of the program's
link). That targets and vectors meet `IsRowsR` at all is shown in OnBytes/Slice/RowsXRec.lean, not
here. The list of the group's code is a letter, and `batSemR_of` asks that the radius be at most the
members' own and below the main code's distance (`SemOK`). Nothing on the sizes of the error counts,
on where a record's seed comes from, or on how often a record fails to single one table out.

-/
import OnBytes.Slice.LinkSoundRec
import OnBytes.Slice.ManyCloses
import Cb.Ld.LdLinkClose

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks

/-- **The numbers of the rows**, and the number n of rows that are batched: the equality row, the
two members' sample rows, the rows of the drawn positions of the first table and of the copy, and
the record's rows of the first table (false) and of the copy (true). Each number is below n. -/
structure RowNo (S : Sz) (Z : Sample GE S.En) where
  n : ℕ
  eq : ℕ
  sm : Bool → ℕ
  c0 : Fin S.P.nu0 → ℕ
  c1 : Fin S.P.nuj → ℕ
  rc : Bool → Z.S → ℕ
  eq_lt : eq < n
  sm_lt : ∀ a, sm a < n
  c0_lt : ∀ i, c0 i < n
  c1_lt : ∀ i, c1 i < n
  rc_lt : ∀ a s, rc a s < n

/-- **The numbers as the program's batching numbers the rows** (OnBytes/Iop/Ground.lean, `beginRun`:
the plain rows as they were created, the members' sample rows, the generator rows as they were
created), for a sample whose answers are numbered below s by num: the first table's record's rows,
the copy's, the equality row, the two members' sample rows (one a member, as the link's family has
it), the first table's drawn positions' rows, the copy's. At s = 0 these are the numbers of `IsRows`
(OnBytes/Slice/BatSem.lean). The order in which the rows are CREATED is another: there the equality
row comes last. num is meant to be one to one; else two of a record's rows have one number. That the
program's test takes the rows in in this order, with these targets and coefficients, is shown in
OnBytes/Slice/BlkLinkRanRec.lean, BlkLinkHeadRec.lean and BlkLinkJoinRec.lean, not here. -/
def RowNo.port (S : Sz) (Z : Sample GE S.En) (s : ℕ) (num : Z.S → Fin s) : RowNo S Z where
  n := 2 * s + 3 + (S.P.nu0 + S.P.nuj)
  eq := 2 * s
  sm := fun a => 2 * s + 1 + a.toNat
  c0 := fun i => 2 * s + 3 + i.val
  c1 := fun i => 2 * s + 3 + S.P.nu0 + i.val
  rc := fun a x => (if a then s else 0) + (num x).val
  eq_lt := by omega
  sm_lt := fun a => by cases a <;> simp <;> omega
  c0_lt := fun i => by have := i.isLt; omega
  c1_lt := fun i => by have := i.isLt; omega
  rc_lt := fun a x => by have := (num x).isLt; cases a <;> simp <;> omega

/-- **The rows, in the field.** As `IsRows` (OnBytes/Slice/BatSem.lean), at the
numbers N, and besides the record's rows: for each answer s, on the first table's member the
library's form `recF` at the first record's seed, with the fold of the first record's answers as
target; the like for the copy. Nothing is asked on rows of the group's table that no member has, and
nothing at a number that is no row's. On the mask row the vectors are 0. -/
structure IsRowsR (S : Sz) (Z : Sample GE S.En) (t : ℕ) (N : RowNo S Z) (x : (S.lkR Z).X4)
    (tg : ℕ → GE) (vs : ℕ → (S.sg t).cIn.J → GE) : Prop where
  mask : ∀ b j, vs b (.inr j) = 0
  eqT : tg N.eq = 0
  eq0 : ∀ j, vs N.eq (atJ S t false j) = (S.lkR Z).layF false S.putAt x.2 j
  eq1 : ∀ j, vs N.eq (atJ S t true j) = -(S.lkR Z).layF true S.putAt x.2 j
  smT : ∀ a : Bool, tg (N.sm a) = (x.1.1.2 a).2 ()
  smS : ∀ (a : Bool) j, vs (N.sm a) (atJ S t a j) = (S.fam.om a).Z.mat (x.1.1.2 a).1 () j
  smO : ∀ (a : Bool) j, vs (N.sm a) (atJ S t (!a) j) = 0
  c0T : ∀ i : Fin S.P.nu0, tg (N.c0 i) = x.1.2.1.2 i
  c0S : ∀ (i : Fin S.P.nu0) j,
    vs (N.c0 i) (atJ S t false j) = (S.lkR Z).colF false S.putAt (x.1.2.1.1 i) j
  c0O : ∀ (i : Fin S.P.nu0) j, vs (N.c0 i) (atJ S t true j) = 0
  c1T : ∀ i : Fin S.P.nuj, tg (N.c1 i) = x.1.2.2.2 i
  c1S : ∀ (i : Fin S.P.nuj) j,
    vs (N.c1 i) (atJ S t true j) = (S.lkR Z).colF true S.putAt (x.1.2.2.1 i) j
  c1O : ∀ (i : Fin S.P.nuj) j, vs (N.c1 i) (atJ S t false j) = 0
  r0T : ∀ s : Z.S, tg (N.rc false s) = (S.ixR Z).tgt x.1.1.1.1.1 x.1.1.1.2 s
  r0S : ∀ (s : Z.S) j,
    vs (N.rc false s) (atJ S t false j) = (S.lkR Z).recF false S.putAt s x.1.1.1.1.1.1 j
  r0O : ∀ (s : Z.S) j, vs (N.rc false s) (atJ S t true j) = 0
  r1T : ∀ s : Z.S, tg (N.rc true s) = (S.ixR Z).tgt x.1.1.1.1.2 x.1.1.1.2 s
  r1S : ∀ (s : Z.S) j,
    vs (N.rc true s) (atJ S t true j) = (S.lkR Z).recF true S.putAt s x.1.1.1.1.2.1 j
  r1O : ∀ (s : Z.S) j, vs (N.rc true s) (atJ S t false j) = 0

/-- If the statement after the link's five rounds has no witness, then no message on the group's
tables is near the word and meets all rows. -/
theorem rows_back_semR (S : Sz) (Z : Sample GE S.En) (N : RowNo S Z) (t e d : ℕ) (hk : SemOK S e d)
    (d2 : PQ.RD) (o : (wRound d2).Orc)
    (f : (S.sg t).cIn.Word) (hf : WordTie S t d2 o f) (x : (S.lkR Z).X4)
    (hno : ∀ w, ¬ (S.lkR Z).j4.cf.relR (x, wordsOf S d2 o) w)
    (tg : ℕ → GE) (vs : ℕ → (S.sg t).cIn.J → GE) (hr : IsRowsR S Z t N x tg vs) :
    ∀ w, ¬ ConL (S.sg t).cIn.N e
      (Slf.All fun _ : Fin N.n => (Slf.idf (E := GE) (J := (S.sg t).cIn.J)))
      ((fun b => tg b.val, fun b => vs b.val), f) w := by
  rintro w ⟨hn, hall⟩
  have h0 : FreeZero S t w.1 := free_zero S t e d hk d2 o f hf w hn
  -- each row, as a sum over the two members' shares, beginning with the member a
  have hval : ∀ (b : ℕ) (a : Bool), b < N.n →
      ∑ j : S.MJ, vs b (atJ S t a j) * w.1 (atJ S t a j) +
        ∑ j : S.MJ, vs b (atJ S t (!a) j) * w.1 (atJ S t (!a) j) = tg b := by
    intro b a hb
    rw [← sum_bool_at a fun a => ∑ j : S.MJ, vs b (atJ S t a j) * w.1 (atJ S t a j),
      ← val_split S t (vs b) w.1 (hr.mask b) h0]
    exact hall ⟨b, hb⟩
  -- a form that is given on some entries, at a member's share
  have hpush : ∀ (a : Bool) {St I : Type} [Fintype I] (φ : I → ((S.lkR Z).N.om a).C.J)
      (c : St → I → GE) (st : St),
      ∑ j, Slf.push φ c st j * w.1 (atJ S t a j) = ∑ i, c st i * w.1 (atJ S t a (φ i)) :=
    fun a St I _ φ c st => ldForm_push GE St I ((S.lkR Z).N.om a).C.J φ c st fun j => w.1
      (atJ S t a j)
  by_cases hon : (S.lkR Z).j4.on (x, wordsOf S d2 o)
  swap
  · exact hno (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)) (Or.inr hon)
  refine hno (fun a => (fun j => w.1 (atJ S t a j), fun q => w.2 (atQ S t a q)),
    (fun _ _ => 0, fun _ _ => 0)) (Or.inl ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩)
  · -- each member decodes, with its sample, to its share
    intro a
    refine (sig_dec_good GE (S.fam.om a) (wordsOf S d2 o a) (x.1.1.2 a).1 (hon a) (x.1.1.2 a).2
      _).2 ⟨mem_inList S t e d hk d2 o f hf w hn a, ?_⟩
    funext u
    have h := hval (N.sm a) a (N.sm_lt a)
    have hz : ∑ j : S.MJ, vs (N.sm a) (atJ S t (!a) j) * w.1 (atJ S t (!a) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hr.smO a j, zero_mul]
    rw [hz, add_zero, hr.smT a] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun j _ => by rw [hr.smS a j]
  · -- the record's rows of the first table
    funext s
    have h := hval (N.rc false s) false (N.rc_lt false s)
    have hz : ∑ j : S.MJ, vs (N.rc false s) (atJ S t (!false) j) * w.1 (atJ S t (!false) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (N.rc false s) (atJ S t (!false) j) = 0 from hr.r0O s j, zero_mul]
    rw [hz, add_zero, hr.r0T s] at h
    refine Eq.trans ?_ h
    refine ((hpush false (fun j => S.putAt ((S.ixR Z).pl j)) (fun ρ j => Z.mat ρ s j)
      x.1.1.1.1.1.1).symm.trans ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hr.r0S s j]; rfl
  · -- the first table's draws
    intro i
    have h := hval (N.c0 i) false (N.c0_lt i)
    have hz : ∑ j : S.MJ, vs (N.c0 i) (atJ S t (!false) j) * w.1 (atJ S t (!false) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (N.c0 i) (atJ S t (!false) j) = 0 from hr.c0O i j, zero_mul]
    rw [hz, add_zero, hr.c0T i] at h
    refine Eq.trans ?_ h
    refine ((hpush false S.putAt (fun x k => (S.ixR Z).G x k) (x.1.2.1.1 i)).symm.trans ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hr.c0S i j]; rfl
  · -- the record's rows of the copy
    funext s
    have h := hval (N.rc true s) true (N.rc_lt true s)
    have hz : ∑ j : S.MJ, vs (N.rc true s) (atJ S t (!true) j) * w.1 (atJ S t (!true) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (N.rc true s) (atJ S t (!true) j) = 0 from hr.r1O s j, zero_mul]
    rw [hz, add_zero, hr.r1T s] at h
    refine Eq.trans ?_ h
    refine ((hpush true (fun j => S.putAt ((S.ixR Z).pl j)) (fun ρ j => Z.mat ρ s j)
      x.1.1.1.1.2.1).symm.trans ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hr.r1S s j]; rfl
  · -- the copy's draws
    intro i
    have h := hval (N.c1 i) true (N.c1_lt i)
    have hz : ∑ j : S.MJ, vs (N.c1 i) (atJ S t (!true) j) *
        w.1 (atJ S t (!true) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (N.c1 i) (atJ S t (!true) j) = 0 from hr.c1O i j, zero_mul]
    rw [hz, add_zero, hr.c1T i] at h
    refine Eq.trans ?_ h
    refine ((hpush true S.putAt (fun x k => (S.ixR Z).G x k) (x.1.2.2.1 i)).symm.trans ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hr.c1S i j]; rfl
  · -- the equality row
    have h := hval N.eq false N.eq_lt
    have e0 : ∑ j : S.MJ, vs N.eq (atJ S t false j) * w.1 (atJ S t false j) =
        ∑ a : S.Lay, Alg.eqk x.2 ((S.lwR Z).pl a) *
          w.1 (atJ S t false (S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))) :=
      (Finset.sum_congr rfl fun j _ => by rw [hr.eq0 j]; rfl).trans
        (hpush false (fun a => S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))
          (fun φ a => Alg.eqk φ ((S.lwR Z).pl a)) x.2)
    have e1 : ∑ j : S.MJ, vs N.eq (atJ S t (!false) j) * w.1 (atJ S t (!false) j) =
        -∑ a : S.Lay, Alg.eqk x.2 ((S.lwR Z).pl a) *
          w.1 (atJ S t true (S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))) := by
      rw [← hpush true (fun a => S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))
        (fun φ a => Alg.eqk φ ((S.lwR Z).pl a)) x.2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show vs N.eq (atJ S t (!false) j) = _ from hr.eq1 j, neg_mul]; rfl
    rw [e0, e1, hr.eqT, ← sub_eq_add_neg, ← Finset.sum_sub_distrib] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun a _ => mul_sub _ _ _

/-! ## The block, in the field -/

/-- The error count of the written round: the bound on the lists of the group's code, times the
number of rows less one, times the number in the law of the format's sampler. -/
def batErrR {S : Sz} {Z : Sample GE S.En} (N : RowNo S Z) (L : ℕ) (dA : PQ.RD) : ℕ :=
  L * (N.n - 1) * (bsRound .two dA.entry dA.kind).w

/-- The rows under the powers of θ: the target and the vector. -/
def sumStmR {S : Sz} {Z : Sample GE S.En} (N : RowNo S Z) (t : ℕ) (tg : ℕ → GE) (vs : ℕ →
    (S.sg t).cIn.J → GE) (θ : GE) :
    GE × ((S.sg t).cIn.J → GE) :=
  (∑ b : Fin N.n, θ ^ b.val * tg b.val, fun j => ∑ b : Fin N.n, vs b.val j * θ ^ b.val)

/-- The round in which all rows become one is taken off, in the field. x: the statement after the
link's five rounds; o: the oracle of the link's second round; f: the word on the stage's rows; tg,
vs: the rows' targets and vectors. -/
theorem bat_block_semR (S : Sz) (Z : Sample GE S.En) (N : RowNo S Z) (t₀ e d L : ℕ)
    (hk : SemOK S e d)
    (hL : (S.sg t₀).cIn.ListAt e L) (d2 dA : PQ.RD) (hA : SendsDraws dA 0 1 0 0)
    (t : Shape) (εt : Err t) (o : (wRound d2).Orc) (f : (S.sg t₀).cIn.Word)
    (hf : WordTie S t₀ d2 o f) (x : (S.lkR Z).X4)
    (hno : ∀ w, ¬ (S.lkR Z).j4.cf.relR (x, wordsOf S d2 o) w)
    (tg : ℕ → GE) (vs : ℕ → (S.sg t₀).cIn.J → GE) (hr : IsRowsR S Z t₀ N x tg vs)
    (bad : Tr (wRound dA :: t) → Prop)
    (hp : ∀ m c τ, GChal.pass (b := dA.entry.work) c = false → bad (m, c, τ))
    (H : ∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal),
      (∀ w, ¬ (S.sg t₀).RIn e (sumStmR N t₀ tg vs (gOne _ (valsOf dA c)), f) w) →
      Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound dA :: t) (batErrR N L dA, εt) bad :=
  peel_draw (Evader.powers GE N.n).D (batNx (Evader.powers GE N.n).ze)
    (know_bat (S.sg t₀).cIn (fun _ : Fin N.n => (S.sg t₀).cIn.J → GE)
      (fun _ => Slf.idf) (Evader.powers GE N.n) e L (ok_powers GE N.n) hL)
    dA (gOne _) hA.gOne_inj hA.logN t εt
    ((fun b => tg b.val, fun b => vs b.val), f)
    (rows_back_semR S Z N t₀ e d hk d2 o f hf x hno tg vs hr) bad hp fun m c hB => H m c hB

/-- The batching is taken off, with the error count εa. -/
def BatSemR (S : Sz) (Z : Sample GE S.En) (N : RowNo S Z) (t₀ e : ℕ) (d2 dA : PQ.RD) (εa : ℕ) :
    Prop :=
  ∀ (t : Shape) (εt : Err t) (o : (wRound d2).Orc) (f : (S.sg t₀).cIn.Word),
    WordTie S t₀ d2 o f →
    ∀ x : (S.lkR Z).X4, (∀ w, ¬ (S.lkR Z).j4.cf.relR (x, wordsOf S d2 o) w) →
    ∀ (tg : ℕ → GE) (vs : ℕ → (S.sg t₀).cIn.J → GE), IsRowsR S Z t₀ N x tg vs →
    ∀ bad : Tr (wRound dA :: t) → Prop,
    (∀ m c τ, GChal.pass (b := dA.entry.work) c = false → bad (m, c, τ)) →
    (∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal),
      (∀ w, ¬ (S.sg t₀).RIn e (sumStmR N t₀ tg vs (gOne _ (valsOf dA c)), f) w) →
      Doomed t εt fun b => bad (m, c, b)) →
    Doomed (wRound dA :: t) (εa, εt) bad

/-- The batching, from a bound L on the lists of the group's code at the radius e. -/
theorem batSemR_of (S : Sz) (Z : Sample GE S.En) (N : RowNo S Z) (t₀ e d L : ℕ)
    (hk : SemOK S e d) (hL : (S.sg t₀).cIn.ListAt e L) (d2 dA : PQ.RD)
    (hA : SendsDraws dA 0 1 0 0) : BatSemR S Z N t₀ e d2 dA (batErrR N L dA) :=
  fun t εt o f hf x hno tg vs hr bad hp H =>
    bat_block_semR S Z N t₀ e d L hk hL d2 dA hA t εt o f hf x hno tg vs hr bad hp H

section
variable {S : Sz} {Z : Sample GE S.En} (N : RowNo S Z) (r : (S.lkR Z).X0) {t₀ : ℕ}
  (d1 d2 d3 d4 d5 dA : PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool)

/-- The rounds after the fifth close the link at the pair of records r (`ClosesR`), where they are
the batching's round dA and the rounds of a chain c from the link's first stage on, for any decision
whose yes in the written protocol gives the chain's yes in the field (`hsem`): at the claim that the
batching makes of the rows, and at the first tree read by w1, z1, g1. Asked besides: the batching's
statement at the chain's first radius, the blocks' statements, and `IsRowsR` and `WordTie` of the
readings. -/
theorem closes_manyR (c : Chain (S.sg t₀)) (εa : ℕ)
    (rows : (S.lkR Z).X4 → (ℕ → GE) × (ℕ → (S.sg t₀).cIn.J → GE))
    (w1 : (wRound d2).Orc → (S.sg t₀).cIn.Word) (z1 : (wRound d2).Orc → (S.sg t₀).cFr.Word)
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (hBat : BatSemR S Z N t₀ c.rad d2 dA εa) (hc : c.Holds)
    (hrows : ∀ x, IsRowsR S Z t₀ N x (rows x).1 (rows x).2) (hw1 : ∀ o, WordTie S t₀ d2 o (w1 o))
    (hsem : ∀ (y : (S.lkR Z).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true →
      c.Acc (sumStmR N t₀ (rows (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rows (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        (w1 m2.1) (z1 m2.1) (g1 m2.1) b) :
    ClosesR S Z r d1 d2 d3 d4 d5 (dA :: c.rds) xs dec (εa, c.errL) := by
  intro y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 hno
  have hpass : ∀ mA cA (τ : Tr (PQ.uL (ckP .two) c.rds)),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τ) = true →
      GChal.pass (b := dA.entry.work) cA = true ∧
        PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true := by
    intro mA cA τ hacc
    have hp : PQ.passSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: dA :: c.rds)
        (PQ.rhoSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: dA :: c.rds)
          (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τ)) = true := by
      have h4 : (PQ.passSL (ckP .two) _ _ && _ && _ && _) = true := hacc
      simp only [Bool.and_eq_true] at h4
      exact h4.1.1.1
    simp only [PQ.passSL, PQ.rhoSL, Bool.and_eq_true] at hp
    exact ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩
  refine hBat _ c.errL m2.1 (w1 m2.1) (hw1 m2.1)
    (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 hno
    _ _ (hrows _) _ ?_ ?_
  · intro mA cA τ hw
    refine Bool.eq_false_iff.2 fun ha => ?_
    rw [(hpass mA cA τ ha).1] at hw
    cases hw
  · intro mA cA h0
    exact chain_many_list c hc _ (w1 m2.1) (z1 m2.1) (g1 m2.1) h0
      (fun τ => (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τ))
      fun b hb => ⟨hsem y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hb, (hpass mA cA _ hb).2⟩

end

end OnBytes.Slice
