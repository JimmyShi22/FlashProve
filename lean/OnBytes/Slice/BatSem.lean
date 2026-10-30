-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BatSem.lean: the round of the written link in which all rows become one, in the field.

After the link's first five rounds (OnBytes/Slice/CorePeel.lean) the verifier holds linear claims,
rows, on the two folded rows that the prover sent: one equality row, one sample row for each of the
two, and one row for each drawn column of a stored table. In the sixth round it draws one element θ
and goes on with one row, the sum of all rows under the powers of θ. That row is a claim on the
tables of the first stage of the proximity test (OnBytes/Slice/Stage.lean).

This file takes the sixth round off: it shows, under the conditions named below, that the prover has
lost before the round. "Has lost" is the library's `Iop.Doomed`: in each round, whatever the prover
sends, all but a counted number of verifier messages leave it lost, and at the end a given goal
holds. The written link is the interactive protocol in the types of the format, that is, of the
library's folder Fmt/, which has the verifier's decision as functions on machine words. Here
everything is read in the field: a row is any target with any vector on the entries of the stage's
tables. No function of the format on claims occurs, so the result serves every written verifier
whose rows are these.

The stage (`Sz.sg`). Each of the two oracle messages, the members, has R rows. A member takes a
block of 2^aR rows of the stage's main table: the first table's member from row 0 on, the copy's
from row 2^aR on. Rows R and above of a block were sent by nobody and count as zero words. The stage
has one carried mask row, which nobody sent either.

The result, `bat_block_sem`. Let the statement that the library's verifier holds after the five
rounds have no witness in the relaxed relation of the link's last joint. Let the rows be the
library's on each member's entries (`IsRows`), and let the word on the stage's rows be what was sent
(`WordTie`). Then the prover has lost before the sixth round, if the goal holds wherever the round's
test of work (its bits of proof of work) fails, and if the prover has lost after the round whenever
the combined row (`sumStm`) has no witness in the stage's relaxed relation.

How it is proved. The library's batching of several rows into one (OnBytes/Slice/CloseKnow.lean:
`know_bat`) is used on the stage's own code, with the rows as vectors and the powers of one
challenge as coefficients. What is left is the way back (`rows_back_sem`): a message on the stage's
tables that is near the word and meets all rows gives a witness for the link's last joint. Its
parts: the message is 0 on the rows that nobody sent (`free_zero`); each member's share is in the
member's list (`mem_inList`); a row's value is the sum of its values on the two shares
(`val_split`); a member without a collision decodes to the one member of its list that has its
sample's answer.

What is asked (`SemOK`): the radius e is at most the members' own and below the number d; the main
code has the distance d. The last is needed because a sample row has weights on the rows that
nobody sent. Also a bound L on the lists of the stage's code at the radius e.

The error count (`batErr`): L times the number of rows less one, times the number in the law of the
format's sampler.

Main definitions: `Sz.sg`, `Sz.nRows`, `memRow`, `atJ`, `SemOK`, `WordTie`, `IsRows`, `sumStm`,
`batErr`.

Main theorems: `peel_draw`, `rows_back_sem`, `bat_block_sem`.

Not claimed. No bound on a list, no distance of a code. Nothing on an honest prover. That a given
verifier's rows meet `IsRows` and its columns `WordTie`: OnBytes/Slice/BlockBat.lean shows it of the
format's, under hypotheses of its own.
-/
import OnBytes.Slice.Stage
import OnBytes.Slice.CloseKnow
import OnBytes.Slice.Cells
import OnBytes.Slice.RoundsMaps
import Cb.Ld.LdSigProofs
import Cb.Ld.LdLinkClose

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## A round in which the library's verifier only draws -/

/-- A round in which the verifier draws a value and reads nothing is taken off: the library's
knowledge soundness of such a round (hK) is carried to the written round d, whose drawn values g
reads injectively. -/
theorem peel_draw {X X' W : Type} {Ex : ExtSpec} (D : Type) [Fintype D] [Nonempty D]
    (nx : X → D → X') {RA : X × Ex.Str → W → Prop} {RB : X' × Ex.Str → W → Prop}
    {ext : X × Ex.Str → Tr (IOR.draw D nx Ex).red.shape → W → W} {e : ℕ}
    (hK : (IOR.draw D nx Ex).red.Know (fun _ => True) RA RB ext ((e, ()) : ℕ × Unit))
    (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → D) (hg : Function.Injective g)
    (hlog : d.entry.logN ≤ 64) (t : Shape) (εt : Err t) (a : X × Ex.Str) (hno : ∀ w, ¬ RA a w)
    (bad : Tr (wRound d :: t) → Prop)
    (hp : ∀ m c τ, GChal.pass (b := d.entry.work) c = false → bad (m, c, τ))
    (H : ∀ m c, (∀ w, ¬ RB (nx a.1 (g (valsOf d c)), a.2) w) →
      Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound d :: t) (e * (bsRound .two d.entry d.kind).w, εt) bad := by
  refine peel (s := [wRound d]) (t := t) (IOR.draw D nx Ex).red hK a trivial hno
    (one (fun _ => ((), ())) (chalTo d g)) (((bsRound .two d.entry d.kind).w, ()) : ℕ × Unit)
    (one_fib _ _ _ (chalTo_fib d g hg hlog)) εt bad ?_ ?_
  · rintro ⟨m, c, ⟨⟩⟩ hτ0
    have hτ := (one_tr (r' := IOR.drawRound D) (fun _ => ((), ())) (chalTo d g) m c).symm.trans hτ0
    have hc : chalTo d g c = none := by
      cases h : chalTo d g c with
      | none => rfl
      | some c' => rw [h] at hτ; cases hτ
    exact doomed_of_all _ _ _ fun b => hp m c b (chalTo_none d g c hc)
  · rintro ⟨m, c, ⟨⟩⟩ τ' hτ0 hno'
    have hτ := (one_tr (r' := IOR.drawRound D) (fun _ => ((), ())) (chalTo d g) m c).symm.trans hτ0
    cases h : chalTo d g c with
    | none => rw [h] at hτ; cases hτ
    | some c' =>
      rw [h] at hτ
      obtain rfl : (((), ()), c', ()) = τ' := Option.some.inj hτ
      obtain rfl := chalTo_some d g c c' h
      exact H m c fun w => hno' _ w rfl

/-! ## The group's stage and the two members in it -/

/-- The stage of the link's group: the two members' blocks of 2^aR main rows side by side, and
one carried mask row, which nobody sent. -/
abbrev Sz.sg (S : Sz) (t : ℕ) : Sg := ⟨S.P.C, S.P.Z, 0, S.P.aR + 1, t⟩

/-- The number of rows that are combined: the equality row, two sample rows, the draws' rows. -/
def Sz.nRows (S : Sz) : ℕ := 3 + (S.P.nu0 + S.P.nuj)

/-- The first row of member a's block in the group's table. -/
def Sz.blk (S : Sz) (a : Bool) : ℕ := if a then 2 ^ S.P.aR else 0

/-- The vertex of row i of member a's block. -/
def memRow (S : Sz) (t : ℕ) (a : Bool) (i : ℕ) : Fin ((S.sg t).h + (S.sg t).g) → Bool :=
  fun u => (S.blk a + i).testBit u.val

/-- An entry of member a's message, as an entry of the message on the group's tables. -/
def atJ (S : Sz) (t : ℕ) (a : Bool) : S.MJ → (S.sg t).cIn.J
  | .inl x => .inl (memRow S t a x.1.val, x.2)
  | .inr x => x.1.elim

/-- An entry of member a's tails, as an entry of the tails on the group's tables. -/
def atQ (S : Sz) (t : ℕ) (a : Bool) : (S.fam.om a).C.Q → (S.sg t).cIn.Q
  | .inl x => .inl (memRow S t a x.1.val, x.2)
  | .inr x => x.1.elim

/-- What is asked of the radius e and the number d: e is at most the members' own radius; a row
of the main code has distance d; e is below d. -/
structure SemOK (S : Sz) (e d : ℕ) : Prop where
  rad : e ≤ S.eU
  dist : (ldOf S.P.C S.P.C.a).Dist d
  lt : e < d

/-- The word on the group's rows is the written oracle's: row i of member a's block holds the
member's symbol number i, and 0 if the member has no such row. Nothing is asked of the mask row. -/
structure WordTie (S : Sz) (t : ℕ) (d2 : PQ.RD) (o : (wRound d2).Orc) (f : (S.sg t).cIn.Word) :
    Prop where
  sent : ∀ (x : Fin (2 ^ S.P.C.a)) (a : Bool) (i : ℕ), i < S.P.R →
    f (.inl x) (memRow S t a i, ()) = symAt d2 o x.val ((if a then S.P.R else 0) + i)
  free : ∀ (x : Fin (2 ^ S.P.C.a)) (a : Bool) (i : ℕ), S.P.R ≤ i → i < 2 ^ S.P.aR →
    f (.inl x) (memRow S t a i, ()) = 0

/-- The rows, in the field. tg b and vs b are the target and the vector of row number b on the
group's tables; x is the statement that the library's verifier holds after the link's five rounds.
On each member's entries the vectors are the library's forms: the equality row (number 0) with
opposite signs on the two members; the members' sample rows (1 and 2); a row of the tables'
generator matrix for each drawn position (from 3 on, the first table's first). Nothing is asked on
rows of the group's table that no member has. On the mask row the vectors are 0. -/
structure IsRows (S : Sz) (t : ℕ) (x : S.lk.X4) (tg : ℕ → GE) (vs : ℕ → (S.sg t).cIn.J → GE) :
    Prop where
  mask : ∀ b j, vs b (.inr j) = 0
  eqT : tg 0 = 0
  eq0 : ∀ j, vs 0 (atJ S t false j) = S.lk.layF false S.putAt x.2 j
  eq1 : ∀ j, vs 0 (atJ S t true j) = -S.lk.layF true S.putAt x.2 j
  smT : ∀ a : Bool, tg (1 + a.toNat) = (x.1.1.2 a).2 ()
  smS : ∀ (a : Bool) j, vs (1 + a.toNat) (atJ S t a j) = (S.fam.om a).Z.mat (x.1.1.2 a).1 () j
  smO : ∀ (a : Bool) j, vs (1 + a.toNat) (atJ S t (!a) j) = 0
  c0T : ∀ i : Fin S.P.nu0, tg (3 + i.val) = x.1.2.1.2 i
  c0S : ∀ (i : Fin S.P.nu0) j,
    vs (3 + i.val) (atJ S t false j) = S.lk.colF false S.putAt (x.1.2.1.1 i) j
  c0O : ∀ (i : Fin S.P.nu0) j, vs (3 + i.val) (atJ S t true j) = 0
  c1T : ∀ i : Fin S.P.nuj, tg (3 + S.P.nu0 + i.val) = x.1.2.2.2 i
  c1S : ∀ (i : Fin S.P.nuj) j,
    vs (3 + S.P.nu0 + i.val) (atJ S t true j) = S.lk.colF true S.putAt (x.1.2.2.1 i) j
  c1O : ∀ (i : Fin S.P.nuj) j, vs (3 + S.P.nu0 + i.val) (atJ S t false j) = 0

/-- The message is 0 on the rows that no member has. -/
def FreeZero (S : Sz) (t : ℕ) (m : (S.sg t).cIn.J → GE) : Prop :=
  ∀ (a : Bool) (i : ℕ) (j : Fin S.P.C.l), S.P.R ≤ i → i < 2 ^ S.P.aR →
    m (.inl (memRow S t a i, j)) = 0

/-! ## From a witness on the group's tables to the two members -/

/-- A code word near a word that is 0 on a row is 0 on that row. -/
theorem free_zero (S : Sz) (t e d : ℕ) (hk : SemOK S e d) (d2 : PQ.RD) (o : (wRound d2).Orc)
    (f : (S.sg t).cIn.Word) (hf : WordTie S t d2 o f) (w : (S.sg t).cIn.N.Wit)
    (hn : offCnt (Ex := (S.sg t).cIn.ext) f ((S.sg t).cIn.enc w.1 w.2) ≤ e) :
    FreeZero S t w.1 := by
  intro a i j hR hi
  by_contra hne
  -- the row's message and tail are not both 0, so its code word is not 0 at d positions or more
  have hnz : ¬ ((fun j => w.1 (.inl (memRow S t a i, j))) = (0 : Fin S.P.C.l → GE) ∧
      (fun q => w.2 (.inl (memRow S t a i, q))) = (0 : Fin S.P.C.r → GE)) :=
    fun h => hne (congrFun h.1 j)
  have h1 := hk.dist _ _ hnz
  -- at each of these positions the word, which is 0 on the row, differs from the encoding
  have h2 : cnt (fun x : Fin (2 ^ S.P.C.a) => (ldOf S.P.C S.P.C.a).T
      ((ldOf S.P.C S.P.C.a).enc (fun j => w.1 (.inl (memRow S t a i, j)))
        (fun q => w.2 (.inl (memRow S t a i, q)))) x ≠ 0) ≤
      offCnt (Ex := (S.sg t).cIn.ext) f ((S.sg t).cIn.enc w.1 w.2) := by
    refine cnt_mono fun x hx heq => hx ?_
    funext u
    have h3 := congrFun heq (.inl (memRow S t a i, ()))
    exact h3.symm.trans (hf.free (posIn S.P.C x) a i hR hi)
  exact absurd (h1.trans (h2.trans hn)) (not_le.2 hk.lt)

/-- Each member's word is near the encoding of its share. -/
theorem mem_inList (S : Sz) (t e d : ℕ) (hk : SemOK S e d) (d2 : PQ.RD) (o : (wRound d2).Orc)
    (f : (S.sg t).cIn.Word) (hf : WordTie S t d2 o f) (w : (S.sg t).cIn.N.Wit)
    (hn : offCnt (Ex := (S.sg t).cIn.ext) f ((S.sg t).cIn.enc w.1 w.2) ≤ e) (a : Bool) :
    (S.fam.om a).InList (wordsOf S d2 o a) (fun j => w.1 (atJ S t a j)) := by
  refine ⟨fun q => w.2 (atQ S t a q), le_trans (le_trans ?_ hn) hk.rad⟩
  -- where the group's symbols agree, so do the member's
  show cnt _ ≤ cnt fun x : Fin (2 ^ S.P.C.a) =>
    (S.sg t).cIn.T f x ≠ (S.sg t).cIn.T ((S.sg t).cIn.enc w.1 w.2) x
  refine cnt_mono fun x hx heq => hx ?_
  funext u
  rcases u with ⟨i, v⟩ | ⟨i, _⟩
  · have h3 := congrFun heq (.inl (memRow S t a i.val, ()))
    exact (hf.sent (posIn S.P.C x) a i.val i.isLt).symm.trans h3
  · exact i.elim

/-- The share of one main row of the group's tables in the value of v at m. -/
private def rowVal (S : Sz) (t : ℕ) (v m : (S.sg t).cIn.J → GE)
    (b : Fin ((S.sg t).h + (S.sg t).g) → Bool) : GE :=
  ∑ p : Fin S.P.C.l, v (.inl (b, p)) * m (.inl (b, p))

/-- The value of v at m is the sum of the main rows' shares, if v is 0 on the mask row. -/
private theorem val_rows (S : Sz) (t : ℕ) (v m : (S.sg t).cIn.J → GE)
    (hv : ∀ j, v (.inr j) = 0) : ∑ j, v j * m j = ∑ b, rowVal S t v m b := by
  have hz : ∑ x : (Fin (S.sg t).h → Bool) × Fin S.P.Z.l, v (.inr x) * m (.inr x) = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [hv, zero_mul]
  rw [Fintype.sum_sum_type, hz, add_zero, Fintype.sum_prod_type]
  rfl

/-- The sum over all main rows, by the rows' numbers: first one member's block, then the other's. -/
private theorem rows_blocks (S : Sz) (t : ℕ) (F : (Fin ((S.sg t).h + (S.sg t).g) → Bool) → GE) :
    ∑ b, F b = (∑ i ∈ Finset.range (2 ^ S.P.aR), F (memRow S t false i)) +
      ∑ i ∈ Finset.range (2 ^ S.P.aR), F (memRow S t true i) := by
  have h1 : ∑ b, F b = ∑ b : Fin ((S.sg t).h + (S.sg t).g) → Bool,
      (fun i : ℕ => F fun u => i.testBit u.val) (Sz.rowNo b) :=
    Finset.sum_congr rfl fun b _ => by
      show F b = F fun u => (Sz.rowNo b).testBit u.val
      rw [show (fun u : Fin ((S.sg t).h + (S.sg t).g) => (Sz.rowNo b).testBit u.val) = b from
        funext (testBit_rowNo b)]
  have h2 : 2 ^ ((S.sg t).h + (S.sg t).g) = 2 ^ S.P.aR + 2 ^ S.P.aR := by
    show 2 ^ (0 + (S.P.aR + 1)) = 2 ^ S.P.aR + 2 ^ S.P.aR
    rw [Nat.zero_add, pow_succ, Nat.mul_two]
  rw [h1, sum_rowNo ((S.sg t).h + (S.sg t).g) (fun i : ℕ => F fun u => i.testBit u.val), h2,
    Finset.sum_range_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · show (F fun u => i.testBit u.val) = F fun u => (S.blk false + i).testBit u.val
    rw [show S.blk false + i = i from Nat.zero_add i]
  · rfl

/-- In a member's block the rows that the member does not have add nothing. -/
private theorem block_cut (S : Sz) (t : ℕ) (v m : (S.sg t).cIn.J → GE) (h0 : FreeZero S t m)
    (a : Bool) :
    ∑ i ∈ Finset.range (2 ^ S.P.aR), rowVal S t v m (memRow S t a i) =
      ∑ i : Fin S.P.R, rowVal S t v m (memRow S t a i.val) := by
  have hR : S.P.R ≤ 2 ^ S.P.aR := le_two_pow_clog S.P.R
  rw [Fin.sum_univ_eq_sum_range (fun i => rowVal S t v m (memRow S t a i)) S.P.R]
  refine (Finset.sum_subset (Finset.range_mono hR) fun i hi hn => ?_).symm
  have h1 : i < 2 ^ S.P.aR := Finset.mem_range.1 hi
  have h2 : S.P.R ≤ i := Nat.le_of_not_lt fun h => hn (Finset.mem_range.2 h)
  exact Finset.sum_eq_zero fun p _ => by rw [h0 a i p h2 h1, mul_zero]

/-- A member's share is the sum of the shares of its rows. -/
private theorem member_rows (S : Sz) (t : ℕ) (v m : (S.sg t).cIn.J → GE) (a : Bool) :
    ∑ j : S.MJ, v (atJ S t a j) * m (atJ S t a j) =
      ∑ i : Fin S.P.R, rowVal S t v m (memRow S t a i.val) := by
  have he : ∑ x : Empty × Fin S.P.Z.l, v (atJ S t a (.inr x)) * m (atJ S t a (.inr x)) = 0 :=
    Finset.sum_eq_zero fun x _ => x.1.elim
  rw [Fintype.sum_sum_type, he, add_zero, Fintype.sum_prod_type]
  rfl

/-- The value of a vector at a message that is 0 on the rows that no member has: the sum of
the two members' shares. -/
theorem val_split (S : Sz) (t : ℕ) (v m : (S.sg t).cIn.J → GE) (hv : ∀ j, v (.inr j) = 0)
    (h0 : FreeZero S t m) :
    ∑ j, v j * m j = ∑ a : Bool, ∑ j : S.MJ, v (atJ S t a j) * m (atJ S t a j) := by
  rw [val_rows S t v m hv, rows_blocks S t (rowVal S t v m), block_cut S t v m h0 false,
    block_cut S t v m h0 true, Fintype.sum_bool, member_rows S t v m true,
    member_rows S t v m false, add_comm]

/-- A sum over the two members, beginning with a. -/
theorem sum_bool_at {M : Type} [AddCommMonoid M] (a : Bool) (F : Bool → M) :
    ∑ b, F b = F a + F (!a) := by
  rw [Fintype.sum_bool]
  cases a
  · exact add_comm _ _
  · rfl

/-- If the statement after the link's five rounds has no witness, then no message on the group's
tables is near the word and meets all rows. -/
theorem rows_back_sem (S : Sz) (t e d : ℕ) (hk : SemOK S e d) (d2 : PQ.RD) (o : (wRound d2).Orc)
    (f : (S.sg t).cIn.Word) (hf : WordTie S t d2 o f) (x : S.lk.X4)
    (hno : ∀ w, ¬ S.lk.j4.cf.relR (x, wordsOf S d2 o) w)
    (tg : ℕ → GE) (vs : ℕ → (S.sg t).cIn.J → GE) (hr : IsRows S t x tg vs) :
    ∀ w, ¬ ConL (S.sg t).cIn.N e
      (Slf.All fun _ : Fin S.nRows => (Slf.idf (E := GE) (J := (S.sg t).cIn.J)))
      ((fun b => tg b.val, fun b => vs b.val), f) w := by
  rintro w ⟨hn, hall⟩
  have h0 : FreeZero S t w.1 := free_zero S t e d hk d2 o f hf w hn
  -- each row, as a sum over the two members' shares, beginning with the member a
  have hval : ∀ (b : ℕ) (a : Bool), b < S.nRows →
      ∑ j : S.MJ, vs b (atJ S t a j) * w.1 (atJ S t a j) +
        ∑ j : S.MJ, vs b (atJ S t (!a) j) * w.1 (atJ S t (!a) j) = tg b := by
    intro b a hb
    rw [← sum_bool_at a fun a => ∑ j : S.MJ, vs b (atJ S t a j) * w.1 (atJ S t a j),
      ← val_split S t (vs b) w.1 (hr.mask b) h0]
    exact hall ⟨b, hb⟩
  -- a form that is given on some entries, at a member's share
  have hpush : ∀ (a : Bool) {St I : Type} [Fintype I] (φ : I → (S.lk.N.om a).C.J)
      (c : St → I → GE) (st : St),
      ∑ j, Slf.push φ c st j * w.1 (atJ S t a j) = ∑ i, c st i * w.1 (atJ S t a (φ i)) :=
    fun a St I _ φ c st => ldForm_push GE St I (S.lk.N.om a).C.J φ c st fun j => w.1 (atJ S t a j)
  by_cases hon : S.lk.j4.on (x, wordsOf S d2 o)
  swap
  · exact hno (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)) (Or.inr hon)
  refine hno (fun a => (fun j => w.1 (atJ S t a j), fun q => w.2 (atQ S t a q)),
    (fun _ _ => 0, fun _ _ => 0)) (Or.inl ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩)
  · -- each member decodes, with its sample, to its share
    intro a
    refine (sig_dec_good GE (S.fam.om a) (wordsOf S d2 o a) (x.1.1.2 a).1 (hon a) (x.1.1.2 a).2
      _).2 ⟨mem_inList S t e d hk d2 o f hf w hn a, ?_⟩
    funext u
    have h := hval (1 + a.toNat) a (by unfold Sz.nRows; cases a <;> simp <;> omega)
    have hz : ∑ j : S.MJ, vs (1 + a.toNat) (atJ S t (!a) j) * w.1 (atJ S t (!a) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hr.smO a j, zero_mul]
    rw [hz, add_zero, hr.smT a] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun j _ => by rw [hr.smS a j]
  · exact funext fun s => s.elim
  · -- the first table's draws
    intro i
    have h := hval (3 + i.val) false (by
      have hi : i.val < S.P.nu0 := i.isLt
      unfold Sz.nRows
      omega)
    have hz : ∑ j : S.MJ, vs (3 + i.val) (atJ S t (!false) j) * w.1 (atJ S t (!false) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (3 + i.val) (atJ S t (!false) j) = 0 from hr.c0O i j, zero_mul]
    rw [hz, add_zero, hr.c0T i] at h
    refine Eq.trans ?_ h
    refine ((hpush false S.putAt (fun x k => S.ix.G x k) (x.1.2.1.1 i)).symm.trans ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hr.c0S i j]; rfl
  · exact funext fun s => s.elim
  · -- the copy's draws
    intro i
    have h := hval (3 + S.P.nu0 + i.val) true (by
      have hi : i.val < S.P.nuj := i.isLt
      unfold Sz.nRows
      omega)
    have hz : ∑ j : S.MJ, vs (3 + S.P.nu0 + i.val) (atJ S t (!true) j) *
        w.1 (atJ S t (!true) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (3 + S.P.nu0 + i.val) (atJ S t (!true) j) = 0 from hr.c1O i j, zero_mul]
    rw [hz, add_zero, hr.c1T i] at h
    refine Eq.trans ?_ h
    refine ((hpush true S.putAt (fun x k => S.ix.G x k) (x.1.2.2.1 i)).symm.trans ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hr.c1S i j]; rfl
  · -- the equality row
    have h := hval 0 false (by unfold Sz.nRows; omega)
    have e0 : ∑ j : S.MJ, vs 0 (atJ S t false j) * w.1 (atJ S t false j) =
        ∑ a : S.Lay, Alg.eqk x.2 (S.lw.pl a) *
          w.1 (atJ S t false (S.putAt (S.ix.pl (S.lw.lay a)))) :=
      (Finset.sum_congr rfl fun j _ => by rw [hr.eq0 j]; rfl).trans
        (hpush false (fun a => S.putAt (S.ix.pl (S.lw.lay a)))
          (fun φ a => Alg.eqk φ (S.lw.pl a)) x.2)
    have e1 : ∑ j : S.MJ, vs 0 (atJ S t (!false) j) * w.1 (atJ S t (!false) j) =
        -∑ a : S.Lay, Alg.eqk x.2 (S.lw.pl a) *
          w.1 (atJ S t true (S.putAt (S.ix.pl (S.lw.lay a)))) := by
      rw [← hpush true (fun a => S.putAt (S.ix.pl (S.lw.lay a)))
        (fun φ a => Alg.eqk φ (S.lw.pl a)) x.2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show vs 0 (atJ S t (!false) j) = _ from hr.eq1 j, neg_mul]; rfl
    rw [e0, e1, hr.eqT, ← sub_eq_add_neg, ← Finset.sum_sub_distrib] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun a _ => mul_sub _ _ _

/-! ## The block, in the field -/

/-- The error count of the written round: the bound on the lists of the group's code, times the
number of rows less one, times the number in the law of the format's sampler. -/
def batErr (S : Sz) (L : ℕ) (dA : PQ.RD) : ℕ :=
  L * (S.nRows - 1) * (bsRound .two dA.entry dA.kind).w

/-- The rows under the powers of θ: the target and the vector. -/
def sumStm (S : Sz) (t : ℕ) (tg : ℕ → GE) (vs : ℕ → (S.sg t).cIn.J → GE) (θ : GE) :
    GE × ((S.sg t).cIn.J → GE) :=
  (∑ b : Fin S.nRows, θ ^ b.val * tg b.val, fun j => ∑ b : Fin S.nRows, vs b.val j * θ ^ b.val)

/-- The round in which all rows become one is taken off, in the field. x: the statement after the
link's five rounds; o: the oracle of the link's second round; f: the word on the stage's rows; tg,
vs: the rows' targets and vectors. -/
theorem bat_block_sem (S : Sz) (t₀ e d L : ℕ) (hk : SemOK S e d)
    (hL : (S.sg t₀).cIn.ListAt e L) (d2 dA : PQ.RD) (hA : SendsDraws dA 0 1 0 0)
    (t : Shape) (εt : Err t) (o : (wRound d2).Orc) (f : (S.sg t₀).cIn.Word)
    (hf : WordTie S t₀ d2 o f) (x : S.lk.X4)
    (hno : ∀ w, ¬ S.lk.j4.cf.relR (x, wordsOf S d2 o) w)
    (tg : ℕ → GE) (vs : ℕ → (S.sg t₀).cIn.J → GE) (hr : IsRows S t₀ x tg vs)
    (bad : Tr (wRound dA :: t) → Prop)
    (hp : ∀ m c τ, GChal.pass (b := dA.entry.work) c = false → bad (m, c, τ))
    (H : ∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal),
      (∀ w, ¬ (S.sg t₀).RIn e (sumStm S t₀ tg vs (gOne _ (valsOf dA c)), f) w) →
      Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound dA :: t) (batErr S L dA, εt) bad :=
  peel_draw (Evader.powers GE S.nRows).D (batNx (Evader.powers GE S.nRows).ze)
    (know_bat (S.sg t₀).cIn (fun _ : Fin S.nRows => (S.sg t₀).cIn.J → GE)
      (fun _ => Slf.idf) (Evader.powers GE S.nRows) e L (ok_powers GE S.nRows) hL)
    dA (gOne _) hA.gOne_inj hA.logN t εt
    ((fun b => tg b.val, fun b => vs b.val), f)
    (rows_back_sem S t₀ e d hk d2 o f hf x hno tg vs hr) bad hp fun m c hB => H m c hB

end OnBytes.Slice

#print axioms OnBytes.Slice.peel_draw
#print axioms OnBytes.Slice.free_zero
#print axioms OnBytes.Slice.mem_inList
#print axioms OnBytes.Slice.val_split
#print axioms OnBytes.Slice.rows_back_sem
#print axioms OnBytes.Slice.bat_block_sem
