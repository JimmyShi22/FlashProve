-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyExit.lean: from a false row on sent messages to a proximity test's first claim.

Before a proximity test the verifier holds linear claims, rows, on messages that the prover sent
earlier. It draws one element, goes on with the sum of all rows under the powers of that element,
and tests this one row on the tables of the test's first stage. This file connects the two sides for
any group of sent messages with seats in a stage (OnBytes/Slice/KeyGroup.lean).

The exit (Gp.no_witness). Each sent message has one decoding, at its own radius. If it is not the
case that all members of the group decode and all rows hold of the decodings, then no message on the
stage's tables is near the group's word and meets all rows. The two cases are stated apart as
Gp.exit_of_false_row and Gp.exit_of_undecodable. These are implications on values. No protocol
occurs in them.

How it is proved. Let a message on the stage's tables be near the word and meet all rows. Its share
at a member's seat is near the member's sent word, at the member's own radius (Site.share), so it is
the member's decoding (Site.fixed). On the rows that no member has it is 0 (Gp.free_zero), because
the word is 0 there and the radius is below a row's distance. So a row's value is the sum of its
values on the members' shares (Gp.val_split).

The round in which all rows become one (batSemAt_of). For any stage, any word and any rows: if no
message is near the word and meets all rows, the prover has lost before the round, provided that it
has lost after the round whenever the combined row has no witness in the stage's relaxed relation.
The statement BatSemAt has no group in it.


What is asked (Gp.OK): no two rows of the group have one place; the stage's radius e, counted in
positions of the range, fits each member's own radius, counted in positions of its own tree; each
member's radius is below half the distance of its code; one main row and one mask row of the stage
have the distance d, and e < d.

Main definitions: Gp.OK, Gp.RowsHold, sumRow, BatSemAt.

Main theorems: Gp.free_zero, Gp.ent_inj, Gp.val_split, Gp.no_witness, Gp.exit_of_false_row,
Gp.exit_of_undecodable, Gp.exit_one, Gp.exit_three, batSemAt_of.

Not claimed. No distance of a code and no bound on a list. Nothing beyond half the distance of a
sent message's code: there a message has no single decoding. No sample of a message is used, and
sample rows are rows like the others. That a given verifier's rows and columns are these.

-/
import OnBytes.Slice.KeyGroup
import OnBytes.Slice.ChainSem

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

namespace Gp
variable {s : Sg} (G : Gp s)

/-- What is asked of a group, the stage's radius e and the number d. -/
structure OK (e d : ℕ) : Prop where
  /-- no two rows have the same place -/
  apart : G.Apart
  /-- e positions of the range are at most the member's radius in positions of its own tree -/
  fits : ∀ i, e < ((G.mb i).e + 1) * 2 ^ (s.C.a - (G.mb i).a)
  /-- each member's radius is below half the distance of its code -/
  uniq : ∀ i, ∃ d', (G.mb i).Uniq d'
  /-- one main row of the stage has the distance d -/
  distM : s.cM.Dist d
  /-- one mask row of the stage has the distance d -/
  distZ : s.cZ.Dist d
  /-- the radius is below d -/
  lt : e < d

/-- **All rows hold of the members' messages.** Row b has the target tg b and the vector vs b on the
entries of the stage's tables, of which only the members' entries are read. -/
def RowsHold (m : G.Msgs) {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE) : Prop :=
  ∀ b, ∑ k : G.J, vs b (G.ent k) * m k.1 k.2 = tg b

variable {G}

/-- Different entries of the members' messages are different entries on the stage's tables. -/
theorem ent_inj (hA : G.Apart) : Function.Injective G.ent := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  rcases j with ⟨r, p⟩ | ⟨r, p⟩ <;> rcases j' with ⟨r', p'⟩ | ⟨r', p'⟩
  · have h1 := Sum.inl.inj h
    have h2 := hA.main ⟨i, r⟩ ⟨i', r'⟩ (congrArg Prod.fst h1)
    have h3 := congrArg (fun x => x.2.val) h1
    cases h2
    have h4 : p = p' := Fin.ext h3
    rw [h4]
  · cases h
  · cases h
  · have h1 := Sum.inr.inj h
    have h2 := hA.mask ⟨i, r⟩ ⟨i', r'⟩ (congrArg Prod.fst h1)
    have h3 := congrArg (fun x => x.2.val) h1
    cases h2
    have h4 : p = p' := Fin.ext h3
    rw [h4]

/-- **A code word near the group's word is 0 on the rows that no member has.** -/
theorem free_zero {e d : ℕ} (hk : G.OK e d) {y : G.Words} {f : s.cIn.Word} (hf : G.Tie y f)
    (w : s.cIn.N.Wit) (hn : offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) ≤ e) (j : s.cIn.J)
    (hj : ∀ k, G.ent k ≠ j) : w.1 j = 0 := by
  rcases j with ⟨b, p⟩ | ⟨b, p⟩
  · have hb : ∀ n : G.RM, (G.seat n.1).pM n.2 ≠ b := fun n h =>
      hj ⟨n.1, .inl (n.2, Fin.cast (congrArg Fmt.M1.Code.l ((G.seat n.1).hC n.2).symm) p)⟩
        (congrArg (fun c => (Sum.inl (c, p) : s.cIn.J)) h)
    by_contra hne
    have hnz : ¬ ((fun j => w.1 (.inl (b, j))) = (0 : Fin s.C.l → GE) ∧
        (fun q => w.2 (.inl (b, q))) = (0 : Fin s.C.r → GE)) := fun h => hne (congrFun h.1 p)
    have h1 := hk.distM _ _ hnz
    have h2 : cnt (fun x : s.Ps => s.cM.T (s.cM.enc (fun j => w.1 (.inl (b, j)))
        (fun q => w.2 (.inl (b, q)))) x ≠ 0) ≤
        offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) := by
      refine cnt_mono fun x hx heq => hx ?_
      funext u
      exact (congrFun heq (.inl (b, ()))).symm.trans (hf.freeM (posIn s.C x) b hb)
    exact absurd (h1.trans (h2.trans hn)) (not_le.2 hk.lt)
  · have hb : ∀ n : G.RZ, (G.seat n.1).pZ n.2 ≠ b := fun n h =>
      hj ⟨n.1, .inr (n.2, Fin.cast (congrArg Fmt.M1.Code.l ((G.seat n.1).hZ n.2).symm) p)⟩
        (congrArg (fun c => (Sum.inr (c, p) : s.cIn.J)) h)
    by_contra hne
    have hnz : ¬ ((fun j => w.1 (.inr (b, j))) = (0 : Fin s.Z.l → GE) ∧
        (fun q => w.2 (.inr (b, q))) = (0 : Fin s.Z.r → GE)) := fun h => hne (congrFun h.1 p)
    have h1 := hk.distZ _ _ hnz
    have h2 : cnt (fun x : s.Ps => s.cZ.T (s.cZ.enc (fun j => w.1 (.inr (b, j)))
        (fun q => w.2 (.inr (b, q)))) x ≠ 0) ≤
        offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) := by
      refine cnt_mono fun x hx heq => hx ?_
      funext u
      exact (congrFun heq (.inr (b, ()))).symm.trans (hf.freeZ x b hb)
    exact absurd (h1.trans (h2.trans hn)) (not_le.2 hk.lt)

/-- **The value of a vector at a code word's message near the group's word** is the sum of its
values on the members' shares. -/
theorem val_split {e d : ℕ} (hk : G.OK e d) {y : G.Words} {f : s.cIn.Word} (hf : G.Tie y f)
    (w : s.cIn.N.Wit) (hn : offCnt (Ex := s.cIn.ext) f (s.cIn.enc w.1 w.2) ≤ e)
    (v : s.cIn.J → GE) : ∑ j, v j * w.1 j = ∑ k : G.J, v (G.ent k) * w.1 (G.ent k) :=
  (Fintype.sum_of_injective G.ent (ent_inj hk.apart) _ (fun j => v j * w.1 j)
    (fun j hj => by
      show v j * w.1 j = 0
      rw [free_zero hk hf w hn j fun k hk' => hj ⟨k, hk'⟩, mul_zero]) fun _ => rfl).symm

/-- **The exit.** Unless all members decode and all rows hold of the decodings, no message on the
stage's tables is near the group's word and meets all rows. -/
theorem no_witness {e d : ℕ} (hk : G.OK e d) {y : G.Words} {f : s.cIn.Word} (hf : G.Tie y f)
    {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE)
    (hno : ¬ ∃ m : G.Msgs, (∀ i, G.fix y i = some (m i)) ∧ G.RowsHold m tg vs) :
    ∀ w, ¬ ConL s.cIn.N e (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J)))
      ((tg, vs), f) w := by
  rintro w ⟨hn, hall⟩
  refine hno ⟨fun i j => w.1 ((G.seat i).atJ j), fun i => ?_, fun b => ?_⟩
  · obtain ⟨d', hU⟩ := hk.uniq i
    exact (G.seat i).fixed hU (hf.mem i) (hk.fits i) w hn
  · exact (val_split hk hf w hn (vs b)).symm.trans (hall b)

/-- The exit, where all members decode and some row is false of the decodings. -/
theorem exit_of_false_row {e d : ℕ} (hk : G.OK e d) {y : G.Words} {f : s.cIn.Word}
    (hf : G.Tie y f) {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE) (m : G.Msgs)
    (hm : ∀ i, G.fix y i = some (m i)) (hrow : ¬ G.RowsHold m tg vs) :
    ∀ w, ¬ ConL s.cIn.N e (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J)))
      ((tg, vs), f) w :=
  no_witness hk hf tg vs fun ⟨m', hm', hr⟩ => hrow (by
    have : m' = m := funext fun i => Option.some.inj ((hm' i).symm.trans (hm i))
    rwa [← this])

/-- The exit, where a member does not decode. -/
theorem exit_of_undecodable {e d : ℕ} (hk : G.OK e d) {y : G.Words} {f : s.cIn.Word}
    (hf : G.Tie y f) {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE) (i : G.ι)
    (hi : G.fix y i = none) :
    ∀ w, ¬ ConL s.cIn.N e (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J)))
      ((tg, vs), f) w :=
  no_witness hk hf tg vs fun ⟨m', hm', _⟩ => by
    have h := hm' i
    rw [hi] at h
    cases h

/-! ### At words made of written oracles -/

/-- **The exit at a group of one member**, whose tree was sent in the written round d. -/
theorem exit_one {M : Mb} {σ : Site s M} {e d₀ : ℕ} (hk : (Gp.one M σ).OK e d₀) (L : Lay)
    (d : PQ.RD) (o : (wRound d).Orc) {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE)
    (hno : ¬ ∃ m, M.fix (M.ofOrc L d o) = some m ∧ (Gp.one M σ).RowsHold (fun _ => m) tg vs) :
    ∀ w, ¬ ConL s.cIn.N e (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J)))
      ((tg, vs), Gp.oneWord M σ L d o) w :=
  no_witness hk ((Gp.one M σ).tie_word hk.apart _) tg vs fun ⟨m, hm, hr⟩ => hno ⟨m (), hm (), hr⟩

/-- **The exit at a group of three members**, whose trees were sent in three written rounds, which
may lie in different stretches of a protocol. -/
theorem exit_three {Ma Mb' Mc : Mb} {σa : Site s Ma} {σb : Site s Mb'} {σc : Site s Mc}
    {e d₀ : ℕ} (hk : (Gp.three Ma Mb' Mc σa σb σc).OK e d₀) (La Lb Lc : Lay) (da db dc : PQ.RD)
    (oa : (wRound da).Orc) (ob : (wRound db).Orc) (oc : (wRound dc).Orc) {n : ℕ}
    (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE)
    (hno : ¬ ∃ ma mb mc, Ma.fix (Ma.ofOrc La da oa) = some ma ∧
      Mb'.fix (Mb'.ofOrc Lb db ob) = some mb ∧ Mc.fix (Mc.ofOrc Lc dc oc) = some mc ∧
      (Gp.three Ma Mb' Mc σa σb σc).RowsHold
        (Tri.pick (T := fun i => ((Gp.three Ma Mb' Mc σa σb σc).mb i).cd.J → GE) ma mb mc) tg vs) :
    ∀ w, ¬ ConL s.cIn.N e (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J)))
      ((tg, vs), Gp.threeWord Ma Mb' Mc σa σb σc La Lb Lc da db dc oa ob oc) w :=
  no_witness hk ((Gp.three Ma Mb' Mc σa σb σc).tie_word hk.apart _) tg vs fun ⟨m, hm, hr⟩ =>
    hno ⟨m .a, m .b, m .c, hm .a, hm .b, hm .c, by
      have h : m = Tri.pick (T := fun i => ((Gp.three Ma Mb' Mc σa σb σc).mb i).cd.J → GE)
          (m .a) (m .b) (m .c) := funext fun i => by cases i <;> rfl
      rwa [← h]⟩

end Gp

/-! ## The round in which all rows become one, at any stage -/

/-- The rows under the powers of θ: the target and the vector. -/
def sumRow (s : Sg) {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE) (θ : GE) :
    GE × (s.cIn.J → GE) :=
  (∑ b : Fin n, θ ^ b.val * tg b, fun j => ∑ b : Fin n, vs b j * θ ^ b.val)

/-- **The batching of n rows at the stage s is taken off**, with the error count εa: if no message
is within e positions of the word f and meets all rows, the prover has lost before the written round
dA. -/
def BatSemAt (s : Sg) (e n : ℕ) (dA : PQ.RD) (εa : ℕ) : Prop :=
  ∀ (t : Shape) (εt : Err t) (f : s.cIn.Word) (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE),
    (∀ w, ¬ ConL s.cIn.N e (Slf.All fun _ : Fin n => (Slf.idf (E := GE) (J := s.cIn.J)))
      ((tg, vs), f) w) →
    ∀ bad : Tr (wRound dA :: t) → Prop,
    (∀ m c τ, GChal.pass (b := dA.entry.work) c = false → bad (m, c, τ)) →
    (∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal),
      (∀ w, ¬ s.RIn e (sumRow s tg vs (gOne _ (valsOf dA c)), f) w) →
      Doomed t εt fun b => bad (m, c, b)) →
    Doomed (wRound dA :: t) (εa, εt) bad

/-- The batching at any stage, from a bound L on the lists of the stage's code at the radius e. The
error count is L times the number of rows less one, times the number in the law of the format's
sampler. -/
theorem batSemAt_of (s : Sg) (e n L : ℕ) (hL : s.cIn.ListAt e L) (dA : PQ.RD)
    (hA : SendsDraws dA 0 1 0 0) :
    BatSemAt s e n dA (L * (n - 1) * (bsRound .two dA.entry dA.kind).w) :=
  fun t εt f tg vs hno bad hp H =>
    peel_draw (Evader.powers GE n).D (batNx (Evader.powers GE n).ze)
      (know_bat s.cIn (fun _ : Fin n => s.cIn.J → GE) (fun _ => Slf.idf) (Evader.powers GE n) e L
        (ok_powers GE n) hL)
      dA (gOne _) hA.gOne_inj hA.logN t εt ((tg, vs), f) hno bad hp fun m c hB => H m c hB

end OnBytes.Slice
