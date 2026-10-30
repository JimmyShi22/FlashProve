-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Base.lean: the last two rounds of the written proximity test are taken off by the
library's theorem on its base case.

The written test is the interactive protocol in the types of the format, that is, of the library's
folder Fmt/, which has the verifier's decision as functions on machine words. It ends with two
rounds. In the first the prover sends one element, the masking word's target, and the verifier draws
one element lam. In the second the prover shows two messages and two tails in full, and the verifier
draws positions. The format's decision then runs `baseOK` (Fmt/M1Fold.lean): one linear equation on
what is shown, and two equations at every drawn position, on the symbols in the opened columns of
the last tree. A column of that tree holds four symbols: the main row's and the mask row's, of which
the claim is made, and next to each a symbol of a masking word.

The library's base case (Cb/Ld/LdBase.lean) has the same two rounds in its own types, with one
difference: there the prover sends the masking word in the first of them. The programs (the C++
implementation) send it earlier, in the last tree. So the masking word is a parameter here (`mk`),
fixed before the block, and the map of prover messages puts it into the first round
(OnBytes/Slice/Carry.lean allows that).

The result, `base_block`. Let the claim before the block (a row on the last tree's two tables, each
of one row) have no witness in the relaxed relation at the radius e. Then the prover has lost at the
start of the two rounds, towards any goal that holds
 - wherever a round's test of work (its bits of proof of work) fails, and
 - wherever the format's own base test says no.
"Has lost" is the library's `Iop.Doomed`: in each round, whatever the prover sends, all but a
counted number of verifier messages leave it lost, and at the end the goal holds. To take a block of
rounds off is to prove this at the block's start.
The function `last`, which gives the opened columns, may depend on the two rounds: which columns
are opened depends on the drawn positions. What is asked of it: a column that it gives holds the
symbols of the fixed word `col` and of the fixed masking word `mk`.

How it is proved, in two theorems.
 `base_block_sem` has the protocol and no function of the format on claims. The library's
   round-by-round knowledge soundness of its base case (`Cb.ldBase_know`) is carried to the written
   rounds (`peel_last`). The claim is any target with any vector, and the goal has to hold wherever
   the library's decision `Cb.LdwAccept` fails at the values of the two rounds as they are read in
   the field. Another implementation of the same decision is joined to it by a lemma like the next.
 `accept_of_baseOK` has the format's function and no protocol: read in the field, the equations of
   `baseOK` give the library's decision (OnBytes/Slice/SimBase.lean has the equations). So the
   written test refuses wherever the library's verifier refuses.

What else is asked: the laws of the two tables' code, a bound on the exceptional points of a line
and a bound on the lists of pairs, both at the radius e (`BaseCodes`); what each of the two rounds
sends and draws (`SendsDraws`); for `base_block`, that each table has one row.

Main definitions: `wordMk`, `shown`, `sentW`, `shownW`, `BaseCodes`, `baseErr`.
Main theorems: `accept_of_baseOK`, `base_block_sem`, `base_block`.
Not claimed. No bound on a list or on a count of exceptional points: these are hypotheses. Nothing
on how large the error counts are. That the written test says yes wherever the library's verifier
accepts is not needed and not stated here.
-/
import OnBytes.Slice.RoundsMaps
import OnBytes.Slice.SimBase
import Cb.Ld.LdBaseProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## A table with one row -/

/-- A sum over the vertices of a cube without variables has one term. -/
theorem sum_rows0 {k : ℕ} (hk : k = 0) {M : Type} [AddCommMonoid M] (f : (Fin k → Bool) → M) :
    ∑ b, f b = f fun _ => false := by
  subst hk
  exact Fintype.sum_eq_single _ fun b hb => absurd (Subsingleton.elim _ _) hb

/-- The one vertex of a cube without variables has the number 0. -/
theorem rowNo_zero {k : ℕ} (hk : k = 0) (b : Fin k → Bool) : Sz.rowNo b = 0 := by
  subst hk
  exact Fin.sum_univ_zero _

/-! ## The library's parameters -/

/-- The masking word. mk x holds the two symbols of the masking word in the column at x: the one
next to the main row's symbol and the one next to the mask row's. -/
def wordMk (s : Sg) (mk : ℕ → Fmt.M1.E × Fmt.M1.E) : s.cIn.Word := fun p =>
  match p with
  | .inl x => fun _ => toE (mk x.val).1
  | .inr x => fun _ => toE (mk x.val).2

/-- What the prover shows in full: two messages and two tails, each row of a table the same. -/
def shown (s : Sg) (M0 M1 R0 R1 : List Fmt.M1.E) : s.cIn.MR :=
  (Sum.elim (fun x => lst M0 x.2.val) (fun x => lst M1 x.2.val),
    Sum.elim (fun x => lst R0 x.2.val) (fun x => lst R1 x.2.val))

/-- The elements that a written prover message sends. -/
def sentW (d : PQ.RD) (m : (wRound d).Msg) : List Fmt.M1.E :=
  Fmt.M1.sentOf (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2))

/-- The four lists of the last message, cut as the decision cuts them. -/
def shownW (s : Sg) (l : List Fmt.M1.E) : s.cIn.MR :=
  shown s (l.take s.C.l) ((l.drop s.C.l).take s.Z.l) ((l.drop (s.C.l + s.Z.l)).take s.C.r)
    (l.drop (s.C.l + s.Z.l + s.C.r))

/-! ## The written test accepts only what the library's verifier accepts -/

/-- If the written base test says yes, the library's decision holds of the claim, the word of
the columns and the masking word as they are read in the field. -/
theorem accept_of_baseOK (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0)
    (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col) (mk : ℕ → Fmt.M1.E × Fmt.M1.E)
    (last : ℕ → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E))
    (hlast : ∀ x q, last x = some q → Fmt.M1.ent (col x).main 0 = q.1 ∧ (mk x).1 = q.2.1 ∧
      Fmt.M1.ent (col x).mask 0 = q.2.2.1 ∧ (mk x).2 = q.2.2.2)
    (tauS lam : Fmt.M1.E) (M0 M1 R0 R1 : List Fmt.M1.E) (xs : List ℕ) (Q : Fin s.t → s.Ps)
    (hQ : ∀ i, (Q i).val ∈ xs)
    (hok : Fmt.M1.baseOK .two s.C s.Z G.c G.d G.t tauS lam M0 M1 R0 R1 xs last = true) :
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) (stmIn s G)) (stmIn s G).1
      (s.cIn.T (wordIn s col)) (s.cIn.T (wordMk s mk)) (toE tauS) (toE lam)
      (shown s M0 M1 R0 R1) Q := by
  obtain ⟨hlen, hb1, hb2⟩ :=
    (baseOK_iff_parts s.C s.Z G.c G.d G.t tauS lam M0 M1 R0 R1 xs last).1 hok
  have hk : s.h + s.g = 0 := by omega
  refine ⟨?_, fun i => ?_⟩
  · -- the linear test
    refine Eq.trans ?_ ((baseB1_iff G.c G.d G.t tauS lam M0 M1 s.C.l s.Z.l (le_of_eq hlen.1)
      (le_of_eq hlen.2.1)).1 hb1)
    show ∑ j : s.cIn.J, vecIn s G j * (shown s M0 M1 R0 R1).1 j = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, sum_rows0 hk,
      sum_rows0 h0, ← Fin.sum_univ_eq_sum_range (fun i => vec G.c i * lst M0 i) s.C.l,
      ← Fin.sum_univ_eq_sum_range (fun i => vec G.d i * lst M1 i) s.Z.l]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      show vec G.c (Sz.rowNo _ + 2 ^ (s.h + s.g) * j.val) * lst M0 j.val = _
      rw [rowNo_zero hk, hk, pow_zero, one_mul, zero_add]
    · refine Finset.sum_congr rfl fun j _ => ?_
      show vec G.d (Sz.rowNo _ + 2 ^ s.h * j.val) * lst M1 j.val = _
      rw [rowNo_zero h0, h0, pow_zero, one_mul, zero_add]
  · -- the tests at the position Q i
    obtain ⟨o, ho, hb⟩ := hb2 (Q i).val (hQ i)
    obtain ⟨h1, h2, h3, h4⟩ := hlast _ _ ho
    obtain ⟨hm, hz⟩ := (baseB2At_iff s.C s.Z lam M0 M1 R0 R1 (Q i).val o).1 hb
    funext α
    rcases α with ⟨b, ⟨⟩⟩ | ⟨b, ⟨⟩⟩
    · have hpc : posIn s.C (Q i) = Q i := Fin.ext (Nat.mod_eq_of_lt (Q i).isLt)
      show (ldOf s.C s.C.a).enc (fun j => lst M0 j.val) (fun q => lst R0 q.val)
          (posIn s.C (Q i)) () =
        toE (mk (posIn s.C (Q i)).val).1 +
          toE lam * vec (col (posIn s.C (Q i)).val).main (Sz.rowNo b)
      rw [hpc, ← symV_enc, hm, rowNo_zero hk, h2]
      unfold vec
      rw [h1]
    · show (ldOf s.Z s.Z.a).enc (fun j => lst M1 j.val) (fun q => lst R1 q.val)
          (posIn s.Z (Q i)) () =
        toE (mk (Q i).val).2 + toE lam * vec (col (Q i).val).mask (Sz.rowNo b)
      have hz' : symV s.Z (posIn s.Z (Q i)).val M1 R1 =
          toE o.2.2.2 + toE lam * toE o.2.2.1 := hz
      rw [← symV_enc, hz', rowNo_zero h0, h4]
      unfold vec
      rw [h3]

/-! ## The block -/

/-- What is asked of the last stage's codes, in the library's words: the laws of the pair of tables;
a bound on the exceptional points of a line at the radius e; a bound on the lists of pairs at the
radius e. -/
structure BaseCodes (s : Sg) (e exc L2 : ℕ) : Prop where
  laws : s.cIn.Laws
  mca : s.cIn.MCAat e exc
  list : (s.cIn.il Bool).ListAt e L2

/-- The error counts of the two written rounds: the library's, each times the number in the law of
the format's sampler. -/
def baseErr (s : Sg) (e exc L2 : ℕ) (dL dB : PQ.RD) : Err (PQ.uL (ckP .two) [dL, dB]) :=
  ((exc + L2) * (bsRound .two dL.entry dL.kind).w,
    ((2 ^ s.C.a - e - 1) ^ s.t * (bsRound .two dB.entry dB.kind).w, ()))

/-- The base case is taken off, in the field. No function of the format on claims occurs. The
claim x is any target with any vector, f any word, g any masking word, all fixed before the block.
fu reads the masking word's target off the first written message, fs reads what is shown in full off
the second: any two maps. The drawn element and the drawn positions are the typed values.
If the claim has no witness at the radius e, the prover has lost at the start of the two rounds,
towards any goal that holds wherever a test of work fails and wherever the library's decision
`Cb.LdwAccept` fails at these values. The stage may have any numbers of rows. -/
theorem base_block_sem (s : Sg) (e exc L2 : ℕ) (dL dB : PQ.RD) {nL aL nB : ℕ}
    (hc : BaseCodes s e exc L2) (hL : SendsDraws dL nL 1 0 aL) (hB : SendsDraws dB nB 0 s.t s.C.a)
    (x : GE × (s.cIn.J → GE)) (f g : s.cIn.Word) (fu : (wRound dL).Msg → GE)
    (fs : (wRound dB).Msg → s.cIn.MR) (hno : ∀ w, ¬ s.RIn e (x, f) w)
    (bad : Tr (PQ.uL (ckP .two) [dL, dB]) → Prop)
    (hp : ∀ τ, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad τ)
    (H : ∀ m1 c1 m2 c2,
      ¬ LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) x) x.1 (s.cIn.T f)
        (s.cIn.T g) (fu m1) (gOne _ (valsOf dL c1)) (fs m2) (gPos s.C.a s.t _ (valsOf dB c2)) →
      bad (m1, c1, m2, c2, ())) :
    Doomed _ (baseErr s e exc L2 dL dB) bad := by
  have hK := ldBase_know s.cIn (Slf.idf (E := GE) (J := s.cIn.J)) s.t
    (fun _ => ⟨0, Nat.two_pow_pos _⟩) (d := e + 1) hc.laws (Nat.lt_succ_self e) hc.mca hc.list
  have hE : baseErr s e exc L2 dL dB = mulErr [wRound dL, wRound dB] (ldBaseShape s.cIn s.t)
      (((bsRound .two dL.entry dL.kind).w, ((bsRound .two dB.entry dB.kind).w, ())) : ℕ × ℕ × Unit)
      (ldBaseErr s.cIn s.t e exc L2) := by
    show _ = ((exc + L2) * _, ((Fintype.card s.Ps - e - 1) ^ s.t * _, ()))
    rw [Fintype.card_fin]
    rfl
  rw [hE]
  -- the image of a written transcript
  have htr := two_tr (r₁' := s.cIn.sendRound GE GE 0)
    (r₂' := Blocks.plainRound s.cIn.MR (Fin s.t → s.Ps) 0)
    (fun m : (wRound dL).Msg => (g, fu m)) (chalTo dL (gOne _))
    (fun m : (wRound dB).Msg => ((), fs m)) (chalTo dB (gPos s.C.a s.t _))
  refine peel_last (s := [wRound dL, wRound dB]) _ hK (x, f) trivial hno
    (two (r₁' := s.cIn.sendRound GE GE 0) (r₂' := Blocks.plainRound s.cIn.MR (Fin s.t → s.Ps) 0)
      (fun m => (g, fu m)) (chalTo dL (gOne _)) (fun m => ((), fs m))
      (chalTo dB (gPos s.C.a s.t _)))
    (((bsRound .two dL.entry dL.kind).w, ((bsRound .two dB.entry dB.kind).w, ())) : ℕ × ℕ × Unit)
    (two_fib _ _ _ _ _ _ (chalTo_fib dL _ (hL.gOne_inj) hL.logN)
      (chalTo_fib dB _ (hB.gPos_inj) hB.logN)) bad ?_ ?_
  · -- no image: a test of work has failed
    rintro ⟨m1, c1, m2, c2, ⟨⟩⟩ hτ0
    have hτ := (htr m1 c1 m2 c2).symm.trans hτ0
    cases h1 : chalTo dL (gOne _) c1 with
    | none =>
      exact hp _ (by simp only [PQ.passSL, PQ.rhoSL, chalTo_none dL _ c1 h1, Bool.false_and])
    | some μ =>
      cases h2 : chalTo dB (gPos s.C.a s.t _) c2 with
      | none =>
        exact hp _ (by
          simp only [PQ.passSL, PQ.rhoSL, chalTo_none dB _ c2 h2, Bool.false_and, Bool.and_false])
      | some Q =>
        rw [h1, h2] at hτ
        cases hτ
  · -- an image at which the library's verifier refuses
    rintro ⟨m1, c1, m2, c2, ⟨⟩⟩ τ' hτ0 hno'
    have hτ := (htr m1 c1 m2 c2).symm.trans hτ0
    cases h1 : chalTo dL (gOne _) c1 with
    | none =>
      rw [h1] at hτ
      cases hτ
    | some μ =>
      cases h2 : chalTo dB (gPos s.C.a s.t _) c2 with
      | none =>
        rw [h1, h2] at hτ
        cases hτ
      | some Q =>
        rw [h1, h2] at hτ
        obtain rfl := Option.some.inj hτ
        obtain rfl := chalTo_some dL _ c1 μ h1
        obtain rfl := chalTo_some dB _ c2 Q h2
        refine H m1 c1 m2 c2 fun hacc => ?_
        have hout : (ldBaseIOR s.cIn (Slf.idf (E := GE) (J := s.cIn.J)) s.t
            fun _ => ⟨0, Nat.two_pow_pos _⟩).out x f
            ((g, fu m1), gOne _ (valsOf dL c1), ((), fs m2), gPos s.C.a s.t _ (valsOf dB c2), ()) =
            some () :=
          if_pos hacc
        exact hno' ((), ()) () (congrArg (Option.map fun xo : Unit => (xo, ())) hout) trivial

/-- The base case is taken off. If the claim on the last tree's tables has no witness at the
radius e, the prover has lost at the start of the last two rounds, towards any goal that holds
wherever a test of work fails and wherever the format's base test says no. Asked: each table has one
row, `BaseCodes`, what the two rounds send and draw, and that a column given by `last` holds the
symbols of the fixed `col` and `mk`. -/
theorem base_block (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (e exc L2 : ℕ)
    (dL dB : PQ.RD) (hc : BaseCodes s e exc L2) (hL : SendsDraws dL 1 1 0 0)
    (hB : SendsDraws dB (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t s.C.a)
    (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col) (mk : ℕ → Fmt.M1.E × Fmt.M1.E)
    (last : Tr (PQ.uL (ckP .two) [dL, dB]) →
      ℕ → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E))
    (hlast : ∀ τ x q, last τ x = some q → Fmt.M1.ent (col x).main 0 = q.1 ∧ (mk x).1 = q.2.1 ∧
      Fmt.M1.ent (col x).mask 0 = q.2.2.1 ∧ (mk x).2 = q.2.2.2)
    (hno : ∀ w, ¬ s.RIn e (stmIn s G, wordIn s col) w)
    (bad : Tr (PQ.uL (ckP .two) [dL, dB]) → Prop)
    (hp : ∀ τ, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad τ)
    (H : ∀ (τ : Tr (PQ.uL (ckP .two) [dL, dB])) tauS lam ps rs1 v,
      Fmt.M1.nextN 1 1 0 (rsOf _ τ) = some (⟨[tauS], [lam], ps⟩, rs1) →
      Fmt.M1.nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 = some (v, []) →
      Fmt.M1.baseOK .two s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l)
        ((v.sent.drop s.C.l).take s.Z.l) ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r)
        (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss (last τ) = false → bad τ) :
    Doomed _ (baseErr s e exc L2 dL dB) bad := by
  refine base_block_sem s e exc L2 dL dB hc hL hB (stmIn s G) (wordIn s col) (wordMk s mk)
    (fun m => lst (sentW dL m) 0) (fun m => shownW s (sentW dB m)) hno bad hp ?_
  intro m1 c1 m2 c2 hrej
  -- the decision's tests of the two rounds' sizes do not refuse
  obtain ⟨tauS, hts⟩ := List.length_eq_one_iff.1 (hL.sent_length m1 c1)
  obtain ⟨lam, hlm⟩ := List.length_eq_one_iff.1 (hL.els_length m1 c1)
  have hn1 : Fmt.M1.nextN 1 1 0 (rsOf [dL, dB] (m1, c1, m2, c2, ())) =
      some (⟨[tauS], [lam], (rvOf dL m1 c1).poss⟩, [rvOf dB m2 c2]) := by
    rw [← hts, ← hlm]
    exact hL.next m1 c1 [rvOf dB m2 c2]
  refine H _ tauS lam _ _ _ hn1 (hB.next m2 c2 []) (Bool.eq_false_iff.2 fun hok => hrej ?_)
  -- the values that the decision reads are those of the image
  have hQ : ∀ i, (gPos s.C.a s.t _ (valsOf dB c2) i).val ∈ (rvOf dB m2 c2).poss := by
    intro i
    have hlt : i.val < (rvOf dB m2 c2).poss.length := by
      rw [hB.poss_length]
      exact i.isLt
    rw [hB.gPos_val m2 c2 i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
    exact List.getElem_mem hlt
  have hu : lst (sentW dL m1) 0 = toE tauS := by
    show lst (rvOf dL m1 c1).sent 0 = _
    rw [hts]
    rfl
  have hμ : gOne _ (valsOf dL c1) = toE lam := gOne_of_els dL m1 c1 hlm
  have hacc := accept_of_baseOK s h0 g0 G col mk _ (hlast (m1, c1, m2, c2, ()))
    tauS lam _ _ _ _ _ _ hQ hok
  rw [← hu, ← hμ] at hacc
  exact hacc

end OnBytes.Slice

#print axioms OnBytes.Slice.accept_of_baseOK
#print axioms OnBytes.Slice.base_block_sem
#print axioms OnBytes.Slice.base_block
