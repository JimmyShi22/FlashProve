-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchSampleMember.lean: the seven premises of `sample_clause_held`
(Johnson/Top/H/SwitchSampleAt.lean) are met TOGETHER at each written record of a code switch, AT
VALUES MADE HERE OF THE RECORD: so the law on the old samples does not speak of nothing there.

`sample_clause_held` pays the clause "sample" of the record `FrontAt` of the code switch's last join
(Johnson/Top/H0/K2Hands/TiePaid.lean; the call: Johnson/Top/H/SwitchSampleFront.lean). It asks: two
kept members have two numbers; the frame holds each member's record; the record's row bits are the
shape's; the member's `Slots`; a kept message has one answer; it is of `CaseE` or `CaseF`; and its
stored sample row is the program's row at a seed that the typed sample reads, with a factor that is
a unit. Here the seven stand together, at the frame and the two statements of
Johnson/G/SwitchAtSwitchLit.lean. Definitions, statements and proofs.
Main names:
  `smpB r`: a test with code on the kept messages' shapes: one answer; main rows of degree 3 or 1;
    the program has a pad for the shape; the cube has at most 64 coordinates; the frame record's old
    number is the place, its row bits the shape's. `smpB_says`.
  `smpB_full`, `smpB_small`: Lean's kernel says yes at each of the 25 and the 5 written records.
  `smpB_no_answers`, `smpB_no_degree`: controls: with two answers, and with degree 2, written into
    the shapes in front, it says no at each of the 24 records that keep a message.
  `shape_at`, `form_of_pad`: a kept member's shape by its number; where the program has a pad it
    makes a sample row.
  `hdRec`, `xsRec`: the caller's held messages' data at a frame; the typed held samples that read
    the seed `seedAt` and the answer zero.
  `SampleEnd`: the end of `sample_clause_held` at the record, under one name.
  `sample_member_at`: it holds, by that law, all seven premises paid.
    **`sample_member_full`**, `sample_member_small`: at each written record, for all other letters
    of the caller.
Limits: THE STATEMENT IN FRONT, ITS STORED SAMPLE ROWS, THE SEED AND THE TYPED SAMPLES ARE MADE
HERE: THEY ARE NO RUN's. The seed is a poor one: a point of 64 zeros, the factor one, the answer
zero: the stored row is the program's own `Send.form` at it, but no prover's message stands behind
the answer.
What is shown: the seven premises do not shut each other out at the written shapes. Every message of
the written lists in front passes the test on shapes, kept or not: so it does not tell the kept ones
from the others. At the last record of each table nothing is kept: nothing is asked there. Those of
SwitchAtSwitchLit.lean. The other fifteen clauses of `FrontAt` are not treated. Nothing on
soundness.

-/
import Johnson.G.SwitchAtSwitchLit
import Johnson.Top.H.SwitchSampleAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First.K2Caller VerifiableInference.Desc.First.K2Hands

/-- **The test on the kept messages' shapes.** At each kept place: one answer; main rows of degree 3
or 1; the program has a pad for the shape; the cube has at most 64 coordinates; the frame record's
old number is the place and its row bits are the shape's. -/
def smpB (r : SwRow) : Bool :=
  (List.range r.kept.length).all fun n =>
    let i := r.kept.getD n 0
    let sh := (r.lo.getD i default).1
    decide (sh.answers = 1) && decide (sh.mainDeg = 3 ∨ sh.mainDeg = 1) &&
      (Send.pad r.cs sh).isSome && decide (bitsZ r.cs sh ≤ 64) && decide ((plB r n).old = i) &&
      decide ((plB r n).rowBits = k1 sh)

set_option maxRecDepth 1000000 in
theorem smpB_full : (tableFullLit.all smpB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem smpB_small : (tableSmallLit.all smpB) = true := by decide +kernel

/-- What its yes says. -/
theorem smpB_says {r : SwRow} (h : smpB r = true) (n : ℕ) (hn : n < r.kept.length) :
    (r.lo.getD (r.kept.getD n 0) default).1.answers = 1 ∧
    ((r.lo.getD (r.kept.getD n 0) default).1.mainDeg = 3 ∨
      (r.lo.getD (r.kept.getD n 0) default).1.mainDeg = 1) ∧
    (Send.pad r.cs (r.lo.getD (r.kept.getD n 0) default).1).isSome = true ∧
    bitsZ r.cs (r.lo.getD (r.kept.getD n 0) default).1 ≤ 64 ∧
    (plB r n).old = r.kept.getD n 0 ∧
    (plB r n).rowBits = k1 (r.lo.getD (r.kept.getD n 0) default).1 := by
  unfold smpB at h
  have h' := List.all_eq_true.1 h n (List.mem_range.2 hn)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h'
  exact ⟨a, b, c, d, e, f⟩

/-- The shape at a kept member's place in the record's list of kept places is the member's. -/
theorem shape_at (r : SwRow) (a : {a // r.kp a}) :
    r.lo.getD (r.kept.getD (numAt r a) 0) default = r.lo.get a.1.1 := by
  rw [numAt_get, List.getD_eq_getElem _ _ a.1.1.isLt]
  rfl

/-- Where the program has a pad for a shape it makes a sample row. -/
theorem form_of_pad (cs : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (a : ℕ)
    (h : (Send.pad cs s).isSome = true) : ∃ row, Send.form cs s o seed a = some row := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
  unfold Send.form
  rw [hp]
  exact ⟨_, rfl⟩

section
variable (r : SwRow) (H : r.OK) (K : AtOK r) (hS : smpB r = true) (t₀ : ℕ)
  (oM oZ : Fin r.lo.length → ℕ)
  (kq : Fin r.lo.length → Prop) [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAt r H t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAt r H t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf r.cs r.lo).sub kq).Msg × Wp)) (t : ℕ)
  (w₀ : ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "KpR" => ((rowsPort r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀)
  (H.hZ t₀)).keep r.kp).Kp
set_option quotPrecheck false in
local notation "memR" =>
  slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r)
set_option quotPrecheck false in
local notation "rowR" =>
  slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
set_option quotPrecheck false in
local notation "plR" => slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
  fun a => plB r (numAt r a)
set_option quotPrecheck false in
local notation "hPr" => heldAt r H t₀ oM oZ kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // r.kp a})

/-- The held messages' data of the caller at a frame W with `Fit`. -/
noncomputable abbrev hdRec (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR)) :=
  (closeSel (hPr) Sb sl Z A₀ r.cs r.l
    (iJ (stageOf r.g t₀) W (memR) (rowR) (plR) r.cs r.l Ft.nameJ)
    (iQ (stageOf r.g t₀) W (memR) (rowR) r.cs r.l Ft.nameQ) t w₀).loc.hd

set_option quotPrecheck false in
local notation:max "hdR " W:max Ft:max => hdRec r H t₀ oM oZ kq Sb sl Z A₀ t w₀ W Ft

/-- The typed held samples that read the seed `seedAt` and the answer zero. -/
noncomputable def xsRec (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR)) : (hdR W Ft).Smp :=
  fun k => ((readP (bitsZ r.cs (r.lo.get k.1.1).1) seedAt.z, 1), fun _ => readE zeroE)

/-- The end of `sample_clause_held` at the record, under one name: there are a frame W with `Fit`
and typed held samples xs such that every held old sample has a kept member's record in W, a stored
sample row in the statement in front `stF r`, the member's `Slots` at the numbers r.lo.length + i,
the typed answer as the row's target, and the typed sample row, carried to the open word's entries,
as the vector of the stored row's form. -/
def SampleEnd : Prop := ∃ (W : SwitchFrame)
    (Ft : Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR)) (xs : (hdR W Ft).Smp),
    ∀ ks : Σ k, ((hdR W Ft).o k).Z.S, ∃ (k : KeptPlace) (smp : Row),
      W.kept[numAt r (aK ks.1)]? = some k ∧ (samplesOf (stF r) k)[0]? = some smp ∧
        Slots (stageOf r.g t₀) (KpR) r.cs r.l W (fun i => r.lo.length + i) (memR) (rowR)
          (numAt r (aK ks.1)) k ∧
        (xs ks.1).2 ks.2 = readE smp.target ∧
        pushTo ((hdR W Ft).sJ ks.1) (((hdR W Ft).o ks.1).Z.mat (xs ks.1).1 ks.2) =
          slotVec (stageOf r.g t₀) (KpR) (memR) (rowR) (numAt r (aK ks.1)) k.rowBits
            (formOn smp)

include K hS in
/-- **The seven premises of `sample_clause_held` are met together at the record**, and so its end
holds there: at the frame W of `atSwitch_at`, the statement in front `stF r`, the new messages'
numbers r.lo.length + i, and the typed held samples that read the seed `seedAt` and the answer
zero. -/
theorem sample_member_at : SampleEnd r H t₀ oM oZ kq Sb sl Z A₀ t w₀ := by
  obtain ⟨W, Ft, -, hk⟩ := paid_at r H K t₀ oM oZ
  refine ⟨W, Ft, xsRec r H t₀ oM oZ kq Sb sl Z A₀ t w₀ W Ft, ?_⟩
  refine sample_clause_held r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
    (fun a _ => a.2) H.h0 kq (numAt r) Sb sl Z A₀ r.cs r.l W (fun a => plB r (numAt r a)) Ft t w₀
    (stF r) (fun i => r.lo.length + i) (xsRec r H t₀ oM oZ kq Sb sl Z A₀ t w₀ W Ft) (numAt_inj r)
    (fun a => (hk a).1) ?_ (fun a => (hk a).2) ?_ ?_ ?_
  · intro a
    rw [(smpB_says hS _ (numAt_lt r a)).2.2.2.2.2, shape_at]
  · intro a
    have h := (smpB_says hS _ (numAt_lt r a)).1
    rwa [shape_at] at h
  · intro a
    have h := (smpB_says hS _ (numAt_lt r a)).2.1
    rw [shape_at] at h
    exact h.elim (fun h3 => Or.inl (Or.inr h3)) fun h1 => Or.inr ⟨H.h0 a.1 a.2, h1⟩
  · intro k
    obtain ⟨-, -, hp, hb, ho, -⟩ := smpB_says hS _ (numAt_lt r (aK k))
    rw [shape_at] at hp hb
    rw [numAt_get] at ho
    obtain ⟨row, hrow⟩ := form_of_pad r.cs (r.lo.get k.1.1).1 k.1.1.val seedAt 0 hp
    refine ⟨seedAt, row, zeroE, 1, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · rw [ho]
      exact hrow
    · show ((stF r).oracles.getD (plB r (numAt r (aK k))).old default).sampleRows.toList[0]? = _
      rw [ho, stF_at r _ k.1.1.isLt]
      show some (rowAt r k.1.1.val) = _
      unfold rowAt
      rw [List.getD_eq_getElem _ _ k.1.1.isLt]
      have e : Send.form r.cs (r.lo[k.1.1.val]).1 k.1.1.val seedAt 0 = some row := hrow
      rw [e]
      rfl
    · show _ ≤ (List.replicate 64 zeroE).length
      rw [List.length_replicate]
      exact hb
    · show ((1 : GEˣ) : GE) = readE oneE
      rw [readE_one]
      rfl

/-- **At each of the 25 written records of the full example.** -/
theorem sample_member_full (hr : r ∈ tableFullLit) : SampleEnd r H t₀ oM oZ kq Sb sl Z A₀ t w₀ :=
  sample_member_at r H (atB_says (List.all_eq_true.1 atB_full r hr))
    (List.all_eq_true.1 smpB_full r hr) t₀ oM oZ kq Sb sl Z A₀ t w₀

/-- **At each of the 5 written records of the small example.** -/
theorem sample_member_small (hr : r ∈ tableSmallLit) : SampleEnd r H t₀ oM oZ kq Sb sl Z A₀ t w₀ :=
  sample_member_at r H (atB_says (List.all_eq_true.1 atB_small r hr))
    (List.all_eq_true.1 smpB_small r hr) t₀ oM oZ kq Sb sl Z A₀ t w₀

end

/-! ### The test can say no -/

set_option maxRecDepth 1000000 in
/-- A control: with two answers written into every shape of the list in front the test says no at
each record that keeps a message. There are 24 such records. -/
theorem smpB_no_answers :
    ((tableFullLit.filter fun r => !r.kept.isEmpty).all fun r =>
      !smpB { r with lo := r.lo.map fun x => ({ x.1 with answers := 2 }, x.2) }) = true ∧
    (tableFullLit.filter fun r => !r.kept.isEmpty).length = 24 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with main rows of degree 2 the test says no at each record that keeps a message. -/
theorem smpB_no_degree :
    ((tableFullLit.filter fun r => !r.kept.isEmpty).all fun r =>
      !smpB { r with lo := r.lo.map fun x => ({ x.1 with mainDeg := 2 }, x.2) }) = true := by
  decide +kernel

end Johnson.G

#print axioms Johnson.G.smpB_says
#print axioms Johnson.G.form_of_pad
#print axioms Johnson.G.sample_member_at
#print axioms Johnson.G.sample_member_full
#print axioms Johnson.G.sample_member_small
#print axioms Johnson.G.smpB_no_answers
#print axioms Johnson.G.smpB_no_degree
#print axioms Johnson.G.smpB_full
#print axioms Johnson.G.smpB_small
