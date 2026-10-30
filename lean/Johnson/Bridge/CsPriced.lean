-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/CsPriced.lean: a code switch of a proximity test, in numbers: from two tests on
natural numbers: the code switch is taken off, and both of its rounds' error counts are at most
2^-128 of the round's written verifier messages, without the planner.

The statement on codes is not used in this file's own proofs: a code switch asks lists alone, and
these are the Johnson bound's. Through its imports the file stands above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

The like of Johnson/Bridge/FoldPriced.lean for a code switch. Definitions, statements and proofs.

Main names:
  `SwitchPlace`: the stage that is left and the stage that is entered, their radii, and the bits of
    work of the second round.
  `SwitchPlace.lst`: the Johnson bound's list of the entered stage at its radius.
  `SwitchPlace.cnt1`, `cnt2`: the library's two counts, written out at q = p^3: of the seed of the
    entered stage's sample: (lst choose 2) times the number of clashing seeds; of the positions and
    the batching element: (n - e - 1)^t q + n^t lst (1 + 3 t).
  `SwitchPlace.good`, `SwitchPlace.priced`: the two tests: the sizes fit and are in order and the
    entered radius is below the Johnson radius; the comparison of `below_of_num` at both rounds.
  `SwitchPlace.holds`, `below`: `CsHolds`, and `Err.Below` of `csErr`, at written rounds that are
    the format's own (`Fmt.M1.rSeed`, `Fmt.M1.rCs`).
  `SwitchPlace.Paid`, `paid`: what the two tests' yes gives, as one record.

Limits: NO PLACE IS WRITTEN HERE (Johnson/Bridge/CsAtWritten.lean). Of the radius of the stage that
is left nothing is asked. Of the 128 bits of the second round, `work` are proof of work: a share is
a count among all strings of hash blocks and test bits. A code switch is written at one answer to a
sample, as in OnBytes/Slice/BlockCs.lean. That a place's numbers are those of a file's plan is not
said here. No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.FoldPriced
import OnBytes.Slice.PricedRound
import OnBytes.Slice.ManyJohnsonErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop _root_.Run
open scoped ENNReal

/-! ## At letters: q in the place of the field's size -/

/-- The draws of the format's round «SEND seed». -/
theorem dsOf_rSeed (st : Fmt.M1.Stage) :
    Fmt.dsOf (Fmt.M1.rSeed st).entry (Fmt.M1.rSeed st).kind =
      List.replicate st.na Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by
  simp [Fmt.dsOf, Fmt.dsElems, Fmt.dsSeeds, Fmt.M1.rSeed, Nat.mod_one]

theorem nVals_rSeed {d : PQ.RD} {st : Fmt.M1.Stage} (hd : IsRd d (Fmt.M1.rSeed st)) (q : ℕ)
    (hq : Fintype.card GE = q) : nVals (Fmt.dsOf d.entry d.kind) = q ^ st.na * (q - 1) := by
  rw [hd.dsOf, dsOf_rSeed, nVals_seed, hq]

theorem seeds_pos (q : ℕ) (hq : Fintype.card GE = q) (na : ℕ) : 0 < q ^ na * (q - 1) :=
  hq ▸ Nat.mul_pos (Nat.pow_pos card_GE_pos) card_GE_pred_pos

/-- The typed values of a written round that draws positions and one element. -/
theorem nVals_posOne {d : PQ.RD} (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 0)
    (hT : d.entry.trits = 0) (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) (q : ℕ)
    (hq : Fintype.card GE = q) :
    nVals (Fmt.dsOf d.entry d.kind) = (2 ^ d.entry.logN) ^ d.entry.poss * q := by
  rw [nVals_dsOf _ _ hk1 hk2, hE, hZ, hT, ← hq, card_GE]
  simp

theorem err1_eq {s s' : Sg} (hf : CsFit s s') (L q : ℕ) (hq : Fintype.card GE = q) :
    (csSw hf).W.err1 L = L * (L - 1) / 2 * clashSeeds q s'.st.na := by
  rw [cs_err1, Nat.choose_two_right, hq]

theorem err2_eq {s s' : Sg} (hf : CsFit s s') (e L q : ℕ) (hq : Fintype.card GE = q) :
    (csSw hf).W.err2 e L =
      (2 ^ s.C.a - e - 1) ^ s.t * q + (2 ^ s.C.a) ^ s.t * (L * (1 + 3 * s.t)) := by
  rw [cs_err2, hq]

/-- A round that draws a seed: na elements and one other than 0, without work. -/
theorem below_seed (count N na : ℕ) (hN0 : 0 < N)
    (h : count * 2 ^ 193 + 3 * (na + 1 + 1) * N ≤ N * 2 ^ (0 + 65)) (d : PQ.RD)
    (hlog : d.entry.logN ≤ 64) (hE : d.entry.drawE = na + 1) (hZ : d.entry.drawNZ = 1)
    (hW : d.entry.work = 0) (hN : nVals (Fmt.dsOf d.entry d.kind) = N) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine below_of_num d hlog (by rw [hE, hZ]; exact Nat.le_add_left 1 na)
    (fun _ => by rw [hW]; decide) _ _ hN hN0 ?_
  simp only [hE, hZ, hW]
  exact h

/-- A round that draws positions and one element, with W bits of work. -/
theorem below_posOne (count N W : ℕ) (hN0 : 0 < N) (hW66 : W + 66 ≤ 128)
    (h : count * 2 ^ 193 + 3 * (1 + 0) * N ≤ N * 2 ^ (W + 65)) (d : PQ.RD)
    (hlog : d.entry.logN ≤ 64) (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 0)
    (hW : d.entry.work = W) (hN : nVals (Fmt.dsOf d.entry d.kind) = N) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine below_of_num d hlog (by rw [hE, hZ]; exact Nat.zero_le _)
    (fun _ => by rw [hW]; exact hW66) _ _ hN hN0 ?_
  simp only [hE, hZ, hW]
  exact h

/-! ## A code switch in numbers -/

/-- The stage that is left, the stage that is entered, their radii, and the bits of work of the
second round. -/
structure SwitchPlace where
  s : Sg
  s' : Sg
  e : ℕ
  e' : ℕ
  work : ℕ

namespace SwitchPlace
variable (x : SwitchPlace)

/-- The Johnson bound's list of the entered stage. -/
def lst : ℕ := x.s'.lstJ x.e'

/-- The number of all seeds of one answer. -/
def n1 : ℕ := (Cb.Gl.p ^ 3) ^ x.s'.st.na * (Cb.Gl.p ^ 3 - 1)

/-- The number of all lists of positions with a batching element. -/
def n2 : ℕ := (2 ^ x.s.C.a) ^ x.s.t * Cb.Gl.p ^ 3

/-- The first round's count. -/
def cnt1 : ℕ := x.lst * (x.lst - 1) / 2 * clashSeeds (Cb.Gl.p ^ 3) x.s'.st.na

/-- The second round's count. -/
def cnt2 : ℕ :=
  (2 ^ x.s.C.a - x.e - 1) ^ x.s.t * Cb.Gl.p ^ 3 + (2 ^ x.s.C.a) ^ x.s.t * (x.lst * (1 + 3 * x.s.t))

/-- The test on sizes and on the entered radius. -/
def good : Bool :=
  decide (CsFit x.s x.s') && Johnson.Top.H.sizedB x.s && Johnson.Top.H.sizedB x.s' &&
    Johnson.Top.H.inJB x.s' x.e'

/-- The comparison of `below_of_num` at the two rounds. -/
def priced : Bool :=
  decide (x.cnt1 * 2 ^ 193 + 3 * (x.s'.st.na + 1 + 1) * x.n1 ≤ x.n1 * 2 ^ (0 + 65)) &&
    decide (x.cnt2 * 2 ^ 193 + 3 * (1 + 0) * x.n2 ≤ x.n2 * 2 ^ (x.work + 65)) &&
    decide (x.work + 66 ≤ 128)

variable {x}

theorem fit (h : x.good = true) : CsFit x.s x.s' := by
  simp only [good, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem sized (h : x.good = true) : x.s.Sized := by
  simp only [good, Bool.and_eq_true] at h
  exact Johnson.Top.H.sized_of h.1.1.2

theorem sized' (h : x.good = true) : x.s'.Sized := by
  simp only [good, Bool.and_eq_true] at h
  exact Johnson.Top.H.sized_of h.1.2

theorem inJ' (h : x.good = true) : x.s'.InJ x.e' := by
  simp only [good, Bool.and_eq_true] at h
  exact ⟨(Johnson.Top.H.inJ_of h.2).1, (Johnson.Top.H.inJ_of h.2).2⟩

/-- **The code switch is taken off**, at written rounds that are the format's own, with the
library's error counts at the Johnson bound's list. -/
theorem holds (h : x.good = true) (hf : CsFit x.s x.s') {dS dC : PQ.RD} {tree W : ℕ}
    (hS : IsRd dS (Fmt.M1.rSeed x.s'.st)) (hC : IsRd dC (Fmt.M1.rCs x.work x.s.st tree W)) :
    CsHolds x.s x.s' x.e x.e' dS dC (csErr hf x.e x.lst dS dC) :=
  cs_holds_joh hf (sized h) (sized' h) x.e x.e' (inJ' h) hS hC

theorem priced1 (h : x.priced = true) :
    x.cnt1 * 2 ^ 193 + 3 * (x.s'.st.na + 1 + 1) * x.n1 ≤ x.n1 * 2 ^ (0 + 65) := by
  unfold priced at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1

theorem priced2 (h : x.priced = true) :
    x.cnt2 * 2 ^ 193 + 3 * (1 + 0) * x.n2 ≤ x.n2 * 2 ^ (x.work + 65) := by
  unfold priced at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).2

theorem priced3 (h : x.priced = true) : x.work + 66 ≤ 128 := by
  unfold priced at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 h).2

/-- The first round: the seed of the entered stage's sample. -/
theorem below1 (h : x.priced = true) (hf : CsFit x.s x.s') {d : PQ.RD}
    (hd : IsRd d (Fmt.M1.rSeed x.s'.st)) :
    RoundBelow ((csSw hf).W.err1 x.lst) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [err1_eq hf x.lst (Cb.Gl.p ^ 3) Cb.Gl.gl_card.2.1]
  exact below_seed x.cnt1 x.n1 x.s'.st.na (seeds_pos _ Cb.Gl.gl_card.2.1 _) (priced1 h) d
    ((congrArg Fmt.Entry.logN hd.entry).le.trans (Nat.zero_le 64))
    (congrArg Fmt.Entry.drawE hd.entry) (congrArg Fmt.Entry.drawNZ hd.entry)
    (congrArg Fmt.Entry.work hd.entry) (nVals_rSeed hd _ Cb.Gl.gl_card.2.1)

/-- The second round: the positions and the batching element. -/
theorem below2 (h : x.priced = true) (ha : x.s.C.a ≤ 64) (hf : CsFit x.s x.s') {d : PQ.RD}
    {tree W : ℕ} (hd : IsRd d (Fmt.M1.rCs x.work x.s.st tree W)) :
    RoundBelow ((csSw hf).W.err2 x.e x.lst) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hE : d.entry.drawE = 1 := congrArg Fmt.Entry.drawE hd.entry
  have hZ : d.entry.drawNZ = 0 := congrArg Fmt.Entry.drawNZ hd.entry
  have hT : d.entry.trits = 0 := congrArg Fmt.Entry.trits hd.entry
  have hL : d.entry.logN = x.s.C.a := congrArg Fmt.Entry.logN hd.entry
  have hP : d.entry.poss = x.s.t := congrArg Fmt.Entry.poss hd.entry
  have hk : d.kind = .positions := hd.kind
  have hN : nVals (Fmt.dsOf d.entry d.kind) = x.n2 := by
    rw [nVals_posOne hE hZ hT (by rw [hk]; decide) (by rw [hk]; decide) _ Cb.Gl.gl_card.2.1, hL,
      hP]
    rfl
  rw [err2_eq hf x.e x.lst (Cb.Gl.p ^ 3) Cb.Gl.gl_card.2.1]
  exact below_posOne x.cnt2 x.n2 x.work
    (Nat.mul_pos (pow_pos (Nat.two_pow_pos _) _) (Cb.Gl.gl_card.2.1 ▸ card_GE_pos)) (priced3 h)
    (priced2 h) d (hL.le.trans ha) hE hZ (congrArg Fmt.Entry.work hd.entry) hN

/-- **Both counts of the code switch.** -/
theorem below (hg : x.good = true) (hp : x.priced = true) (hf : CsFit x.s x.s') {dS dC : PQ.RD}
    {tree W : ℕ} (hS : IsRd dS (Fmt.M1.rSeed x.s'.st))
    (hC : IsRd dC (Fmt.M1.rCs x.work x.s.st tree W)) :
    Err.Below (csErr hf x.e x.lst dS dC) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  cs_below_joh hf x.e x.lst dS dC _ (below1 hp hf hS)
    (below2 hp (le_trans (sized hg).small (by decide)) hf hC)

/-- What is said of one place. -/
structure Paid (x : SwitchPlace) : Prop where
  /-- the two stages' sizes fit -/
  fit : CsFit x.s x.s'
  /-- the code switch is taken off, with the library's error counts at the Johnson bound's list -/
  holds : ∀ (hf : CsFit x.s x.s') (dS dC : PQ.RD) (tree W : ℕ), IsRd dS (Fmt.M1.rSeed x.s'.st) →
    IsRd dC (Fmt.M1.rCs x.work x.s.st tree W) →
    CsHolds x.s x.s' x.e x.e' dS dC (csErr hf x.e x.lst dS dC)
  /-- both of these counts are at most 2^-128 of their rounds' written verifier messages -/
  below : ∀ (hf : CsFit x.s x.s') (dS dC : PQ.RD) (tree W : ℕ), IsRd dS (Fmt.M1.rSeed x.s'.st) →
    IsRd dC (Fmt.M1.rCs x.work x.s.st tree W) →
    Err.Below (csErr hf x.e x.lst dS dC) ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem paid (hg : x.good = true) (hp : x.priced = true) : x.Paid :=
  ⟨fit hg, fun hf _ _ _ _ hS hC => holds hg hf hS hC, fun hf _ _ _ _ hS hC => below hg hp hf hS hC⟩

end SwitchPlace

end Johnson.Bridge

#print axioms Johnson.Bridge.SwitchPlace.holds
#print axioms Johnson.Bridge.SwitchPlace.below
#print axioms Johnson.Bridge.SwitchPlace.paid
