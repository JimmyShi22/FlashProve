-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Weights.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the public weights of seven of its masked sumchecks, AT ANY POINT r, read in a
field, are the library's weight polynomials at r, read. Definitions, and statements with their
proofs.

The prover's summands (Johnson/Desc/K5/Honest/Products.lean, Index.lean) call the verifier's own
weight functions with a point r laid in the place of one sumcheck's challenges. This library has,
for each of these functions, a lemma that reads it as the library's `Wb` (Inst/Model/Att/Sums.lean)
or `bitWt` (Cb/Pv/Att/Bits.lean) at the challenges heard, whatever these are:
Johnson/Desc/First/Att/K05Weights.lean, K05Weights2.lean, K05Weights3.lean, K05Weights4.lean. Here
these lemmas are called at r.

Main names:
  `PtsCut`, `pts_cut`   what the verifier's `pointsOf` lays into the fields that the prover reads
  `divIn_spec`          what `divIn` returns
  `Drawn`               the premise on the challenges' numbers
  `Planned`             the premise on the planner's numbers of these rounds
  `unitM_reads`, `unitD_reads`   a softmax-table unit below the diagonal, on it: steps s6b, s6d
  `division_reads`      the denominator times the output: step s8
  `below_reads`, `on_reads`      the value product below the diagonal, on it: steps s11, s12
  `IndexPts`, `atIndex_reads`   the score at the index: step s16
  `BitPts`, `cells_reads`       the index's cells are bits: `bitWt 4`
  `indexPts_pubOf`, `bitPts_pubOf`   the two premises hold at `pubOf`
  `DivPts`, `divPts_of`, `divPts_pubOf`, `keyPts_k3`, `KeysFit`, `keyPts_of_keysFit`
                        the premises on the lookup's points, from what the lookup hands on

Every statement is conditional but `size_powers`, `indexPts_pubOf` and `bitPts_pubOf`. Beside the
named premises below: each of the seven asks that r has enough coordinates and that b is below the
number of pairs; some take public equations on sizes by letter (g1 to g3) where others take `Sized`;
the two on a unit ask on which side of the diagonal it lies, and the length of the inner part of its
key point; `pts_cut`, `divIn_spec`, `divPts_of` and `divPts_pubOf` ask that the function they speak
of returns, `divPts_of` also that the batching element heard, read, is the library's; `keyPts_k3`
and `keysFit_of_calls` ask the library's `CallsFit`. The named premises, and who is meant to show
each:
  `LookPts`, `UnitPtsM`, `UnitPtsD` (the named files): the key points, read, are the library's.
    They follow from `KeyPtsAre` and `UnitIs` (Johnson/Desc/First/Att/K05LookAll.lean);
    `KeyPtsAre`, at the reading `Reading.gl`, follows from `K3Pts` and the public `KeysFit`;
    `K3Pts` is the lookup's to show of what it hands on, and
    `UnitIs` is public and has a test with code there (`unitOk`).
  `Sized` (Johnson/Desc/K5/Honest/Law/Cells.lean): public, the caller's.
  `Drawn`: that the one round which draws many elements has been heard with all of them: the
    caller's.
  `Planned`: public: the planner's numbers of these rounds are the shape's and the library's.
  `IndexPts`, `BitPts`: the library's challenges are the prover's, read: they hold at `pubOf`.
Tests of `Sized`, `Planned`, `Drawn` at small places: Johnson/Desc/K5/Honest/Law/PremisesToy.lean.
Limits. But for `IndexPts` and `BitPts` at `pubOf`, which hold by `pubOf`'s definition, nothing here
says that a premise holds at any place.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Cells
import Johnson.Desc.First.Att.K05Weights3
import Johnson.Desc.First.Att.K05Weights4
import Johnson.Desc.First.Att.K05LookAll
import Johnson.Desc.First.Att.Claims.KeysPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo geoOf eqTab ofNat chal Heard Left Pts W1 UnitG
  pointsOf piecesOf inner weights scoreW wDivision wBelow wOn wAtIndex wCells LookPts UnitPtsM
  UnitPtsD KeyPtsAre UnitIs K3Pts)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## What the verifier's function lays where -/

/-- **What `pointsOf` lays into the fields that the prover's division, value product and index
read.** -/
structure PtsCut (g : Geo) (zk : Array (Array E)) (h : Heard) (p : Pts) (uW : UnitG) : Prop where
  single : g.single .wl = some uW
  nZ : (inner uW (zk.getD uW.call #[])).size = 1 + g.lgk + g.lt + g.ldh
  pwW : p.d.pwW = piecesOf uW (zk.getD uW.call #[])
  nW : p.d.pwW.size = g.NP
  zgW : p.d.zgW = (inner uW (zk.getD uW.call #[])).extract 1 (1 + g.lgk)
  ziW : p.d.ziW = (inner uW (zk.getD uW.call #[])).extract (1 + g.lgk) (1 + g.lgk + g.lt)
  zcW : p.d.zcW =
    (inner uW (zk.getD uW.call #[])).extract (1 + g.lgk + g.lt) (1 + g.lgk + g.lt + g.ldh)
  gam : p.d.gam = h.gam.getD 1 zeroE
  scE : p.d.scE.r = chal h.division
  vpm : p.d.vpm.r = chal h.below
  vpd : p.d.vpd.r = chal h.on
  tg : p.x.tg = h.point.extract 0 g.lgk
  ti : p.x.ti = h.point.extract g.lgk (g.lgk + g.lt)
  scF : p.x.scF.r = chal h.atIndex
  scd : p.x.scd.r = chal h.key
  scH : p.x.scH.r = chal h.cells

theorem pts_cut {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) : ∃ uW, PtsCut g zk h p uW := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, hW, uX, hX, uH, hH, _, hs, _, hz, e⟩ := hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hs hz
  subst e
  exact ⟨uW, hW, hz.1.1, rfl, hs.1.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What `divIn` returns.** -/
theorem divIn_spec {P : Pub5} {c : Chal} {Dv : DivIn} (h : divIn P c = some Dv) :
    ∃ pts wl, ptsOf P c = some pts ∧ P.g.single .wl = some wl ∧ Dv.d = pts.d ∧
      Dv.pw = weights wl (c.zk.getD wl.call #[]) ∧ Dv.zW = inner wl (c.zk.getD wl.call #[]) ∧
      Dv.h = (heardAt P c fun _ => none) ∧ Dv.ec = eqTab pts.d.zcW := by
  unfold divIn at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨pts, h1, wl, h2, e⟩ := h
  subst e
  exact ⟨pts, wl, h1, h2, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The premises -/

/-- **The premise on the challenges' numbers**: the round that draws many elements has been heard
with all its elements. -/
structure Drawn (P : Pub5) (c : Chal) : Prop where
  point : 2 * P.D.lg + 2 * P.D.lT + 4 ≤ (c.many (firstOf P.x (iZero P.x))).size

/-- **The premise on the planner's numbers of these rounds**: its numbers of pairs, of a token's
bits, of a head's bits and of layers are the shape's, and six of the sumchecks have the library's
numbers of variables. Public. -/
structure Planned (P : Pub5) : Prop where
  pairs : P.x.pairs = P.g.NP
  lt : P.x.lt = P.g.lt
  lgk : P.x.lgk = P.g.lgk
  Lam : P.x.Lam = P.g.Lam
  vSE : (cut P.x).getD (iSE P.x) 3 - 3 = Step.s8.g P.D
  vVM : (cut P.x).getD (iVM P.x) 3 - 3 = Step.s11.g P.D
  vVD : (cut P.x).getD (iVD P.x) 3 - 3 = Step.s12.g P.D
  vSF : (cut P.x).getD (iSF P.x) 3 - 3 = Step.s16.g P.D
  vSD : (cut P.x).getD (iSD P.x) 3 - 3 = g18 P.D
  vHB : (cut P.x).getD (iHB P.x) 3 - 3 = P.D.lT + P.D.lg + 4

theorem size_powers (y : E) (n : ℕ) : (powers y n).size = n := by
  have len : ∀ (n : ℕ) (a : E),
      (VerifiableInference.Desc.Part.MaskedSum.powersFrom y n a).length = n := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      show (a :: VerifiableInference.Desc.Part.MaskedSum.powersFrom y n (mulE a y)).length = n + 1
      rw [List.length_cons, ih]
  unfold powers
  rw [List.size_toArray]
  exact len n oneE

/-! ## The seven weights -/

/-- **A softmax-table unit below the diagonal.** -/
theorem unitM_reads (D : Dim) (C : Calls) (p : Pub K) {g : Geo} {u : UnitG} {zk : Array E}
    (hbl : u.below = true) (lp : UnitPtsM ρ D C p.z u zk) (g2 : g.lgk = D.lg)
    (g3 : g.lnT = D.lP + 1) (hz : (inner u zk).size = g.lgk + (g.lnT - 1) + g.lnT + 2 * g.lB)
    (r : Array E) (hr : D.lg + D.lP + (D.lP + 1) ≤ r.size) {b : ℕ} (hb : b < D.nb) :
    ρ.val (((scoreW g u zk r).getD #[]).getD b zeroE) = Wb D C p .s6b b (pt ρ r) := by
  have hs : ∃ Wt, scoreW g u zk r = some Wt := by
    unfold scoreW
    simp [hbl, hz, guard]
  obtain ⟨Wt, e⟩ := hs
  rw [e]
  exact VerifiableInference.Desc.First.Att.P.unitM_weight D C p hbl e lp g2 g3 hr hb

/-- **A softmax-table unit on the diagonal.** -/
theorem unitD_reads (D : Dim) (C : Calls) (p : Pub K) {g : Geo} {u : UnitG} {zk : Array E}
    (hbl : u.below = false) (lp : UnitPtsD ρ D C p.z u zk) (g2 : g.lgk = D.lg)
    (g3 : g.lnT = D.lP + 1) (hz : (inner u zk).size = g.lgk + g.lnT + 2 * g.lB)
    (r : Array E) (hr : D.lg + (D.lP + 1) ≤ r.size) {b : ℕ} (hb : b < D.nb) :
    ρ.val (((scoreW g u zk r).getD #[]).getD b zeroE) = Wb D C p .s6d b (pt ρ r) := by
  have hs : ∃ Wt, scoreW g u zk r = some Wt := by
    unfold scoreW
    simp [hbl, hz, guard]
  obtain ⟨Wt, e⟩ := hs
  rw [e]
  exact VerifiableInference.Desc.First.Att.P.unitD_weight D C p hbl e lp g2 g3 hr hb

/-- **The denominator times the output.** -/
theorem division_reads (D : Dim) (C : Calls) (p : Pub K) (g : Geo) (h : Heard) {pw zW : Array E}
    (lp : LookPts ρ D C p.z pw zW) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg) (r : Array E)
    (hr : D.lg + D.lT ≤ r.size) {b : ℕ} (hb : b < D.nb) :
    ρ.val ((wDivision g pw zW { h with division := sumAt r }).getD b zeroE) =
      Wb D C p .s8 b (pt ρ r) := by
  have e := VerifiableInference.Desc.First.Att.P.division_weight D C p g
    { h with division := sumAt r } lp g1 g2 (by rw [chal_sumAt]; exact hr) hb
  rw [chal_sumAt] at e
  exact e

/-- **The value product below the diagonal.** -/
theorem below_reads {P : Pub5} (H : Sized P) (C : Calls) (p : Pub K) (h : Heard)
    {pw zW : Array E} (lp : LookPts ρ P.D C p.z pw zW) (r : Array E)
    (hr : P.D.lg + P.D.lP + (P.D.lP + 1) ≤ r.size) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val ((wBelow P.g pw zW { h with below := sumAt r }).getD b zeroE) =
      Wb P.D C p .s11 b (pt ρ r) := by
  have e := VerifiableInference.Desc.First.Att.P.below_weight P.S H.Z C p
    { h with below := sumAt r } lp H.lt (by
      rw [chal_sumAt]
      have := H.lnT
      show P.D.lg + P.D.lP + P.g.lnT ≤ r.size
      omega) hb
  rw [chal_sumAt] at e
  exact e

/-- **The value product on the diagonal.** -/
theorem on_reads (D : Dim) (C : Calls) (p : Pub K) (g : Geo) (h : Heard) {pw zW : Array E}
    (lp : LookPts ρ D C p.z pw zW) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg)
    (g3 : g.lnT = D.lP + 1) (r : Array E) (hr : D.lg + (D.lP + 1) ≤ r.size) {b : ℕ}
    (hb : b < D.nb) :
    ρ.val ((wOn g pw zW { h with on := sumAt r }).getD b zeroE) = Wb D C p .s12 b (pt ρ r) := by
  have e := VerifiableInference.Desc.First.Att.P.on_weight D C p g
    { h with on := sumAt r } lp g1 g2 g3 (by rw [chal_sumAt]; exact hr) hb
  rw [chal_sumAt] at e
  exact e

/-- **What the weight of the score at the index reads of the challenges**: the batching element's
powers and two cuts of the round that draws many elements, read, are the library's o, tg and ti. -/
structure IndexPts (ρ : Reading K) (P : Pub5) (c : Chal) (p : Pub K) : Prop where
  o : ∀ b < P.D.nb, pt ρ (heardAt P c fun _ => none).om b = p.o b
  tg : ∀ k < P.D.lg, pt ρ (heardAt P c fun _ => none).point k = p.tg k
  ti : ∀ k < P.D.lT, pt ρ (heardAt P c fun _ => none).point (P.D.lg + k) = p.ti k

theorem indexPts_pubOf (P : Pub5) (c : Chal) (z : ℕ → K) : IndexPts ρ P c (pubOf ρ P c z) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The score at the index.** -/
theorem atIndex_reads {P : Pub5} (H : Sized P) (Pl : Planned P) {c : Chal} (Dr : Drawn P c)
    (C : Calls) {p : Pub K} (I : IndexPts ρ P c p) (r : Array E) (hr : P.D.lT + P.D.lg ≤ r.size)
    {b : ℕ} (hb : b < P.D.nb) :
    ρ.val ((wAtIndex P.g { (heardAt P c fun _ => none) with atIndex := sumAt r }).getD b zeroE) =
      Wb P.D C p .s16 b (pt ρ r) := by
  have hp := Dr.point
  have e := VerifiableInference.Desc.First.Att.P.atIndex_weight (ρ := ρ) P.D C p P.g
    { (heardAt P c fun _ => none) with atIndex := sumAt r } (b := b)
    (by
      show b < (powers _ P.x.pairs).size
      rw [size_powers, Pl.pairs]
      exact hb)
    H.lt rfl
    (by
      show P.D.lg + P.D.lT ≤ (c.many (firstOf P.x (iZero P.x))).size
      omega)
    (by rw [chal_sumAt]; exact hr) (I.o b hb) I.tg I.ti
  rw [chal_sumAt] at e
  exact e

/-- **What the weight of "the index's cells are bits" reads of the challenges**: the batching
element's powers and three cuts of the round that draws many elements, read, are the library's o'',
tk, tbg and tbi. -/
structure BitPts (ρ : Reading K) (P : Pub5) (c : Chal) (p : Pub K) : Prop where
  o'' : ∀ b < P.D.nb, pt ρ (heardAt P c fun _ => none).om'' b = p.o'' b
  tk : ∀ k < 4, pt ρ (heardAt P c fun _ => none).point (P.D.lg + P.D.lT + k) = p.tk k
  tbg : ∀ k < P.D.lg, pt ρ (heardAt P c fun _ => none).point (P.D.lg + P.D.lT + 4 + k) = p.tbg k
  tbi : ∀ k < P.D.lT,
    pt ρ (heardAt P c fun _ => none).point (2 * P.D.lg + P.D.lT + 4 + k) = p.tbi k

theorem bitPts_pubOf (P : Pub5) (c : Chal) (z : ℕ → K) : BitPts ρ P c (pubOf ρ P c z) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The index's cells are bits.** -/
theorem cells_reads {P : Pub5} (H : Sized P) (Pl : Planned P) {c : Chal} (Dr : Drawn P c)
    {p : Pub K} (I : BitPts ρ P c p) (r : Array E) (hr : P.D.lT + P.D.lg + 4 ≤ r.size) {b : ℕ}
    (hb : b < P.D.nb) :
    ρ.val ((wCells P.g { (heardAt P c fun _ => none) with cells := sumAt r }).getD b zeroE) =
      Cb.Pv.Att.bitWt 4 P.D p b (pt ρ r) := by
  have e := VerifiableInference.Desc.First.Att.P.cells_weight (ρ := ρ) P.D p P.g
    { (heardAt P c fun _ => none) with cells := sumAt r } (b := b)
    (by
      show b < (powers _ P.x.pairs).size
      rw [size_powers, Pl.pairs]
      exact hb)
    H.lt rfl Dr.point (by rw [chal_sumAt]; exact hr) (I.o'' b hb) I.tk I.tbg I.tbi
  rw [chal_sumAt] at e
  exact e

/-! ## The premises on the lookup's points, from what the lookup hands on -/

/-- **What the division's and the value product's summands read of the lookup's points**, at what
`divIn` returns: the pieces' weights and the cuts of the inner point of the list of the remainders'
low bits, read, are the library's; the batching element is the library's. p: any challenges of the
library's: of its fields the three steps read z and th alone. -/
structure DivPts (ρ : Reading K) (P : Pub5) (C : Calls) (p : Pub K) (Dv : DivIn) : Prop where
  look : LookPts ρ P.D C p.z Dv.pw Dv.zW
  nC : Dv.d.zcW.size = P.D.ln
  hn : ∀ k < P.D.ln, pt ρ Dv.d.zcW k = yn P.D C p.z k
  nLo : (Dv.d.zilo P.g).size = P.D.lB
  hlo : ∀ k < P.D.lB, pt ρ (Dv.d.zilo P.g) k = yi' P.D C p.z k
  ec : Dv.ec = eqTab Dv.d.zcW
  gam : ρ.val Dv.d.gam = p.th

/-- These hold where the key points, read, are the library's, the list's unit is the library's
family, and the batching element heard, read, is the library's. -/
theorem divPts_of {P : Pub5} (H : Sized P) {c : Chal} {Dv : DivIn} (h : divIn P c = some Dv)
    {C : Calls} {p : Pub K} (Kp : KeyPtsAre ρ C p.z c.zk)
    (UW : ∀ wl, P.g.single .wl = some wl → ∃ q, UnitIs P.D C .w3 q wl)
    (hth : ρ.val ((heardAt P c fun _ => none).gam.getD 1 zeroE) = p.th) :
    DivPts ρ P C p Dv := by
  obtain ⟨pts, wl, h1, h2, ed, e1, e2, eh, ec⟩ := divIn_spec h
  obtain ⟨u, Cu⟩ := pts_cut h1
  have eu : u = wl := Option.some.inj (Cu.single.symm.trans h2)
  subst eu
  obtain ⟨q, U⟩ := UW u h2
  have hlt := H.lt
  have hnT := H.lnT
  have hT : P.D.lT = P.D.lP + 1 + P.D.lB := rfl
  have nZ := Cu.nZ
  have rd : ∀ j < P.D.lW, pt ρ (inner u (c.zk.getD u.call #[])) j = uW P.D C p.z j :=
    fun j hj => VerifiableInference.Desc.First.Att.P.inner_read Kp U j hj
  have hW : P.D.lW = 1 + P.D.lg + P.D.lT + P.D.ln := rfl
  have g2 : P.g.lgk = P.D.lg := rfl
  have g4 : P.g.ldh = P.D.ln := rfl
  have g5 : P.g.lB = P.D.lB := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2]
    exact VerifiableInference.Desc.First.Att.P.lookPts_of Kp U
  · rw [ed, Cu.zcW, size_extract_le _ (by omega)]
    omega
  · intro k hk
    rw [ed, Cu.zcW, pt_extract ρ _ _ _ k (by omega), rd _ (by omega), g2, hlt]
    rfl
  · unfold VerifiableInference.Desc.First.Att.P.DivP.zilo
    rw [ed, Cu.ziW, size_extract_le _ (by rw [size_extract_le _ (by omega)]; omega)]
    omega
  · intro k hk
    unfold VerifiableInference.Desc.First.Att.P.DivP.zilo
    rw [ed, Cu.ziW, pt_extract ρ _ _ _ k (by omega), pt_extract ρ _ _ _ _ (by omega),
      rd _ (by omega), g2, hnT]
    show uW P.D C p.z (1 + P.D.lg + (P.D.lP + 1 + k)) =
      uW P.D C p.z (1 + P.D.lg + (P.D.lP + 1) + k)
    rw [Nat.add_assoc (1 + P.D.lg)]
  · rw [ec, ed]
  · rw [ed, Cu.gam]
    exact hth

/-- The same at the library's challenges made of the prover's. -/
theorem divPts_pubOf {P : Pub5} (H : Sized P) {c : Chal} {Dv : DivIn} (h : divIn P c = some Dv)
    {C : Calls} {z : ℕ → K} (Kp : KeyPtsAre ρ C z c.zk)
    (UW : ∀ wl, P.g.single .wl = some wl → ∃ q, UnitIs P.D C .w3 q wl) :
    DivPts ρ P C (pubOf ρ P c z) Dv :=
  divPts_of ρ H h (p := pubOf ρ P c z) Kp UW rfl

/-- The key points, read, are the library's, where they are cut of the lookup's two points as
`K3Pts` says. -/
theorem keyPts_k3 {P : Pub5} {c : Chal} {fs : OnBytes.Model.Forest.Shape}
    (hf : OnBytes.Road.L5.CallsFit P.S fs) {zx zy : Array E} {z : ℕ → Cb.Gl.E}
    (H3 : K3Pts fs zx zy c.zk z) : KeyPtsAre Reading.gl (OnBytes.Road.L5.callsOf fs) z c.zk :=
  VerifiableInference.Desc.First.Att.P.keyPts_of_k3 hf H3

/-- **The three clauses on the lookup's numbers that the key points' cut spends**: a call has at
least a tree's keys, and the lookup's number of bits of a call's trees is the library's and at most
the number of coordinates of zy. Public; three of the clauses of this library's `CallsFit`
(Johnson/Road/Lane5CallsOf.lean). -/
def KeysFit (fs : OnBytes.Model.Forest.Shape) : Prop :=
  ∀ q : Fin 4, (OnBytes.Road.L5.callsOf fs).Dk ≤ (OnBytes.Road.L5.callsOf fs).a q ∧
    fs.iota.getD q.val 0 = (OnBytes.Road.L5.callsOf fs).e q ∧
    (OnBytes.Road.L5.callsOf fs).e q ≤ fs.rK

theorem keysFit_of_calls {S : OnBytes.Attention.Shape} {fs : OnBytes.Model.Forest.Shape}
    (h : OnBytes.Road.L5.CallsFit S fs) : KeysFit fs := fun q =>
  ⟨h.2.1 q, (OnBytes.Road.L5.callsFit_iota h q).1, (OnBytes.Road.L5.callsFit_iota h q).2⟩

/-- The same as `keyPts_k3` from these three clauses alone. -/
theorem keyPts_of_keysFit {zk : Array (Array E)} {fs : OnBytes.Model.Forest.Shape}
    (hf : KeysFit fs) {zx zy : Array E} {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z) :
    KeyPtsAre Reading.gl (OnBytes.Road.L5.callsOf fs) z zk where
  size := fun q => by
    obtain ⟨h3, h1, h2⟩ := hf q
    have hDk : (OnBytes.Road.L5.callsOf fs).Dk = fs.dT := rfl
    have he : (OnBytes.Road.L5.callsOf fs).e q =
      (OnBytes.Road.L5.callsOf fs).a q - (OnBytes.Road.L5.callsOf fs).Dk := rfl
    rw [H3.zk q, Array.size_append, Array.size_extract, H3.nx, H3.ny, h1]
    omega
  read := fun q i hi => by
    rw [H3.zk q, H3.z]
    exact OnBytes.Road.L5.zk_eq_zC fs zx zy H3.nx H3.ny q (hf q).2.1 (hf q).2.2 (hf q).1 i hi

end H2K5.Honest

#print axioms H2K5.Honest.pts_cut
#print axioms H2K5.Honest.divIn_spec
#print axioms H2K5.Honest.size_powers
#print axioms H2K5.Honest.unitM_reads
#print axioms H2K5.Honest.unitD_reads
#print axioms H2K5.Honest.division_reads
#print axioms H2K5.Honest.below_reads
#print axioms H2K5.Honest.on_reads
#print axioms H2K5.Honest.indexPts_pubOf
#print axioms H2K5.Honest.atIndex_reads
#print axioms H2K5.Honest.bitPts_pubOf
#print axioms H2K5.Honest.cells_reads
#print axioms H2K5.Honest.divPts_of
#print axioms H2K5.Honest.divPts_pubOf
#print axioms H2K5.Honest.keyPts_k3
#print axioms H2K5.Honest.keysFit_of_calls
#print axioms H2K5.Honest.keyPts_of_keysFit
