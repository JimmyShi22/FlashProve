-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaTriesWires.lean: a bound on the probability expression for failed proof-of-work searches,
from the number of tests, a bound on their bits and a lower bound on the search limits.

Summary. `capFail` (Johnson/Prover/Law/Defs.lean) is the sum, over the rounds with a test, of
(1 - 2 ^ -b) ^ (cap i + 1). This file bounds it, and computes the number of tests and their bits
from the rounds' data, for a whole file's wiring and for the link's. The rounds' data are arbitrary.

Main results.
  `capFail_le_cnt`: if every test has at most β bits (`BitsLe β`) and 2 ^ β · k ≤ cap i + 1 for
    every i, then `capFail … ≤ cnt · 2 ^ -k`.
  `cnt_wqWhole`, `bits_wqWhole`, `cnt_wqW`, `bits_wqW`: the number of tests and the bound on their
    bits, for a whole file's wiring and for the link's, read off the rounds' data.

Terms: E2E/HidingTerms.lean.

Limits. `cnt` counts a test of either component, whatever the round's kind: it is an upper bound on
the rounds that `capFail` counts. Nothing is evaluated. No security property is stated.

Definitions and helper lemmas.
  `cnt s A W`, `cntR`: the tests of a wiring's rounds, of both components.
  `BitsLe β s A W`, `BitsR`: each has at most β bits.
  `testsT`, `testsR`, `testsW`: the rounds whose entry names bits of proof of work.
  `WorkLe β D`: none names more than β.
  `grFail_opt`: for one round's test, if there is one, of at most β bits, with 2 ^ β · k ≤ n + 1:
    `grFailAt n` of it is at most 2 ^ -k; if there is none it is 0.
  `cnt_app`, `bitsLe_app`, `cnt_wires`: wirings in a row; the six parts of a file.
  `cnt_wiresLo`, `cnt_wiresSh`, `cnt_wiresSL`, `bits_wiresLo`, `bits_wiresSh`, `bits_wiresSL`: a
    chain of rounds: the number of its tests and their bits.
  `bits_Dn`, `isSome_Dn`: a round's test has as many bits as the round's entry names, and there is
    one exactly if that number is not 0.


-/
import E2E.ZetaTries
import E2E.ZetaWires

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open OnBytes.Prover
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO Dn)

/-! ## 1. For an arbitrary wiring -/

section
variable {lam K : ℕ}

/-- One round's tests. -/
def cntR {r : Round} {a : RAnn r} (w : WireRB lam K r a) : ℕ :=
  w.grJ.isSome.toNat + w.gr0.isSome.toNat

/-- The tests of a wiring's rounds, of both components. -/
def cnt : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => cntR w + cnt s A W

/-- Every test of one round has at most β bits. -/
def BitsR (β : ℕ) {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop :=
  (∀ g, w.grJ = some g → g.b ≤ β) ∧ ∀ g, w.gr0 = some g → g.b ≤ β

/-- Every test of a wiring has at most β bits. -/
def BitsLe (β : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) => BitsR β w ∧ BitsLe β s A W

theorem grFail_opt {C P : Type} (o : Option (GrW C P)) (β k n : ℕ) (hb : ∀ g, o = some g → g.b ≤ β)
    (hn : 2 ^ β * k ≤ n + 1) : grFailAt n o ≤ (o.isSome.toNat : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ k := by
  cases o with
  | none => exact zero_le _
  | some g =>
    show _ ≤ ((1 : ℕ) : ℝ≥0∞) * _
    rw [Nat.cast_one, one_mul]
    exact grFail_le g β k n (hb g rfl) hn

/-- **The searches' failure, from a bound on the tests' bits and a lower bound on the search
limits.** -/
theorem capFail_le_cnt (β k : ℕ) (cap : ℕ → ℕ) (hc : ∀ i, 2 ^ β * k ≤ cap i + 1) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), BitsLe β s A W →
      capFail s A W cap i ≤ (cnt s A W : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ k
  | [], _, _, _, _ => zero_le _
  | _ :: s, (a, A), (w, W), i, h => by
    have ih := capFail_le_cnt β k cap hc s A W (i + 1) h.2
    have hJ := grFail_opt w.grJ β k (cap i) h.1.1 (hc i)
    have h0 := grFail_opt w.gr0 β k (cap i) h.1.2 (hc i)
    have hr : (match a.kind with
        | .lo => grFailAt (cap i) w.grJ
        | .sh => grFailAt (cap i) w.gr0) ≤ (cntR w : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ k := by
      unfold cntR
      rw [Nat.cast_add, add_mul]
      cases a.kind with
      | lo => exact le_trans hJ le_self_add
      | sh => exact le_trans h0 le_add_self
    show _ + capFail s A W cap (i + 1) ≤ ((cntR w + cnt s A W : ℕ) : ℝ≥0∞) * _
    rw [Nat.cast_add, add_mul]
    exact add_le_add hr ih

theorem cnt_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B), cnt (s ++ u) (RoundSplits.app A B) (WireSB.app W V) = cnt s A W + cnt u B V
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, _), _, (w, W), V => by
    show cntR w + cnt _ _ (WireSB.app W V) = cntR w + cnt _ _ W + cnt _ _ V
    rw [cnt_app W V]
    omega

theorem bitsLe_app {β : ℕ} : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, BitsLe β s A W → BitsLe β u B V →
      BitsLe β (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, bitsLe_app hW.2 hV⟩

/-- The six parts of a file. -/
theorem cnt_wires {G : Compile.Joined.Chains} (V : Wires lam K G) :
    cnt _ _ V.sh =
      cntR V.wF + (cnt _ _ V.W₁ + (cntR V.wJ + (cnt _ _ V.W₂ + (cntR V.w3 + cnt _ _ V.W₃)))) := by
  show cntR V.wF + cnt _ _ (WireSB.app V.W₁ V.shJ) = _
  rw [cnt_app]
  show cntR V.wF + (cnt _ _ V.W₁ + (cntR V.wJ + cnt _ _ (WireSB.app V.W₂ V.sh₃))) = _
  rw [cnt_app]
  rfl

end

/-! ## 2. For a whole file's wiring and for the link's -/

/-- A round's test has as many bits as the round's entry names bits of proof of work. -/
theorem bits_Dn {Cc P : Type} : ∀ (b : ℕ) (g : GrW (GChal b Cc) (GPlain ℕ b P)),
    (_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = some g → g.b = b
  | 0, _, h => by cases h
  | b + 1, g, h => by
    obtain rfl : TypedOracleCompiler.Tagged.ofGr (_root_.Iop.GrW.ofBits Dn b Cc P) = g := Option.some.inj h
    rfl

theorem isSome_Dn {Cc P : Type} : ∀ b : ℕ,
    ((_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr).isSome.toNat = (b != 0).toNat
  | 0 => rfl
  | _ + 1 => rfl

/-- The rounds of a chain whose entry names bits of proof of work. -/
def testsT (ds : List RDT) : ℕ := (ds.map fun d => (d.entry.work != 0).toNat).sum

/-- The same for the link's rounds. -/
def testsR (ds : List TypedOracleCompiler.Run.PQ.RD) : ℕ := (ds.map fun d => (d.entry.work != 0).toNat).sum

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem cnt_wiresLo : ∀ ds : List RDT, cnt _ _ (wiresLo C K chal ds) = testsT ds
  | [] => rfl
  | d :: ds => by
    show (_ + 0) + cnt _ _ (wiresLo C K chal ds) = (d.entry.work != 0).toNat + testsT ds
    rw [cnt_wiresLo ds, Nat.add_zero]
    exact congrArg (· + testsT ds) (isSome_Dn d.entry.work)

theorem cnt_wiresSh : ∀ ds : List RDT, cnt _ _ (wiresSh C K chal ds) = testsT ds
  | [] => rfl
  | d :: ds => by
    show (0 + _) + cnt _ _ (wiresSh C K chal ds) = (d.entry.work != 0).toNat + testsT ds
    rw [cnt_wiresSh ds, Nat.zero_add]
    exact congrArg (· + testsT ds) (isSome_Dn d.entry.work)

theorem cnt_wiresSL : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    cnt _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) = testsR ds
  | [] => rfl
  | d :: ds => by
    show (_ + 0) + cnt _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) =
      (d.entry.work != 0).toNat + testsR ds
    rw [cnt_wiresSL ds, Nat.add_zero]
    exact congrArg (· + testsR ds) (isSome_Dn d.entry.work)

theorem bits_wiresLo {β : ℕ} : ∀ ds : List RDT, (∀ d ∈ ds, d.entry.work ≤ β) →
    BitsLe β _ _ (wiresLo C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨fun g hg => (bits_Dn _ g hg).le.trans (h d List.mem_cons_self), (fun _ hg => by cases hg)⟩,
      bits_wiresLo ds fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem bits_wiresSh {β : ℕ} : ∀ ds : List RDT, (∀ d ∈ ds, d.entry.work ≤ β) →
    BitsLe β _ _ (wiresSh C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨(fun _ hg => by cases hg), fun g hg => (bits_Dn _ g hg).le.trans (h d List.mem_cons_self)⟩,
      bits_wiresSh ds fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem bits_wiresSL {β : ℕ} : ∀ ds : List TypedOracleCompiler.Run.PQ.RD, (∀ d ∈ ds, d.entry.work ≤ β) →
    BitsLe β _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨fun g hg => (bits_Dn _ g hg).le.trans (h d List.mem_cons_self), (fun _ hg => by cases hg)⟩,
      bits_wiresSL ds fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The rounds of a whole file whose entry names bits of proof of work. -/
def testsW (D : WholeD) : ℕ := testsT D.ds₁ + (testsT D.ds₂ + testsT D.ds₃)

/-- No round of a whole file names more than β bits of proof of work. -/
def WorkLe (β : ℕ) (D : WholeD) : Prop :=
  (∀ d ∈ D.ds₁, d.entry.work ≤ β) ∧ (∀ d ∈ D.ds₂, d.entry.work ≤ β) ∧ ∀ d ∈ D.ds₃, d.entry.work ≤ β

theorem cnt_wqWhole : cnt _ _ (wqWhole C K chal D tF tJ t3 silent run).sh = testsW D := by
  show cnt _ _ (wiresOf C K chal D tF tJ t3).sh = _
  rw [cnt_wires]
  show (0 + 0) + (cnt _ _ (wiresLo C K chal D.ds₁) + ((0 + 0) + (cnt _ _ (wiresSh C K chal D.ds₂) +
    ((0 + 0) + cnt _ _ (wiresLo C K chal D.ds₃))))) = _
  rw [cnt_wiresLo, cnt_wiresSh, cnt_wiresLo]
  unfold testsW
  omega

theorem bits_wqWhole {β : ℕ} (h : WorkLe β D) :
    BitsLe β _ _ (wqWhole C K chal D tF tJ t3 silent run).sh :=
  ⟨⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg)⟩,
    bitsLe_app (bits_wiresLo C K chal D.ds₁ h.1)
      ⟨⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg)⟩,
        bitsLe_app (bits_wiresSh C K chal D.ds₂ h.2.1)
          ⟨⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg)⟩,
            bits_wiresLo C K chal D.ds₃ h.2.2⟩⟩⟩

variable (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
  (dec : Y → View → Bool)

theorem cnt_wqW : cnt _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh = testsR ds := by
  show (0 + 0) + cnt _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) = _
  rw [cnt_wiresSL]
  omega

theorem bits_wqW {β : ℕ} (h : ∀ d ∈ ds, d.entry.work ≤ β) :
    BitsLe β _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh :=
  ⟨⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg)⟩, bits_wiresSL C K chal ds h⟩

end

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.capFail_le_cnt
#print axioms AtPublicFiles.ZetaAt.cnt_wqWhole
#print axioms AtPublicFiles.ZetaAt.bits_wqWhole
#print axioms AtPublicFiles.ZetaAt.cnt_wqW
#print axioms AtPublicFiles.ZetaAt.bits_wqW
#print axioms AtPublicFiles.ZetaAt.grFail_opt
#print axioms AtPublicFiles.ZetaAt.cnt_app
#print axioms AtPublicFiles.ZetaAt.bitsLe_app
#print axioms AtPublicFiles.ZetaAt.cnt_wires
#print axioms AtPublicFiles.ZetaAt.bits_Dn
#print axioms AtPublicFiles.ZetaAt.isSome_Dn
#print axioms AtPublicFiles.ZetaAt.cnt_wiresLo
#print axioms AtPublicFiles.ZetaAt.cnt_wiresSh
#print axioms AtPublicFiles.ZetaAt.cnt_wiresSL
#print axioms AtPublicFiles.ZetaAt.bits_wiresLo
#print axioms AtPublicFiles.ZetaAt.bits_wiresSh
#print axioms AtPublicFiles.ZetaAt.bits_wiresSL
