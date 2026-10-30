-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/FoeZeta.lean: TESTS THAT HOLD THE PREMISES AND THE ERROR of the statement of index
privacy (PremW, Johnson/WholeKey/Premises.lean; zetaW, Johnson/WholeKey/Zeta.lean): two summands of
the error cannot be struck.

Statements and proofs. Toys: nothing here is about the protocol of the release. This file states no
goal of the release.

Why. A theorem "PremW → index privacy at zetaW" would compile as well with a larger error. That no
summand of zetaW is idle wants, for each summand, letters at which PremW holds and index privacy
FAILS at the error without that summand. Here that is shown for two of them.
  parts_bite THE SESSIONS' SIMULATION ERROR, n · zO. At the teller (Johnson/WholeKey/FoeScheme.lean:
    the session's honest side lays the index's bit in a plain part):
      PremW holds at the numbers nuG 1 0: those of the second member, but zO = 1;
      so the scheme has index privacy at zetaW at these numbers (the theorem wholeKeyPrivacy,
      Johnson/WholeKey/Main.lean, called);
      zetaW at these numbers is zetaW at the second member's numbers nu2, plus n;
      and at zetaW at nu2, which is the error with n · zO struck, index privacy fails FOR EVERY
      SIMULATOR.
  stops_bite THE SESSIONS' STOPS, n · hO. The like at the stopper (the session's honest side stops
    at one of the two indices in range), at the numbers nuG 0 1: hO = 1. There zO = 0: where the
    honest side does not stop the simulator is exact, and where it stops nothing is asked of a
    simulator.
So if either summand were struck from zetaW, the statement of index privacy would be false.
  guess_member AN ERROR LETTER STRICTLY BETWEEN 0 AND 1. At the teller, with a simulator that lays a
    bit of the verifier's randomness where the index's bit stands: it is right at half of the
    verifier's randomness, so PremW holds at zO = 1/2, and the scheme, WHICH TELLS THE INDEX, has
    index privacy at an error that is below 1 at no query and one request (at most 1/2 + 62 / 2^32).
    So "below 1" is too low a bar: nothing is said until ζ + ζ < 1 (Johnson/WholeKey/Half.lean,
    whose head argues this example). And the summand is nearly tight there: whatever the simulator,
    the error is at least 15/32.

Main names (namespace OnBytes.WholeKey.FoeScheme).
  premW_atG    PremW at a scheme of the family, for any simulator of sessions, from the two clauses
               on sessions.
  zeta_atG     zetaW does not hang on what the session's honest side sends or where it stops.
  zeta01       zetaW at the second member's numbers, at no query and one request: at most 62 / 2^32.
  no_privacy_small   an error that is at most 62 / 2^32 at (0, 1) contradicts the lower bound.

"PASSES THE BAR" IS NOT "HIDES". ζ + ζ < 1 is where the statement begins to speak, no more. The
lower bound for the teller is 15/32, which is below 1/2. Argued, not typed: a simulator that mixes
the two indices would bring the teller's error to (1 - β)/2, with β the share of its proofs that
hold no string (Lean has β ≤ 1/16 alone): if β is not 0, a scheme that tells its index in every
proof that holds a string would pass the bar. A bar that shuts out a prover that tells outright is ζ
+ ζ + α < 1, with α the completeness error, which β does not exceed. Quote numbers, not "passes the
bar".
Limits. Toys. parts_bite and stops_bite try their summands at zO = 1 and hO = 1, where zetaW is 1 or
more and the theorem says nothing: they show that the summands are NEEDED. That one is nearly TIGHT
is shown for n · zO alone, at n = 1 and zO = 1/2. Nothing here tries zT, zL, hT, hL, the summand for
an overrun, the summand for the seeds, the summand for the hashes, or the budgets. NO MEMBER IS
SHOWN AT WHICH AN ERROR LETTER IS NOT 0 AND THE BAR ζ + ζ < 1 IS PASSED: at this object the seeds
are two, so a bad seed costs 3/2; and a share of the verifier's randomness below 1/4 wants the
measure of a set of two bits or more of the block, which is not typed.
The sum over the oracles' names follows hash_pad (Johnson/WholeKey/Member.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.FoeScheme
import Johnson.WholeKey.Main

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey.FoeScheme
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WholeKey.Member2
open OnBytes.WholeKey.Member (pick pick_ok)
open Hiop.Seeded.Two
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A block of 32 bits (Hiop/Seeded/Pad2.lean). -/
local notation "Blk₂" => Hiop.Seeded.Two.Blk

/-! ## PremW at a scheme of the family -/

section Fam
variable (say : Option Bool → Bool → Bool) (stp : Option Bool → Bool)

theorem coinsG : CoinsFit W2 p2 (atG say stp) cn2 where
  ri := pick_ok _
  kT := pick_ok _
  kL := pick_ok _
  kB := pick_ok _
  sl := saltsLaw_saltsPre [false] (2 ^ 0) 32 (pick _) (pick_ok _)
  len₀ := rfl
  okT := fun _ => trivial
  okL := fun _ => trivial
  okB := fun _ => trivial
  lenT := fun _ _ _ _ _ _ _ => rfl
  lenL := fun _ _ _ _ _ _ _ => rfl
  lenB := fun _ _ _ _ _ _ _ => rfl
  coT := co2_law
  coL := co2_law
  coB := co2_law
  rounds := coins2.rounds
  winT := coins2.winT
  winL := coins2.winL
  winB := coins2.winB

/-- The numbers of the second member, but for the two on sessions. -/
def nuG (zO hO : ℝ≥0∞) : NumsW := ⟨3, 1, 1, 1, 1, 2, 0, 0, zO, 0, 0, hO, 0⟩

/-- PremW at a scheme of the family, from the two clauses on sessions. -/
theorem premW_atG (sB : ℕ → Compile.Lifetime.SimOf pad2.onlineBatch.loc)
    (Ryes : Option Bool → Unit → Prop) (zO hO : ℝ≥0∞)
    (hG : ∀ n i r e x, ok2 i → Ryes i x →
      pr (unif (Rho pad2.onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh ρ ∉
            (sessionAt (recsG2 say stp) n).Hid (i, r, e) (x, pad2.recOf i r e) ∧
          (sessionAt (recsG2 say stp) n).output (i, r, e) (x, pad2.recOf i r e)
            (RoundsQueryLayout.zero pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh ρ) ≠
          sB n (x, pad2.recOf i r e)
            (RoundsQueryLayout.zero pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh ρ)
            (pad2.onlineBatch.loc.extAns (x, pad2.recOf i r e)
              (RoundsQueryLayout.zero pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh ρ) (pad2.encodeIndex i r))} ≤ zO)
    (hS : ∀ n i r e x, ok2 i → Ryes i x →
      pr (unif (Rho pad2.onlineBatch.loc.shape))
        {ρ | RoundsQueryLayout.zero pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh ρ ∈
          (sessionAt (recsG2 say stp) n).Hid (i, r, e) (x, pad2.recOf i r e)} ≤ hO) :
    PremW W2 S2 cA2 p2 (atG say stp) ⟨simT, simL, sB⟩ ok2 (fun _ => True) Ryes cn2
      (nuG zO hO) where
  ext := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  runVals :=
    ⟨fun _ _ _ _ ρ _ _ => by
        obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
        rfl,
      fun _ _ _ _ ρ _ _ => by
        obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
        rfl,
      fun _ _ _ _ _ _ _ _ _ => rfl⟩
  reads := pad2_readsG 3
  budget₀ := le_rfl
  budget₁ := le_rfl
  good :=
    ⟨fun i r e hi _ =>
        le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h.2 (exactT (i, r, e) hi _ _)),
      fun i r e r' e' hi _ _ =>
        le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
          h.2 (exactL (i, (r, e), (r', e')) hi _ _)),
      fun n i r e x hi _ hx => hG n i r e x hi hx⟩
  stops :=
    ⟨fun _ _ _ hi _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hi h),
      fun _ _ _ _ _ hi _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hi h),
      fun n i r e x hi _ hx => hS n i r e x hi hx⟩
  seeds := le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h trivial)
  freeT := fun _ _ _ _ => rfl
  freeL := fun _ _ _ _ => rfl
  freeB := fun _ _ _ _ => rfl
  wires := oka
  fmt := fmt2
  backT := ⟨fun _ e => (by cases e), trivial⟩
  backL := ⟨fun _ e => (by cases e), trivial⟩
  backB := ⟨fun g e k α _ => by
    have e' : gr = g := Option.some.inj e
    rw [← e']
    rfl, fun _ e => (by cases e), trivial⟩
  plain := ⟨rfl, rfl⟩
  coherent := wiresFit2.coh
  isLocal := wiresFit2.loc
  coins := coinsG say stp

/-- zetaW reads of the honest side's letters the number of copies and the caps alone. -/
theorem zeta_atG (u : NumsW) : zetaW W2 S2 p2 (atG say stp) cn2 u = zetaW W2 S2 p2 at2 cn2 u := rfl

end Fam

/-! ## The error of the second member's numbers at no query and one request -/

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

theorem hash01 :
    Rom.costTotal (S := typedOracleFamily 32 W2.K C2) (eW W2 S2 at2 1) (mW W2 at2 1) (bitsW (lam := 32) p2 cn2)
      (osW W2 at2) 0 ≤ 62 / 4294967296 := by
  have key : ∑ o ∈ ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link,
      .fb .onl, .fbw .onl 0, .fbw .onl 1, .fbw .onl 2} : Finset ON₂),
      (mW W2 at2 1 o : ℝ≥0∞) * ((0 + eW W2 S2 at2 1 o + mW W2 at2 1 o : ℕ) : ℝ≥0∞) /
        2 ^ bitsW (lam := 32) p2 cn2 o = 62 / 4294967296 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    show ((4 : ℕ) : ℝ≥0∞) * ((0 + 0 + 4 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((4 : ℕ) : ℝ≥0∞) * ((0 + 0 + 4 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((0 : ℕ) : ℝ≥0∞) * ((0 + 0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((0 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((2 : ℕ) : ℝ≥0∞) * ((0 + 0 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((0 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((0 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((2 : ℕ) : ℝ≥0∞) * ((0 + 0 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((2 : ℕ) : ℝ≥0∞) * ((0 + 6 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((0 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((0 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      ((1 : ℕ) : ℝ≥0∞) * ((0 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32)))))))))) = 62 / 4294967296
    simp only [ENNReal.div_add_div_same]
    norm_num
  refine (Rom.costTotal_le _ _ _ _ _).trans (le_of_eq ?_)
  unfold Rom.costNames
  rw [os_pad2]
  exact key

/-- One request cannot overrun a copy that serves two. -/
theorem tail01 : Prob.pOver (at2.M + 1) nu2.s1 1 = 0 := by
  refine le_antisymm ((Prob.pOver_le_choose 2 2 1).trans (le_of_eq ?_)) (zero_le _)
  have hc : Nat.choose 1 (2 + 1) = 0 := by decide
  rw [hc]
  simp

theorem zeta01 : zetaW W2 S2 p2 at2 cn2 nu2 0 1 ≤ 62 / 4294967296 := by
  have hz : zetaW W2 S2 p2 at2 cn2 nu2 0 1 =
      Rom.costTotal (S := typedOracleFamily 32 W2.K C2) (eW W2 S2 at2 1) (mW W2 at2 1)
        (bitsW (lam := 32) p2 cn2) (osW W2 at2) 0 := by
    unfold zetaW
    rw [tail01]
    show (0 : ℝ≥0∞) + (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + ((1 : ℕ) : ℝ≥0∞) * 0) +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + ((1 : ℕ) : ℝ≥0∞) * 0) + ((1 + 2 : ℕ) : ℝ≥0∞) * 0 + _ = _
    simp
  rw [hz]
  exact hash01

/-- The numbers: 62 / 2^32 twice and 1/16 do not add up to 1. -/
theorem no_privacy_small {z : ℝ≥0∞} (hz : z ≤ 62 / 4294967296) : ¬ (1 ≤ z + z + 16⁻¹) := by
  have e16 : (16⁻¹ : ℝ≥0∞) = 268435456 / 4294967296 := by
    rw [← one_div, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  refine not_le.2 (lt_of_le_of_lt (add_le_add (add_le_add hz hz) (le_of_eq e16)) ?_)
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

/-- The error at the numbers nuG zO hO is that at the second member's numbers, and the two summands
on sessions. -/
theorem zeta_nuG (zO hO : ℝ≥0∞) (t n : ℕ) :
    zetaW W2 S2 p2 at2 cn2 (nuG zO hO) t n =
      zetaW W2 S2 p2 at2 cn2 nu2 t n + (n : ℝ≥0∞) * zO + (n : ℝ≥0∞) * hO := by
  unfold zetaW
  show Prob.pOver (at2.M + 1) 2 n + (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * zO) +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * hO) + ((1 + 2 : ℕ) : ℝ≥0∞) * 0 + _ =
    Prob.pOver (at2.M + 1) 2 n + (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * 0) +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * 0) + ((1 + 2 : ℕ) : ℝ≥0∞) * 0 + _ +
      (n : ℝ≥0∞) * zO + (n : ℝ≥0∞) * hO
  ring

theorem zeta01G (say : Option Bool → Bool → Bool) (stp : Option Bool → Bool) :
    zetaW W2 S2 p2 (atG say stp) cn2 nu2 0 1 ≤ 62 / 4294967296 := by
  rw [zeta_atG]
  exact zeta01

theorem zeta_nuG' (say : Option Bool → Bool → Bool) (stp : Option Bool → Bool) (zO hO : ℝ≥0∞)
    (t n : ℕ) :
    zetaW W2 S2 p2 (atG say stp) cn2 (nuG zO hO) t n =
      zetaW W2 S2 p2 (atG say stp) cn2 nu2 t n + (n : ℝ≥0∞) * zO + (n : ℝ≥0∞) * hO := by
  rw [zeta_atG, zeta_atG]
  exact zeta_nuG zO hO t n

theorem ok2_some (b : Bool) : ok2 (some b) := fun h => by cases h

/-! ## The sessions' simulation error cannot be struck -/

theorem premW_teller (Ryes : Option Bool → Unit → Prop) :
    PremW W2 S2 cA2 p2 (atG sayTell stpRange) sm2 ok2 (fun _ => True) Ryes cn2 (nuG 1 0) :=
  premW_atG sayTell stpRange (fun _ => simB) Ryes 1 0 (fun _ _ _ _ _ _ _ => pr_le_one _ _)
    fun _ i _ _ _ hi _ =>
      le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ (h : i.isNone = true) => by
        cases i with
        | none => exact hi rfl
        | some b => cases h)

/-- The theorem on index privacy, called at the teller. -/
theorem privacy_teller (r₀ : pad2.Rec) (i₀ : Option Bool)
    (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) :
    ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1
      (simWholeKey W2 S2 cA2 r₀ (atG sayTell stpRange).side sm2 i₀ (nuG 1 0).s1 (fun _ => True)
        Unit)
      (zetaW W2 S2 p2 (atG sayTell stpRange) cn2 (nuG 1 0)) ok2 :=
  wholeKeyPrivacy _ _ _ _ _ _ _ _ _ _ r₀ _ _ _ _ _ (fun i x => ∃ w, R.yes i x w) _ _ R i₀
    (fun _ _ w h => ⟨w, h⟩) (premW_teller _)

/-- At the error with n · zO struck, index privacy fails for every simulator. -/
theorem struck_teller (r₀ : pad2.Rec) (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit)
    (hy : R.yes (some true) () ()) (hy' : R.yes (some false) () ())
    (Sim : ZKCP.Gen.Simulator (typedOracleFamily 32 W2.K C2) Unit (FullKey 32 pad2 aT aL) Unit (RequestProof 32 pad2)) :
    ¬ ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1 Sim
      (zetaW W2 S2 p2 (atG sayTell stpRange) cn2 nu2) ok2 := fun H =>
  no_privacy_small (zeta01G sayTell stpRange)
    (teller_not_private r₀ R hy hy' Sim (zetaW W2 S2 p2 (atG sayTell stpRange) cn2 nu2) ok2
      (ok2_some true) (ok2_some false) H)

/-- **THE SUMMAND n · zO CANNOT BE STRUCK.** -/
theorem parts_bite (r₀ : pad2.Rec) (i₀ : Option Bool)
    (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) (hy : R.yes (some true) () ())
    (hy' : R.yes (some false) () ()) :
    PremW W2 S2 cA2 p2 (atG sayTell stpRange) sm2 ok2 (fun _ => True)
        (fun i x => ∃ w, R.yes i x w) cn2 (nuG 1 0) ∧
      ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1
        (simWholeKey W2 S2 cA2 r₀ (atG sayTell stpRange).side sm2 i₀ (nuG 1 0).s1 (fun _ => True)
          Unit)
        (zetaW W2 S2 p2 (atG sayTell stpRange) cn2 (nuG 1 0)) ok2 ∧
      (∀ t n, zetaW W2 S2 p2 (atG sayTell stpRange) cn2 (nuG 1 0) t n =
        zetaW W2 S2 p2 (atG sayTell stpRange) cn2 nu2 t n + (n : ℝ≥0∞) * 1 + (n : ℝ≥0∞) * 0) ∧
      ∀ Sim, ¬ ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1 Sim
        (zetaW W2 S2 p2 (atG sayTell stpRange) cn2 nu2) ok2 :=
  ⟨premW_teller _, privacy_teller r₀ i₀ R, zeta_nuG' sayTell stpRange 1 0,
    struck_teller r₀ R hy hy'⟩

/-! ## The sessions' stops cannot be struck -/

/-- Where it does not stop, the honest side that sends a coin is simulated exactly. -/
theorem exactG (stp : Option Bool → Bool) {Y : Type} (w : WB) (hw : stp w.1 = false) (y : Y)
    (ρ : Rho (sessP Y).shape) :
    (sideG sayCoin stp Y).output w y ρ =
      simB y ρ ((sessP Y).extAns y ρ ((sideG sayCoin stp Y).ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ (sideG sayCoin stp Y).withheld w y := fun hh =>
    ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) fun (h0 : stp w.1 = true) => by
      rw [hw] at h0
      cases h0
  rw [if_neg hm]
  show _ = (unif Bool).map fun κ => some (viewB
    (((((sessP Y).extAns y ρ fun _ => xor (bit w.1) w.2.1.1) 0).getD false, κ), 0) (echoOf ρ) _)
  rw [extAnsB]
  refine congrArg (fun f => PMF.map f (unif Bool)) (funext fun κ => congrArg some ?_)
  obtain ⟨c, c', ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
  show (⟨_, _, _⟩ : DView (sessP Y)) = ⟨_, _, _⟩
  congr 1
  funext p
  exact (no_oposB p).elim

theorem premW_stopper (Ryes : Option Bool → Unit → Prop) :
    PremW W2 S2 cA2 p2 (atG sayCoin stpBut0) sm2 ok2 (fun _ => True) Ryes cn2 (nuG 0 1) :=
  premW_atG sayCoin stpBut0 (fun _ => simB) Ryes 0 1
    (fun n i r e x _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun ρ _ h => by
      cases hq : stpBut0 i with
      | true => exact h.1 hq
      | false => exact h.2 (exactG stpBut0 (i, r, e, n) hq _ _)))
    fun _ _ _ _ _ _ _ => pr_le_one _ _

/-- The theorem on index privacy, called at the stopper. -/
theorem privacy_stopper (r₀ : pad2.Rec) (i₀ : Option Bool)
    (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) :
    ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayCoin stpBut0).side) 1
      (simWholeKey W2 S2 cA2 r₀ (atG sayCoin stpBut0).side sm2 i₀ (nuG 0 1).s1 (fun _ => True) Unit)
      (zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 (nuG 0 1)) ok2 :=
  wholeKeyPrivacy _ _ _ _ _ _ _ _ _ _ r₀ _ _ _ _ _ (fun i x => ∃ w, R.yes i x w) _ _ R i₀
    (fun _ _ w h => ⟨w, h⟩) (premW_stopper _)

/-- At the error with n · hO struck, index privacy fails for every simulator. -/
theorem struck_stopper (r₀ : pad2.Rec) (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit)
    (hy : R.yes (some false) () ()) (hy' : R.yes (some true) () ())
    (Sim : ZKCP.Gen.Simulator (typedOracleFamily 32 W2.K C2) Unit (FullKey 32 pad2 aT aL) Unit (RequestProof 32 pad2)) :
    ¬ ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayCoin stpBut0).side) 1 Sim
      (zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 nu2) ok2 := fun H =>
  no_privacy_small (zeta01G sayCoin stpBut0)
    (stopper_not_private r₀ R hy hy' Sim (zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 nu2) ok2
      (ok2_some false) (ok2_some true) H)

/-- **THE SUMMAND n · hO CANNOT BE STRUCK.** -/
theorem stops_bite (r₀ : pad2.Rec) (i₀ : Option Bool)
    (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) (hy : R.yes (some false) () ())
    (hy' : R.yes (some true) () ()) :
    PremW W2 S2 cA2 p2 (atG sayCoin stpBut0) sm2 ok2 (fun _ => True)
        (fun i x => ∃ w, R.yes i x w) cn2 (nuG 0 1) ∧
      ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayCoin stpBut0).side) 1
        (simWholeKey W2 S2 cA2 r₀ (atG sayCoin stpBut0).side sm2 i₀ (nuG 0 1).s1 (fun _ => True)
          Unit)
        (zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 (nuG 0 1)) ok2 ∧
      (∀ t n, zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 (nuG 0 1) t n =
        zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 nu2 t n + (n : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * 1) ∧
      ∀ Sim, ¬ ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayCoin stpBut0).side) 1 Sim
        (zetaW W2 S2 p2 (atG sayCoin stpBut0) cn2 nu2) ok2 :=
  ⟨premW_stopper _, privacy_stopper r₀ i₀ R, zeta_nuG' sayCoin stpBut0 0 1,
    struck_stopper r₀ R hy hy'⟩

/-! ## A simulator that guesses: "below 1" is too low a bar, and n · zO is nearly tight -/

/-- The simulator of a session that lays a bit of the verifier's randomness in the run value's
place: its guess of the index's bit. -/
def simGuess {Y : Type} : Compile.Lifetime.SimOf (sessP Y) :=
  fun _ ρ ans =>
    PMF.pure (some (viewB (((ans (0 : Fin 1)).getD false, echoOf ρ), 0) (echoOf ρ) ans))

def smGuess : Sims pad2 := ⟨simT, simL, fun _ => simGuess⟩

/-- Where the guess is right, the teller's output is the simulator's. -/
theorem tell_eq_guess {Y : Type} (w : WB) (hw : stpRange w.1 = false) (y : Y)
    (ρ : Rho (sessP Y).shape) (hg : echoOf ρ = bit w.1) :
    (sideG sayTell stpRange Y).output w y ρ =
      simGuess y ρ ((sessP Y).extAns y ρ ((sideG sayTell stpRange Y).ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ (sideG sayTell stpRange Y).withheld w y := fun hh =>
    ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) fun (h0 : stpRange w.1 = true) => by
      rw [hw] at h0
      cases h0
  rw [if_neg hm]
  have key : ∀ κ : Bool, some ((sessP Y).dview y ((sideG sayTell stpRange Y).ext w)
      (((sideG sayTell stpRange Y).strat w y κ).run ρ).1) =
      some (viewB
        (((((sessP Y).extAns y ρ fun _ => xor (bit w.1) w.2.1.1) 0).getD false, echoOf ρ), 0)
        (echoOf ρ) ((sessP Y).extAns y ρ fun _ => xor (bit w.1) w.2.1.1)) := by
    intro κ
    refine congrArg some ?_
    rw [extAnsB]
    obtain ⟨c, c', ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
    have hg' : c 0 1 = bit w.1 := hg
    show (⟨_, _, _⟩ : DView (sessP Y)) = ⟨_, _, _⟩
    congr 1
    · show ((((xor (bit w.1) w.2.1.1, bit w.1), 0), (c 0 1, ())) :
          ((Bool × Bool) × ℕ) × (Bool × Unit)) =
        (((xor (bit w.1) w.2.1.1, c 0 1), 0), (c 0 1, ()))
      rw [hg']
    · funext p
      exact (no_oposB p).elim
  exact (congrArg (fun f => PMF.map f (unif Bool)) (funext key)).trans (PMF.map_const _ _)

/-- Setting the test bit to 0 does not touch the bit that is sent back. -/
theorem echo_zero (ρ : Rho pad2.onlineBatch.loc.shape) :
    echoOf (RoundsQueryLayout.zero pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh ρ) = echoOf ρ := by
  obtain ⟨c, c', ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
  show (Function.update c 0 (Function.update (c 0) 0 false)) 0 1 = c 0 1
  rw [Function.update_self, Function.update_of_ne (by decide)]

/-- turn over the bit that is sent back -/
def flipEcho (ρ : Rho pad2.onlineBatch.loc.shape) : Rho pad2.onlineBatch.loc.shape :=
  ((Function.update (show Blk₂ × Unit × Unit from ρ).1 0
      (Function.update ((show Blk₂ × Unit × Unit from ρ).1 0) 1
        (!(show Blk₂ × Unit × Unit from ρ).1 0 1)),
    (show Blk₂ × Unit × Unit from ρ).2) : Blk₂ × Unit × Unit)

theorem flipEcho_flipEcho : Function.Involutive flipEcho := by
  intro ρ
  obtain ⟨c, ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
  show ((Function.update (Function.update c 0 (Function.update (c 0) 1 (!c 0 1))) 0
      (Function.update ((Function.update c 0 (Function.update (c 0) 1 (!c 0 1))) 0) 1
        (!(Function.update c 0 (Function.update (c 0) 1 (!c 0 1))) 0 1)), ρ') :
      Blk₂ × Unit × Unit) = (c, ρ')
  rw [Function.update_self, Function.update_self, Function.update_idem, Function.update_idem,
    Bool.not_not, Function.update_eq_self, Function.update_eq_self]
  rfl

theorem echo_flipEcho (ρ : Rho pad2.onlineBatch.loc.shape) : echoOf (flipEcho ρ) = !echoOf ρ := by
  obtain ⟨c, ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
  show (Function.update c 0 (Function.update (c 0) 1 (!c 0 1))) 0 1 = !c 0 1
  rw [Function.update_self, Function.update_self]

/-- The bit that is sent back is a fair coin. -/
theorem half_echo (b : Bool) :
    pr (unif (Rho pad2.onlineBatch.loc.shape)) {ρ | echoOf ρ ≠ b} = 2⁻¹ := by
  have e1 : pr (unif (Rho pad2.onlineBatch.loc.shape)) {ρ | echoOf ρ ≠ b} =
      pr (unif (Rho pad2.onlineBatch.loc.shape)) {ρ | echoOf ρ ≠ b}ᶜ := by
    conv_lhs => rw [← map_unif_equiv flipEcho_flipEcho.toPerm, pr_map]
    refine congrArg (pr _) (Set.ext fun ρ => ?_)
    show echoOf (flipEcho ρ) ≠ b ↔ ¬ echoOf ρ ≠ b
    rw [echo_flipEcho]
    cases echoOf ρ <;> cases b <;> decide
  have e2 := pr_add_compl (unif (Rho pad2.onlineBatch.loc.shape)) {ρ | echoOf ρ ≠ b}
  rw [← e1, ← mul_two] at e2
  exact ENNReal.eq_inv_of_mul_eq_one_left e2

/-- **PremW at the teller, with the simulator that guesses: zO = 1/2.** -/
theorem premW_guess (Ryes : Option Bool → Unit → Prop) :
    PremW W2 S2 cA2 p2 (atG sayTell stpRange) smGuess ok2 (fun _ => True) Ryes cn2 (nuG 2⁻¹ 0) :=
  premW_atG sayTell stpRange (fun _ => simGuess) Ryes 2⁻¹ 0
    (fun n i r e x hi _ => by
      refine (pr_mono _ fun ρ h => ?_).trans (le_of_eq (half_echo (bit i)))
      show echoOf ρ ≠ bit i
      intro hg
      have hs : stpRange i = false := by
        cases i with
        | none => exact absurd rfl hi
        | some b => rfl
      exact h.2 (tell_eq_guess (i, r, e, n) hs _ _ ((echo_zero ρ).trans hg)))
    fun _ i _ _ _ hi _ =>
      le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ (h : i.isNone = true) => by
        cases i with
        | none => exact hi rfl
        | some b => cases h)

/-- The error at these numbers, at no query and one request: at most 1/2 + 62 / 2^32. -/
theorem zeta_guess_le :
    zetaW W2 S2 p2 (atG sayTell stpRange) cn2 (nuG 2⁻¹ 0) 0 1 ≤
      62 / 4294967296 + 2147483648 / 4294967296 := by
  have e2 : (2⁻¹ : ℝ≥0∞) = 2147483648 / 4294967296 := by
    rw [← one_div, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [zeta_nuG', Nat.cast_one, one_mul, one_mul, add_zero, e2]
  exact add_le_add (zeta01G sayTell stpRange) le_rfl

/-- **"BELOW 1" IS TOO LOW A BAR, AND THE SUMMAND n · zO IS NEARLY TIGHT.** The scheme whose prover
tells the index meets all premises with a simulator that guesses, at zO = 1/2. So it has index
privacy at an error that is below 1 at no query and one request. That error is at most
1/2 + 62 / 2^32, and no error at which this scheme has index privacy, with whatever simulator, is
below 15/32 there. -/
theorem guess_member (r₀ : pad2.Rec) (i₀ : Option Bool)
    (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) (hy : R.yes (some true) () ())
    (hy' : R.yes (some false) () ()) :
    PremW W2 S2 cA2 p2 (atG sayTell stpRange) smGuess ok2 (fun _ => True)
        (fun i x => ∃ w, R.yes i x w) cn2 (nuG 2⁻¹ 0) ∧
      ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1
        (simWholeKey W2 S2 cA2 r₀ (atG sayTell stpRange).side smGuess i₀ (nuG 2⁻¹ 0).s1
          (fun _ => True) Unit)
        (zetaW W2 S2 p2 (atG sayTell stpRange) cn2 (nuG 2⁻¹ 0)) ok2 ∧
      zetaW W2 S2 p2 (atG sayTell stpRange) cn2 (nuG 2⁻¹ 0) 0 1 < 1 ∧
      ∀ Sim ζ, ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1 Sim ζ
        ok2 → 1 ≤ ζ 0 1 + ζ 0 1 + 16⁻¹ := by
  refine ⟨premW_guess _,
    wholeKeyPrivacy _ _ _ _ _ _ _ _ _ _ r₀ _ _ _ _ _ (fun i x => ∃ w, R.yes i x w) _ _ R i₀
      (fun _ _ w h => ⟨w, h⟩) (premW_guess _), ?_,
    fun Sim ζ H => teller_not_private r₀ R hy hy' Sim ζ ok2 (ok2_some true) (ok2_some false) H⟩
  refine lt_of_le_of_lt zeta_guess_le ?_
  rw [ENNReal.div_add_div_same]
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

end OnBytes.WholeKey.FoeScheme

#print axioms OnBytes.WholeKey.FoeScheme.guess_member
#print axioms OnBytes.WholeKey.FoeScheme.parts_bite
#print axioms OnBytes.WholeKey.FoeScheme.stops_bite
