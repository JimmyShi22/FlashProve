-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/FoeScheme.lean: TESTS THAT CAN FAIL, AT THE SCHEME: the scheme with the whole key
published (argW, Johnson/WholeKey/Defs.lean) with an honest side that leaks HAS INDEX PRIVACY AT NO
ERROR BELOW 15/32 (at no query and one request), whatever the simulator. (At an error of about 1/2
the first of the two schemes here, the teller, has it: guess_member, Johnson/WholeKey/FoeZeta.lean.)

Definitions, statements and proofs. Toys: nothing here is about the protocol of the release. This
file states no goal of the release.

Why. The tests of Johnson/WholeKey/Foes2.lean bound letters of a PREMISE from below. Here the bound
is on the PROPERTY of a scheme: whatever the simulator, an error ζ at which the scheme has index
privacy on a range that holds two named indices meets 1 ≤ ζ 0 1 + ζ 0 1 + 1/16: no query, one
request.

THE SCHEMES. The letters (atG say stp) are those of Johnson/WholeKey/Member2.lean, but for two
things. The session's honest side is sideG say stp: in the place of the run value it sends say i κ,
and it stops, at every verifier's randomness, where stp i. And the session's run value, as the
scheme's letters have it (rvB, pvB), is a constant, not what stands in that place.
  THE TELLER   say i κ := the index's bit; it stops out of range alone.
  THE STOPPER  say i κ := κ; it stops at every index but the bit 0.
Both convince the verifier wherever they do not stop: the verifier does not read that place.

HOW. One request, no query; the adversary looks at the proof.
  (a) If the proof holds a string, the string's plain parts are those of the honest side's own run
      but for nonces (chain_at, OnBytes/Prover/Chain.lean), and the honest side did not stop:
      inv_proveAt.
  (b) The verifier refuses a proof that holds no string (det_verify_none). At fixed coins it refuses
      with probability at most 1/16 where the honest side does not stop (fixed_law,
      Johnson/WholeKey/Complete.lean). So at such an index the proof holds a string but for 1/16
      (noString_le, for every honest side at these wires). AT THE SECOND MEMBER ITSELF:
      string_often_pad2: a theorem that a string is handed out at all.
  (c) A test on proofs that says yes to every string of the index i, and no to every proof of the
      index i', has probability at least 15/16 at i and 0 at i'. A simulator is handed the same at
      both. one_le_of_event: the count, for any scheme.

Main names (namespace OnBytes.WholeKey.FoeScheme).
  one_le_of_event   for ANY scheme: an event on views that fails with probability at most α at one
                    index and is impossible at another forces 1 ≤ ζ t N + ζ t N + α.
  sideG, recsG2, atG   the family of honest sides, and the scheme's letters at them.
  noString_le, string_often_pad2   one request: the proof holds no string with probability at most
                    the number of completeness; at the second member: at most 1/16.
  foe_of_test       the lower bound, for a test on proofs.
  teller_not_private, stopper_not_private   the two schemes.
  complete_atG      each scheme of the family is complete at 1/16 at the indices where it does not
                    stop.

Limits. Toys. One request and no query. The tell is sure: the test never errs at a string. 15/16 is
what completeness gives; the true share of proofs that hold a string is not computed. The bound is
on ζ at (0, 1) alone.
The proofs of the premises of completeness follow Johnson/WholeKey/Member2Complete.lean closely; the
way through the coins follows complete_argW (Johnson/WholeKey/Complete.lean); the environment, the
adversary and the event follow said_not_private (Johnson/WholeKey/Foes.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Member2Complete
import Johnson.WholeKey.Small
import ZKCP.OnRange

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

/-! ## The count, for any scheme -/

section Any
variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

theorem one_le_of_event (R : ZKCP.Gen.RelPair I X Wn PP) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf)
    (B : ℕ) (Sim : ZKCP.Gen.Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop)
    (H : ZKCP.Gen.PrivacyOn R A B Sim ζ ok) (i i' : I) (hi : ok i) (hi' : ok i')
    (hpp : R.pp i = R.pp i') (Z : ZKCP.Gen.ViewEnv S IVK X Wn Pf) (hZ : Z.IsValid R B i)
    (hZ' : Z.IsValid R B i') (t N : ℕ) (Vt : IVK → ZKCP.Gen.AdvVerifier S X Pf)
    (hb : ∀ ivk, (Vt ivk).QueryBound t) (T : Set (ZKCP.Gen.View S IVK X Pf)) {α : ℝ≥0∞}
    (h1 : Rom.Pr (ZKCP.Gen.realExp A Vt Z i N) (fun _ => Tᶜ) ≤ α)
    (h0 : Rom.Pr (ZKCP.Gen.realExp A Vt Z i' N) (fun _ => T) = 0) :
    1 ≤ ζ t N + ζ t N + α := by
  have a : Rom.Pr (ZKCP.Gen.realExp A Vt Z i N) (fun _ => T) ≤
      pr (ZKCP.Gen.idealExp R Sim Vt Z i N) T + ζ t N :=
    (Prob.sd_le_iff.1 (H i hi Z hZ t Vt N hb).1 T).1
  have b : pr (ZKCP.Gen.idealExp R Sim Vt Z i' N) T ≤
      Rom.Pr (ZKCP.Gen.realExp A Vt Z i' N) (fun _ => T) + ζ t N :=
    (Prob.sd_le_iff.1 (H i' hi' Z hZ' t Vt N hb).1 T).2
  have e : ZKCP.Gen.idealExp R Sim Vt Z i N = ZKCP.Gen.idealExp R Sim Vt Z i' N := by
    unfold ZKCP.Gen.idealExp
    rw [hpp]
  rw [h0, zero_add, ← e] at b
  have s : Rom.Pr (ZKCP.Gen.realExp A Vt Z i N) (fun _ => T) +
      Rom.Pr (ZKCP.Gen.realExp A Vt Z i N) (fun _ => Tᶜ) = 1 := by
    rw [Rom.Pr_eq_law, Rom.Pr_eq_law]
    exact Prob.pr_add_compl _ T
  calc (1 : ℝ≥0∞) = _ := s.symm
    _ ≤ (pr (ZKCP.Gen.idealExp R Sim Vt Z i N) T + ζ t N) + α := add_le_add a h1
    _ ≤ (ζ t N + ζ t N) + α := add_le_add (add_le_add b le_rfl) le_rfl

end Any

/-! ## The family of honest sides -/

variable (say : Option Bool → Bool → Bool) (stp : Option Bool → Bool)

/-- The session's honest side of pad2, but that it sends say i κ in the run value's place and stops
where stp i. -/
def sideG (Y : Type) : Honest (sessP Y) WB where
  Coin := Bool
  ext := fun w _ => xor (bit w.1) w.2.1.1
  strat := fun w _ κ =>
    ((((), ((xor (bit w.1) w.2.1.1, say w.1 κ), 0)), fun c => (((), c 0 1), fun _ => ())) :
      (Unit × ((Bool × Bool) × ℕ)) × (Blk₂ → (Unit × Bool) × (Unit → Unit)))
  Bad := ∅
  Hid := fun w _ => {_ρ | stp w.1 = true}

def recsG2 : ThreeProvers pad2 := ⟨sideT _, sideL _, sideG say stp _⟩

/-- The scheme's letters: those of Johnson/WholeKey/Member2.lean at these honest sides; the
session's run value is a constant. -/
def atG : AtRecs 32 pad2 Bool aT aL where
  Hs := recsG2 say stp
  dc := ⟨fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _⟩
  b₀ := false
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 3
  M := 1
  nm := id
  RV := Bool
  okV := fun _ => True
  rvT := fun κ => κ
  rvL := fun κ => κ
  rvB := fun _ => false
  startT := fun v _ _ _ => [v]
  startL := fun v _ _ _ => [v]
  startB := fun v _ _ _ => [v]
  pvT := fun pl => (show Bool × Unit from pl).1
  pvL := fun pl => (show (Bool × Bool) × Unit from pl).1.2
  pvB := fun _ => false
  rtail := fun _ => []
  nR := 2
  nK := 1
  nJ := 1
  fill := List.replicate 32 false
  ri := pick (Bool × Bool)
  sl := saltsPre [false] (2 ^ 0) 32 (pick _)
  kT := pick Bool
  kL := pick Bool
  kB := pick Bool
  coT := co2
  coL := co2
  coB := co2

/-! ## The premises of completeness -/

/-- The true instances: the first table's and the link's honest sides stop out of range; the
session's where stp. -/
def YesG : Option Bool → Unit → Prop := fun i _ => i ≠ none ∧ stp i = false

def badsG (i : Option Bool) : Bads pad2 :=
  ⟨∅, ∅, fun _ => {_ρ | i = none}, fun _ _ => {_ρ | i = none}, fun _ => {_ρ | stp i = true}⟩

theorem sideFitG : SideFit W2 p2 (atG say stp).side where
  sl := fun a j hj => by
    have hj' : j < 2 ^ 0 := hj
    show (if j < 2 ^ 0 then (if h : j < 2 ^ 0 then [false] ++ List.ofFn _ else []) else []).length
      = 33
    rw [if_pos hj', dif_pos hj', List.length_append, List.length_ofFn]
    rfl
  coT := fun a _ => fit_co2 _ a
  coL := fun a _ => fit_co2 _ a
  coB := fun a _ => fit_co2 _ a

/-- What round 1's plain part holds in a transcript that is the honest run but for nonces. -/
theorem plain_of_puts (i : Option Bool) (r : Bool × Bool) (e : Bool) (x : Unit) (n : ℕ) (κ : Bool)
    (τ : Tr pad2.onlineBatch.loc.shape)
    (hp : Puts pad2.onlineBatch.loc.shape pad2.onlineBatch.ann (wBC W2).sh
      (((recsG2 say stp).B.strat (i, r, e, n) (x, pad2.recOf i r e) κ).run τ.rho).1 τ) :
    (plB1 τ).1 = (xor (bit i) r.1, say i κ) ∧ plB2 τ = chB1 τ 0 1 := by
  refine ⟨?_, ?_⟩
  · rcases hp.2.2.1 with h | ⟨g, m, _, hg, h⟩ | ⟨g, m, hk, _⟩
    · exact congrArg Prod.fst h
    · have e' : gr = g := Option.some.inj hg
      rw [← e'] at h
      exact congrArg Prod.fst h
    · cases hk
  · rcases hp.2.2.2.2.2.1 with h | ⟨g, m, hk, _⟩ | ⟨g, m, _, hg, _⟩
    · exact h
    · cases hk
    · cases hg

theorem accLawG (i : Option Bool) (r : Bool × Bool) (e : Bool) (x : Unit) (n : ℕ) (κ : Bool)
    (B : Set (Rho pad2.onlineBatch.loc.shape)) :
    AccLaw pad2.onlineBatch (wBC W2) (x, pad2.recOf i r e) (pad2.encodeIndex i r)
      ((recsG2 say stp).B.strat (i, r, e, n) (x, pad2.recOf i r e) κ) B := fun τ _ hp _ => by
  show (((plB1 τ).1.1 == xor (bit i) r.1) && (plB2 τ == chB1 τ 0 1)) = true
  obtain ⟨h1, h2⟩ := plain_of_puts say stp i r e x n κ τ hp
  rw [h1, h2, beq_self_eq_true, beq_self_eq_true]
  rfl

theorem accLawsG :
    AccLaws W2 S2 (atG say stp).side.st.joint (YesG stp) (fun i _ _ _ => badsG stp i) 0 0 0 0
      0 where
  acc := fun i r₁ x d _ =>
    ⟨fun e₁ _ => accLawT i r₁ e₁ d.κ.1 _, fun e₁ e₂ _ _ => accLawL i r₁ e₁ d.r e₂ d.κ.2.1 _,
      fun e₂ _ => accLawG say stp i d.r e₂ x d.n d.κ.2.2 _, fun _ _ _ => rfl⟩
  small := fun _ _ _ _ hY =>
    ⟨le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
      le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h),
      fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hY.1 h),
      fun _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hY.1 h),
      fun _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ (h : stp _ = true) => by
        rw [hY.2] at h
        cases h)⟩

theorem stopsInG : StopsIn (lam := 32) (Bd := Bool) (aT := aT) (aL := aL) (atG say stp).side.st
    (fun i _ _ _ => badsG stp i) where
  T := fun i r₁ _ _ e ρ hs =>
    ((Set.mem_union ρ _ _).1
      (@of_decide_eq_true _ ((atG say stp).dc.T (i, r₁, e) (pad2.recOf i r₁ e) ρ) hs)).elim
      (fun h => h.elim) fun h => h
  Lk := fun i r₁ _ d e e' ρ hs =>
    ((Set.mem_union ρ _ _).1
      (@of_decide_eq_true _ ((atG say stp).dc.Lk (i, (r₁, e), (d.r, e'))
        (pad2.recOf i r₁ e, pad2.recOf i d.r e') ρ) hs)).elim
      (fun h => h.elim) fun h => h
  B := fun i _ x d e ρ hs =>
    ((Set.mem_union ρ _ _).1
      (@of_decide_eq_true _ ((atG say stp).dc.B (i, d.r, e, d.n) (x, pad2.recOf i d.r e) ρ)
        hs)).elim
      (fun h => h.elim) fun h => h

/-- Each scheme of the family is complete at 1/16 at the indices where no honest side stops. -/
theorem complete_atG (r₀ : pad2.Rec) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation (YesG stp)))
      (argW W2 S2 cA2 r₀ p2 (atG say stp).side) 1 16⁻¹ := by
  rw [← alpha2]
  exact complete_argW W2 S2 cA2 r₀ p2 (atG say stp).side (YesG stp) (fun i _ _ _ => badsG stp i)
    lawFit2 wiresFit2 (sideFitG say stp) (accLawsG say stp) (stopsInG say stp)

/-! ## What a proof holds -/

/-- what stands in the run value's place of a session's string -/
def slotOf (s : OneProtocolProof 32 pad2.onlineBatch) : Bool :=
  (show ((Bool × Bool) × ℕ) × (Bool × Unit) from s.plains).1.1.2

/-- If the proof holds a string: the honest side did not stop, and the string holds say i κ. -/
def Inv (i : Option Bool) (π : RequestProof 32 pad2) : Prop :=
  ∀ s, π.piB = some s → stp i = false ∧ ∃ κ, slotOf s = say i κ

variable (r₀ : pad2.Rec) (g : Fam (typedOracleFamily 32 W2.K C2))

theorem inv_proveAt (isk : Isk 32 pad2 Bool aT aL) (d : DrawP 32 pad2 Bool aT aL Bool)
    (hd : DrawPOf (atG say stp).side d) :
    Inv say stp isk.i ((proveAt W2 cA2 r₀ (atG say stp).side isk () d).det g) := by
  intro s hs
  obtain ⟨_, a₃, k₃, hco, _⟩ := hd
  cases ht : isk.copies[d.j]? with
  | none =>
    have e : (proveAt W2 cA2 r₀ (atG say stp).side isk () d).det g =
        ⟨d.j, (atG say stp).side.nm d.j, none⟩ := by
      unfold proveAt
      rw [ht]
      rfl
    rw [e] at hs
    cases hs
  | some t =>
    rw [det_proveAt W2 cA2 r₀ (atG say stp).side g isk () d t ht] at hs
    have hs' : shown ((atG say stp).side.st.stopB isk.i t.r t.seed () ((atG say stp).side.nm d.j))
        ((proveBA W2 cA2 r₀ (fun _ => t.tree)
          ((atG say stp).side.dressB ((atG say stp).side.rvB d.κ) d.co) (atG say stp).side.capB
          t.tree.root () (pad2.recOf isk.i t.r t.seed) (pad2.encodeIndex isk.i t.r)
          ((atG say stp).side.st.B isk.i t.r t.seed () ((atG say stp).side.nm d.j) d.κ)).det g) =
        some s := hs
    cases hr : (proveBA W2 cA2 r₀ (fun _ => t.tree)
          ((atG say stp).side.dressB ((atG say stp).side.rvB d.κ) d.co) (atG say stp).side.capB
          t.tree.root () (pad2.recOf isk.i t.r t.seed) (pad2.encodeIndex isk.i t.r)
          ((atG say stp).side.st.B isk.i t.r t.seed () ((atG say stp).side.nm d.j) d.κ)).det g with
    | noFormat => rw [hr] at hs'; cases hs'
    | ranOut j => rw [hr] at hs'; cases hs'
    | ok a =>
      obtain ⟨π, τ⟩ := a
      rw [hr] at hs'
      have hs2 : (if (atG say stp).side.st.stopB isk.i t.r t.seed () ((atG say stp).side.nm d.j)
          τ.rho then none else some π) = some s := hs'
      cases hst : (atG say stp).side.st.stopB isk.i t.r t.seed () ((atG say stp).side.nm d.j)
          τ.rho with
      | true => rw [hst] at hs2; cases hs2
      | false =>
        rw [hst] at hs2
        have hπ : π = s := Option.some.inj hs2
        subst hπ
        refine ⟨?_, d.κ, ?_⟩
        · cases hq : stp isk.i with
          | false => rfl
          | true =>
            exfalso
            have hm : τ.rho ∈ (recsG2 say stp).B.withheld (isk.i, t.r, t.seed, id d.j)
                ((), pad2.recOf isk.i t.r t.seed) := Or.inr hq
            have hdec := @decide_eq_true _ ((atG say stp).dc.B (isk.i, t.r, t.seed, id d.j)
              ((), pad2.recOf isk.i t.r t.seed) τ.rho) hm
            have hst' : @decide _ ((atG say stp).dc.B (isk.i, t.r, t.seed, id d.j)
              ((), pad2.recOf isk.i t.r t.seed) τ.rho) = false := hst
            rw [hdec] at hst'
            cases hst'
        · obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff Tag.onl pad2.onlineBatch (wBC W2) W2.embB id
            (xinBA r₀) _ _ _ _ _ _ _ g π τ).1 hr
          have hfit :
              ((atG say stp).side.dressB ((atG say stp).side.rvB d.κ) d.co).Fit 33 32 0 := by
            rw [hco]
            exact fit_co2 _ a₃
          obtain ⟨R, hc⟩ := chain_at g 33 Tag.onl _ _ _ _ hfit.leaf pad2.onlineBatch.loc.shape pad2.onlineBatch.ann
            (wBC W2).sh W2.embB id 0 .first _ z hz fmt2.2.2 wiresFit2.fewB.1 wiresFit2.fewB.2
            (z.2.2.2.getD fun _ => false) (fun r hr => by rw [hr]; rfl)
          have hp := hc.puts
          rw [← rho_trK pad2.onlineBatch.loc.shape z.2.1 z.1] at hp
          exact congrArg Prod.snd
            (plain_of_puts say stp isk.i t.r t.seed () (id d.j) d.κ _ hp).1

/-- The verifier refuses a proof that holds no string. -/
theorem det_verify_none (k : FullKey 32 pad2 aT aL) (π : RequestProof 32 pad2) (h : π.piB = none) :
    (verifyW W2 S2 cA2 r₀ p2 k () π).det g = false := by
  rw [verifyW_eq_VCA]
  obtain ⟨leaf, copy, piB⟩ := π
  obtain rfl : piB = none := h
  obtain ⟨cm, rcd, piT, links⟩ := k
  unfold verifyAtFullKey
  cases piT <;> rcases links[leaf]? with _ | ⟨cmj, recj, _ | πL⟩ <;> rfl

/-! ## The experiment: one request, no query -/

/-- The types of the scheme's views. -/
abbrev Vw : Type := ZKCP.Gen.View (typedOracleFamily 32 W2.K C2) (FullKey 32 pad2 aT aL) Unit (RequestProof 32 pad2)

/-- The environment: a batch of the one instance, the adversary's own. -/
def envOne : ZKCP.Gen.ViewEnv (typedOracleFamily 32 W2.K C2) (FullKey 32 pad2 aT aL) Unit Unit (RequestProof 32 pad2) :=
  fun _ => some [((), (), true)]

/-- The adversary: one request, then it halts. -/
def advOne : FullKey 32 pad2 aT aL → ZKCP.Gen.AdvVerifier (typedOracleFamily 32 W2.K C2) Unit (RequestProof 32 pad2) :=
  fun _ => .request fun _ => .halt

/-- The view after that request. -/
def viewOf (k : FullKey 32 pad2 aT aL) (π : RequestProof 32 pad2) : Vw := ⟨k, [[((), π)]], [], []⟩

theorem valid_envOne (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) (j : Option Bool)
    (hj : R.yes j () ()) : ZKCP.Gen.ViewEnv.IsValid R 1 envOne j := by
  intro v b hbv
  cases hbv
  exact ⟨le_rfl, fun _ _ => hj⟩

omit g in
/-- A bound at all coins that can be drawn is a bound on the real experiment: for every honest
side. -/
theorem real_le (h : HonestSide 32 pad2 Bool aT aL) (i : Option Bool) (T : Set Vw) {ε : ℝ≥0∞}
    (hpt : ∀ c, DrawCOf h c → ∀ dP, DrawPOf h dP →
      PrFrom (Table.empty _) ((commitAt W2 S2 cA2 h i c).bind fun key =>
        (proveAt W2 cA2 r₀ h key.2 () dP).bind fun π => OComp.pure (viewOf key.1 π)) T ≤ ε) :
    Rom.Pr (ZKCP.Gen.realExp (argW W2 S2 cA2 r₀ p2 h) advOne envOne i 1) (fun _ => T) ≤ ε := by
  show PrFrom (Table.empty _) (((coinsC W2 h).bind fun d => commitAt W2 S2 cA2 h i d).bind
    fun key => ((coinsP W2 h).bind fun d => (proveAt W2 cA2 r₀ h key.2 () d).bind fun π =>
        (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof 32 pad2) [((), ())]))).bind fun πs =>
      OComp.pure { (⟨key.1, [], [], []⟩ : Vw) with
        sessions := [] ++ [ZKCP.Gen.Batch.released [((), (), true)] πs.val] }) T ≤ ε
  simp only [OComp.bind_assoc]
  refine PrFrom_coins_le _ _ _ (fun c hc => ?_) _ (onlyCoins_coinsC W2 h)
  refine PrFrom_bind_coins_le _ (commitAt W2 S2 cA2 h i c) _ _ (fun dP hdP => ?_) _
    (onlyCoins_coinsP W2 h)
  exact hpt c hc dP hdP

/-- The event: the one proof that was shown passes the test ψ. -/
def passes (ψ : RequestProof 32 pad2 → Bool) : Set Vw := {v | ∃ s ∈ v.sessions, ∃ e ∈ s, ψ e.2 = true}

theorem mem_passes (ψ : RequestProof 32 pad2 → Bool) (k : FullKey 32 pad2 aT aL) (π : RequestProof 32 pad2) :
    viewOf k π ∈ passes ψ ↔ ψ π = true := by
  constructor
  · rintro ⟨s, hs, e, he, hψ⟩
    have hs' : s = [((), π)] := List.mem_singleton.1 hs
    subst hs'
    have he' : e = ((), π) := List.mem_singleton.1 he
    subst he'
    exact hψ
  · intro h
    exact ⟨[((), π)], List.mem_singleton.2 rfl, ((), π), List.mem_singleton.2 rfl, h⟩

/-- the test: does the proof hold a string? -/
def someTest (π : RequestProof 32 pad2) : Bool := π.piB.isSome

omit g in
/-- **One request: the proof holds no string with probability at most the number of completeness**,
for every honest side at these wires that meets the premises of completeness. -/
theorem noString_le (h : HonestSide 32 pad2 Bool aT aL) (Yes : Option Bool → Unit → Prop)
    (Bs : Option Bool → pad2.EncodingRandomness → Unit → Draw 32 pad2 Bool aT aL (h.KT × h.KL × h.KB) → Bads pad2)
    {ζ₁ ζ₂ δT δL δB : ℝ≥0∞} (hL : LawFit W2 S2 h.capT h.capL h.capB) (hF : SideFit W2 p2 h)
    (acc : AccLaws W2 S2 h.st.joint Yes Bs ζ₁ ζ₂ δT δL δB) (hS : StopsIn h.st Bs)
    (i : Option Bool) (hY : Yes i ()) :
    Rom.Pr (ZKCP.Gen.realExp (argW W2 S2 cA2 r₀ p2 h) advOne envOne i 1)
      (fun _ => (passes someTest)ᶜ) ≤ alphaAll W2 h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB := by
  refine real_le r₀ h i _ fun c hc dP hdP => ?_
  refine (PrFrom_le_of_det (E' := {b | b = false}) ?_ ?_ _ fun g hg => ?_).trans
    (fixed_law W2 S2 cA2 r₀ p2 h Yes Bs hL wiresFit2 hF acc hS i () hY c hc dP hdP)
  · exact (noCoin_commitAt W2 S2 cA2 _ i c).bind fun key =>
      (noCoin_proveAt W2 cA2 r₀ _ key.2 () dP).bind fun _ => trivial
  · exact (noCoin_commitAt W2 S2 cA2 _ i c).bind fun key =>
      (noCoin_proveAt W2 cA2 r₀ _ key.2 () dP).bind fun π => noCoin_VRA W2 S2 cA2 r₀ p2 _ _ _
  · have hg' : OComp.det g _ ∈ (passes someTest)ᶜ := hg
    simp only [OComp.det_bind] at hg'
    show OComp.det g _ = false
    simp only [OComp.det_bind]
    refine det_verify_none r₀ g _ _ ?_
    cases hπ : ((proveAt W2 cA2 r₀ h ((commitAt W2 S2 cA2 h i c).det g).2 () dP).det g).piB with
    | none => rfl
    | some s =>
      refine absurd ((mem_passes someTest _ _).2 ?_) hg'
      unfold someTest
      rw [hπ]
      rfl

omit g in
/-- **AT THE SECOND MEMBER ITSELF a string is handed out**: at an index in range, the proof of one
request holds a string but for probability 1/16. -/
theorem string_often_pad2 (i : Option Bool) (hi : i ≠ none) :
    Rom.Pr (ZKCP.Gen.realExp (argW W2 S2 cA2 r₀ p2 at2.side) advOne envOne i 1)
      (fun _ => (passes someTest)ᶜ) ≤ 16⁻¹ :=
  (noString_le r₀ at2.side Yes2 (fun i _ _ _ => bads2 i) lawFit2 sideFit2 accLaws2 stopsIn2 i
    hi).trans (le_of_eq alpha2)

/-- What the committer keeps holds the index. -/
theorem isk_i (i : Option Bool) (c : DrawC 32 pad2 Bool aT aL Bool Bool) :
    ((commitAt W2 S2 cA2 (atG say stp).side i c).det g).2.i = i := by
  rw [det_commitAt]

omit g in
/-- **THE LOWER BOUND, for a test on proofs.** At the index i no honest side stops, and ψ says yes
to every string that the prover can hand out there; at the index i' it says no to every proof. Then,
WHATEVER THE SIMULATOR, index privacy on a range that holds both forces 1 ≤ ζ 0 1 + ζ 0 1 + 1/16. -/
theorem foe_of_test (ψ : RequestProof 32 pad2 → Bool) (i i' : Option Bool) (hi : i ≠ none)
    (hs : stp i = false) (ha : ∀ π, Inv say stp i π → ψ π = false → π.piB = none)
    (hb : ∀ π, Inv say stp i' π → ψ π = false)
    (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit) (hy : R.yes i () ()) (hy' : R.yes i' () ())
    (Sim : ZKCP.Gen.Simulator (typedOracleFamily 32 W2.K C2) Unit (FullKey 32 pad2 aT aL) Unit (RequestProof 32 pad2))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : Option Bool → Prop) (hok : ok i) (hok' : ok i')
    (H : ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG say stp).side) 1 Sim ζ ok) :
    1 ≤ ζ 0 1 + ζ 0 1 + 16⁻¹ := by
  refine one_le_of_event R _ 1 Sim ζ ok H i i' hok hok' (Subsingleton.elim _ _) envOne
    (valid_envOne R i hy) (valid_envOne R i' hy') 0 1 advOne (fun _ _ => trivial) (passes ψ) ?_ ?_
  · refine real_le r₀ (atG say stp).side i _ fun c hc dP hdP => ?_
    refine (PrFrom_le_of_det (E' := {b | b = false}) ?_ ?_ _ fun g hg => ?_).trans
      ((fixed_law W2 S2 cA2 r₀ p2 (atG say stp).side (YesG stp) (fun i _ _ _ => badsG stp i)
        lawFit2 wiresFit2 (sideFitG say stp) (accLawsG say stp) (stopsInG say stp) i () ⟨hi, hs⟩ c
        hc dP hdP).trans (le_of_eq alpha2))
    · exact (noCoin_commitAt W2 S2 cA2 _ i c).bind fun key =>
        (noCoin_proveAt W2 cA2 r₀ _ key.2 () dP).bind fun _ => trivial
    · exact (noCoin_commitAt W2 S2 cA2 _ i c).bind fun key =>
        (noCoin_proveAt W2 cA2 r₀ _ key.2 () dP).bind fun π => noCoin_VRA W2 S2 cA2 r₀ p2 _ _ _
    · have hg' : OComp.det g _ ∈ (passes ψ)ᶜ := hg
      simp only [OComp.det_bind] at hg'
      show OComp.det g _ = false
      simp only [OComp.det_bind]
      refine det_verify_none r₀ g _ _ (ha _ ?_ ?_)
      · have h := inv_proveAt say stp r₀ g
          ((commitAt W2 S2 cA2 (atG say stp).side i c).det g).2 dP hdP
        rw [isk_i] at h
        exact h
      · cases hψ : ψ ((proveAt W2 cA2 r₀ (atG say stp).side
            ((commitAt W2 S2 cA2 (atG say stp).side i c).det g).2 () dP).det g) with
        | false => rfl
        | true => exact absurd ((mem_passes ψ _ _).2 hψ) hg'
  · refine le_antisymm (real_le r₀ (atG say stp).side i' _ fun c hc dP hdP => ?_) (zero_le _)
    refine (PrFrom_le_of_det (c' := OComp.pure ()) (E' := ∅) ?_ trivial _ fun g hg => ?_).trans
      (le_of_eq (PrFrom_pure _ () ∅ fun h => h))
    · exact (noCoin_commitAt W2 S2 cA2 _ i' c).bind fun key =>
        (noCoin_proveAt W2 cA2 r₀ _ key.2 () dP).bind fun _ => trivial
    · exfalso
      have hg' : OComp.det g _ ∈ passes ψ := hg
      simp only [OComp.det_bind] at hg'
      have h := inv_proveAt say stp r₀ g
        ((commitAt W2 S2 cA2 (atG say stp).side i' c).det g).2 dP hdP
      rw [isk_i] at h
      have h1 := (mem_passes ψ _ _).1 hg'
      rw [hb _ h] at h1
      cases h1

end OnBytes.WholeKey.FoeScheme

namespace OnBytes.WholeKey.FoeScheme
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WholeKey.Member2
open Hiop.Seeded.Two
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The two schemes -/

/-- The teller: the index's bit in the run value's place; it stops out of range alone. -/
def sayTell : Option Bool → Bool → Bool := fun i _ => bit i
def stpRange : Option Bool → Bool := fun i => i.isNone

/-- The stopper: a coin in the run value's place; it stops at every index but the bit 0. -/
def sayCoin : Option Bool → Bool → Bool := fun _ κ => κ
def stpBut0 : Option Bool → Bool := fun i => !(i == some false)

/-- the test for the teller: the bit in the run value's place; "no" if there is no string -/
def tellTest (π : RequestProof 32 pad2) : Bool := (π.piB.map slotOf).getD false

/-- **THE SCHEME WHOSE PROVER TELLS THE INDEX HAS INDEX PRIVACY AT NO ERROR BELOW 15/32** at no
query and one request: for every simulator, on every range that holds the two bits. -/
theorem teller_not_private (r₀ : pad2.Rec) (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit)
    (hy : R.yes (some true) () ()) (hy' : R.yes (some false) () ())
    (Sim : ZKCP.Gen.Simulator (typedOracleFamily 32 W2.K C2) Unit (FullKey 32 pad2 aT aL) Unit (RequestProof 32 pad2))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : Option Bool → Prop) (hok : ok (some true)) (hok' : ok (some false))
    (H : ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayTell stpRange).side) 1 Sim ζ ok) :
    1 ≤ ζ 0 1 + ζ 0 1 + 16⁻¹ := by
  refine foe_of_test sayTell stpRange r₀ tellTest (some true) (some false) (by simp) rfl
    (fun π hI hψ => ?_) (fun π hI => ?_) R hy hy' Sim ζ ok hok hok' H
  · cases hπ : π.piB with
    | none => rfl
    | some s =>
      obtain ⟨_, κ, hκ⟩ := hI s hπ
      have e : tellTest π = slotOf s := by
        unfold tellTest
        rw [hπ]
        rfl
      rw [e, hκ] at hψ
      cases hψ
  · cases hπ : π.piB with
    | none =>
      unfold tellTest
      rw [hπ]
      rfl
    | some s =>
      obtain ⟨_, κ, hκ⟩ := hI s hπ
      unfold tellTest
      rw [hπ]
      exact hκ

/-- **THE SCHEME WHOSE PROVER STOPS AT ONE INDEX OF TWO HAS INDEX PRIVACY AT NO ERROR BELOW 15/32**
at no query and one request: for every simulator, on every range that holds the two bits. -/
theorem stopper_not_private (r₀ : pad2.Rec) (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit)
    (hy : R.yes (some false) () ()) (hy' : R.yes (some true) () ())
    (Sim : ZKCP.Gen.Simulator (typedOracleFamily 32 W2.K C2) Unit (FullKey 32 pad2 aT aL) Unit (RequestProof 32 pad2))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : Option Bool → Prop) (hok : ok (some false)) (hok' : ok (some true))
    (H : ZKCP.Gen.PrivacyOn R (argW W2 S2 cA2 r₀ p2 (atG sayCoin stpBut0).side) 1 Sim ζ ok) :
    1 ≤ ζ 0 1 + ζ 0 1 + 16⁻¹ := by
  refine foe_of_test sayCoin stpBut0 r₀ someTest (some false) (some true) (by simp)
    rfl (fun π _ hψ => ?_) (fun π hI => ?_) R hy hy' Sim ζ ok hok hok' H
  · cases hπ : π.piB with
    | none => rfl
    | some s =>
      unfold someTest at hψ
      rw [hπ] at hψ
      cases hψ
  · cases hπ : π.piB with
    | none =>
      unfold someTest
      rw [hπ]
      rfl
    | some s => exact absurd (hI s hπ).1 (by decide)

end OnBytes.WholeKey.FoeScheme

#print axioms OnBytes.WholeKey.FoeScheme.noString_le
#print axioms OnBytes.WholeKey.FoeScheme.string_often_pad2
#print axioms OnBytes.WholeKey.FoeScheme.foe_of_test
#print axioms OnBytes.WholeKey.FoeScheme.teller_not_private
#print axioms OnBytes.WholeKey.FoeScheme.stopper_not_private
#print axioms OnBytes.WholeKey.FoeScheme.one_le_of_event
#print axioms OnBytes.WholeKey.FoeScheme.complete_atG
#print axioms OnBytes.WholeKey.FoeScheme.inv_proveAt
#print axioms OnBytes.WholeKey.FoeScheme.det_verify_none
