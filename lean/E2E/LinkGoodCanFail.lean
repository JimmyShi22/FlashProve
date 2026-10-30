-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LinkGoodCanFail.lean: what the premise on the link's simulator asks at error 0, and a condition
under which no simulator meets it.

Summary. Among the premises of index privacy (`PremW`, Johnson/WholeKey/Premises.lean) the field
`good` has a clause on the link: it compares the link prover's output with the simulator's. A
statement is worth something only if it can fail. This file spells out what the clause says at error
0 and derives a condition on a link prover under which the clause, and so `PremW`, fails for every
choice of simulators. Everything is for arbitrary parameters: any interactive protocols L, any three
provers, any simulators. The main limit: no prover is built here, and no prover and no pair of
private inputs that meet the condition are exhibited.

Main results.
  `link_output_of_good`: at error 0 the clause says: for every verifier message with the
    proof-of-work test bits 0 that is not in the prover's set `Hid`, the prover's output is the
    simulator's value for the two OOD samples, that verifier message, and the symbols that the
    verifier reads there.
  `link_outputs_agree`: so for two private inputs with the same two OOD samples and the same symbols
    read, the two outputs are the same.
  `no_good_of_two`, `no_premW_of_two`: the condition of failure: if a link prover has two such
    private inputs with different outputs, then `good` holds for it at error 0 with no simulators;
    so `PremW` holds for no parameters with that prover and the link's error 0. Its premise, that
    there are two such private inputs, is not proved here.

Terms: E2E/HidingTerms.lean.

Limits.
- The premise that there are two private inputs with the same two OOD samples and the same symbols
  read is proved nowhere in this file. (They may share the index: the statement does not ask for two
  indices.) This part is about L only, not about a prover; that the two outputs differ is the part
  about the prover. Where L has no such pair, no prover meets this condition.
- The two outputs can differ though no message does. An output holds the symbols read in the
  prover's own external strings (`Hs.Lk.ext`), while the premise on the symbols read is about the
  encodings (`L.encodeIndex`): a prover of fixed messages whose external strings are not the encodings can
  meet this condition. `PremW`'s field `ext` excludes that; it is no premise here.
- `good` is not the only field of `PremW` that reads the link's strategy: `runVals` reads its plain
  messages.
- Error 0 only. The outputs are distributions over the prover's coins: two provers that differ at
  every coin can have the same distribution.
- It is about the interactive link protocol. Nothing on the hashed scheme, and nothing on the
  statement that `PremW` is a premise of.

Helper lemma.
  `none_of_pr_le_zero`: under the uniform distribution on a finite type, an event of probability at
    most 0 has no member.


-/
import Johnson.WholeKey.Premises

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.CanFail
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

theorem none_of_pr_le_zero {C : Type} [Fintype C] [Nonempty C] (P : C → Prop)
    (h : pr (unif C) {c | P c} ≤ 0) : ∀ c, ¬ P c := by
  classical
  intro c hc
  have h1 := (pr_unif_le_iff P 0).1 h
  rw [zero_mul, nonpos_iff_eq_zero, Nat.cast_eq_zero, cnt_eq_card_filter,
    Finset.card_eq_zero] at h1
  exact Finset.notMem_empty c (h1 ▸ Finset.mem_filter.2 ⟨Finset.mem_univ c, hc⟩)

variable {I X : Type} {lam : ℕ}
variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
variable {Sm : Sims L} {Hs : ThreeProvers L} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {ok : I → Prop}
  {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {zT zO : ℝ≥0∞}

/-- At error 0: the output is the simulator's value, for every verifier message with the test bits 0
outside `Hid`. -/
theorem link_output_of_good (hG : Sm.Good Hs W ok Gs Ryes zT 0 zO) (i : I) (r : L.EncodingRandomness) (e : L.OutOfDomainSeed)
    (r' : L.EncodingRandomness) (e' : L.OutOfDomainSeed) (hi : ok i) (he : Gs e) (he' : Gs e') (ρ : Rho L.link.shape)
    (hH : (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ∉
      Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')) :
    Hs.Lk.output (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) =
      Sm.Lk (L.recOf i r e, L.recOf i r' e') (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ)
        (L.link.extAns (L.recOf i r e, L.recOf i r' e')
          (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex i r, L.encodeIndex i r')) := by
  by_contra hne
  exact none_of_pr_le_zero _ (hG.Lk i r e r' e' hi he he') ρ ⟨hH, hne⟩

/-- **The same OOD samples, the same symbols read: the same output.** -/
theorem link_outputs_agree (hG : Sm.Good Hs W ok Gs Ryes zT 0 zO) (i j : I) (r r' s s' : L.EncodingRandomness)
    (e e' f f' : L.OutOfDomainSeed) (hi : ok i) (hj : ok j) (he : Gs e) (he' : Gs e') (hf : Gs f)
    (hf' : Gs f') (ρ : Rho L.link.shape)
    (hx : (L.recOf i r e, L.recOf i r' e') = (L.recOf j s f, L.recOf j s' f'))
    (ha : L.link.extAns (L.recOf i r e, L.recOf i r' e')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex i r, L.encodeIndex i r') =
      L.link.extAns (L.recOf j s f, L.recOf j s' f')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex j s, L.encodeIndex j s'))
    (hH : (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ∉
      Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e'))
    (hH' : (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ∉
      Hs.Lk.Hid (j, (s, f), (s', f')) (L.recOf j s f, L.recOf j s' f')) :
    Hs.Lk.output (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) =
      Hs.Lk.output (j, (s, f), (s', f')) (L.recOf j s f, L.recOf j s' f')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) := by
  have key : ∀ (x x' : L.Rec × L.Rec) (A A' : (twoExternalStrings L.wordLength L.Symbol).Pos → Option (twoExternalStrings L.wordLength L.Symbol).Sym),
      x = x' → A = A' →
      Sm.Lk x (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) A =
        Sm.Lk x' (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) A' :=
    fun _ _ _ _ h1 h2 => by rw [h1, h2]
  exact ((link_output_of_good hG i r e r' e' hi he he' ρ hH).trans (key _ _ _ _ hx ha)).trans
    (link_output_of_good hG j s f s' f' hj hf hf' ρ hH').symm

/-- **The condition of failure**: two such private inputs with different outputs: `good` holds with
no simulators at the link's error 0. -/
theorem no_good_of_two (i j : I) (r r' s s' : L.EncodingRandomness) (e e' f f' : L.OutOfDomainSeed) (hi : ok i) (hj : ok j)
    (he : Gs e) (he' : Gs e') (hf : Gs f) (hf' : Gs f') (ρ : Rho L.link.shape)
    (hx : (L.recOf i r e, L.recOf i r' e') = (L.recOf j s f, L.recOf j s' f'))
    (ha : L.link.extAns (L.recOf i r e, L.recOf i r' e')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex i r, L.encodeIndex i r') =
      L.link.extAns (L.recOf j s f, L.recOf j s' f')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex j s, L.encodeIndex j s'))
    (hH : (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ∉
      Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e'))
    (hH' : (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ∉
      Hs.Lk.Hid (j, (s, f), (s', f')) (L.recOf j s f, L.recOf j s' f'))
    (hne : Hs.Lk.output (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ≠
      Hs.Lk.output (j, (s, f), (s', f')) (L.recOf j s f, L.recOf j s' f')
        (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ)) :
    ∀ (Sm' : Sims L) (zT' zO' : ℝ≥0∞), ¬ Sm'.Good Hs W ok Gs Ryes zT' 0 zO' :=
  fun _ _ _ hG =>
    hne (link_outputs_agree hG i j r r' s s' e e' f f' hi hj he he' hf hf' ρ hx ha hH hH')

/-- So `PremW` holds for no parameters whose three provers are these and whose link's error is 0. -/
theorem no_premW_of_two {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params}
    {a : AtRecs lam L Bd aT aL} {c : CoinNums Bd} {N : NumsW}
    (hno : ∀ (Sm' : Sims L) (zT' zO' : ℝ≥0∞), ¬ Sm'.Good a.Hs W ok Gs Ryes zT' 0 zO')
    (hz : N.zL = 0) (Sm' : Sims L) : ¬ PremW W S cA p a Sm' ok Gs Ryes c N :=
  fun hP => hno Sm' N.zT N.zO (hz ▸ hP.good)

end AtPublicFiles.CanFail

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.CanFail.none_of_pr_le_zero
#print axioms AtPublicFiles.CanFail.link_output_of_good
#print axioms AtPublicFiles.CanFail.link_outputs_agree
#print axioms AtPublicFiles.CanFail.no_good_of_two
#print axioms AtPublicFiles.CanFail.no_premW_of_two
