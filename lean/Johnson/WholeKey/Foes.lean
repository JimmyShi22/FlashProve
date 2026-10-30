-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Foes.lean: TESTS THAT CAN FAIL, for the statement of index privacy of the scheme
with the whole key published (Johnson/WholeKey/Statement.lean): schemes and letters that leak, at
which the property or a premise must FAIL.

General theorems with their proofs. This file states no goal of the release.

Why. A statement of index privacy that every scheme met would say nothing. Each test below shows
that the property (ZKCP.Gen.PrivacyOn, ZKCP/OnRange.lean), or a premise of the statement, refuses
something that it ought to refuse. "Fails" is always meant so: on every range of indices that holds
the two indices, whatever the simulator, the error is at least 1/2 at the named numbers of queries
and requests.

THE KIT.
  AllOut P c              (the library's, Compile/GenPub.lean) every run of the program c, whatever
                          the oracles answer and the coins show, yields a value with the property P.
  not_private_of_event    for ANY scheme: two indices OF THE RANGE with the same public parameters,
                          one environment that is valid at both, one adversary, and an event on
                          views that has probability 1 at the one index and 0 at the other: then
                          1 ≤ ζ t N + ζ t N.
THE TESTS.
  (1) told_not_private    A COMMITTER THAT TELLS THE INDEX IN THE KEY. PROVED. At an object whose
        out-of-domain answers tell two indices apart (the statement: Spec.told_not_private,
        Johnson/WholeKey/Idle.lean) the scheme argW fails index privacy at 0 queries and 0 requests,
        for all wires, all letters of the honest side, all relations. The premise that shuts such
        an object out: the encoding hides together with the answers (ReadsG.hidE): see (6).
  (2) said_not_private    A PROVER THAT TELLS THE INDEX IN A PROOF, UNDER ANY KEY. PROVED, for ANY
        scheme, so for argW at any letters: if a test on proofs says yes to every proof that the
        prover can make for one instance at the index i, and no at the index i', index privacy fails
        at 0 queries and ONE request. It shows that the sessions stand in the view, not the key
        alone. The premise that shuts such a prover out: the session's simulators are good for the
        honest sides (Sims.Good): a simulator is handed nothing by which it could tell i from i'.
        ITS LIMIT: it asks a SURE tell, at EVERY proof that the prover can make. AT argW IT IS IDLE
        wherever a session can hand "none" (a search that runs out; a stop): "none" tells nothing,
        so no test says yes to every proof. A test at argW's own prover with numbers:
        Johnson/WholeKey/FoeScheme.lean.
  (3) saltsLaw_not_const  A CONSTANT ENUMERATION OF SALTS. PROVED: it fails the law on a table's
        salts (SaltsLaw, Johnson/WholeKey/CoinLaws.lean) wherever there is a leaf and a free bit.
        NOT SHOWN: that with constant salts and constant encoding randomness the PROPERTY fails as
        well (an adversary rebuilds the first table's tree for one index and compares the roots).
  (4) leaky_typed_not_private   THE LIBRARY's SCHEME WITH A TRAPDOOR INSTANCE (ZKCP/Separation.lean:
        it hands out the index at the instance that equals the hash of the empty string). PROVED: in
        the typed form, at one request a proof, it fails at 1 query and 1 request. So the property
        in which the statement is typed IS the strong form, in which the environment sees the
        adversary's queries.
  (5) silent_good         SILENT HONEST SIDES MEET THE PREMISES ON PROVERS AT ERROR 0. PROVED.
        Honest sides that send fixed messages and never stop meet ExtEnc, StopsSmall at 0 and, with
        a simulator that sends the same fixed messages, Sims.Good at 0. INDEX PRIVACY ALONE IS
        CHEAP. What they are MEANT to fail is completeness at a small error; that they do fail it
        is shown nowhere in this file.

  (6) readsG_not_told     THE PREMISE ON READS REFUSES AN ANSWER THAT TELLS. PROVED, for every
        object: if at one seed of Gs a test on answers says yes to every honest answer of the index
        i and no to every honest answer of i', the premise ReadsG (a clause of PremW) fails.
Tests (1), (2), (4) are tests of the PROPERTY: they do not look at PremW or zetaW. Tests (3) and (6)
are tests of single PREMISES; they name neither PremW nor zetaW. SO NOTHING IN THIS FILE WOULD FAIL
IF A TERM OF zetaW WERE TAKEN OUT; tests that hold PremW and zetaW: Johnson/WholeKey/FoeZeta.lean.
That PremW is not empty and zetaW not trivial: Johnson/WholeKey/Member.lean. In
Johnson/WholeKey/Foes2.lean: an honest side that lays the index in a plain part forces
1/2 ≤ z + h; one that stops at one index alone forces 1 ≤ h.

Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Statement
import Johnson.WholeKey.Idle
import ZKCP.Separation
import ZKCP.SpecialAny
import Compile.GenPub

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Compile.GenPub (AllOut allOut_true)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The kit -/

section Kit
variable {S : OSpec} {α β : Type}

theorem prCoins_outs (f : Fam S) {P : α → Prop} {c : OComp S α} :
    AllOut P c → Rom.PrCoins f c {a | P a} = 1 := by
  induction c with
  | pure a =>
    intro h
    show pr (PMF.pure a) {a | P a} = 1
    rw [Prob.pr_pure, if_pos]
    exact h
  | query o q k ih => intro h; exact ih (f o q) (h (f o q))
  | sample n k ih =>
    intro h
    show pr ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).runEager f) {a | P a} = 1
    rw [Prob.pr_bind]
    have e : ∀ r, pr ((k r).runEager f) {a | P a} = 1 := fun r => ih r (h r)
    rw [Prob.expect_congr _ e, Prob.expect_const]

theorem prCoins_outs_not (f : Fam S) {P : α → Prop} {c : OComp S α} :
    AllOut (fun a => ¬ P a) c → Rom.PrCoins f c {a | P a} = 0 := by
  induction c with
  | pure a =>
    intro h
    show pr (PMF.pure a) {a | P a} = 0
    rw [Prob.pr_pure, if_neg]
    exact h
  | query o q k ih => intro h; exact ih (f o q) (h (f o q))
  | sample n k ih =>
    intro h
    show pr ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).runEager f) {a | P a} = 0
    rw [Prob.pr_bind]
    have e : ∀ r, pr ((k r).runEager f) {a | P a} = 0 := fun r => ih r (h r)
    rw [Prob.expect_congr _ e, Prob.expect_const]

theorem Pr_outs {P : α → Prop} {c : OComp S α} (h : AllOut P c) :
    Rom.Pr c (fun _ => {a | P a}) = 1 := by
  have e : ∀ f, Rom.PrCoins f c {a | P a} = 1 := fun f => prCoins_outs f h
  simp only [Rom.Pr, e, MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

theorem Pr_outs_not {P : α → Prop} {c : OComp S α} (h : AllOut (fun a => ¬ P a) c) :
    Rom.Pr c (fun _ => {a | P a}) = 0 := by
  have e : ∀ f, Rom.PrCoins f c {a | P a} = 0 := fun f => prCoins_outs_not f h
  simp only [Rom.Pr, e, MeasureTheory.lintegral_const, zero_mul]

variable {I X Wn PP IVK ISK Pf : Type}

/-- **For any scheme**: an event on views that is sure at one index and impossible at another, under
one environment and one adversary, at equal public parameters, shuts out index privacy with an error
below 1/2. -/
theorem not_private_of_event (R : ZKCP.Gen.RelPair I X Wn PP)
    (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ) (Sim : ZKCP.Gen.Simulator S PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (H : ZKCP.Gen.PrivacyOn R A B Sim ζ ok) (i i' : I)
    (hi : ok i) (hi' : ok i')
    (hpp : R.pp i = R.pp i') (Z : ZKCP.Gen.ViewEnv S IVK X Wn Pf) (hZ : Z.IsValid R B i)
    (hZ' : Z.IsValid R B i') (t N : ℕ) (Vt : IVK → ZKCP.Gen.AdvVerifier S X Pf)
    (hb : ∀ ivk, (Vt ivk).QueryBound t) (T : Set (ZKCP.Gen.View S IVK X Pf))
    (h1 : Rom.Pr (ZKCP.Gen.realExp A Vt Z i N) (fun _ => T) = 1)
    (h0 : Rom.Pr (ZKCP.Gen.realExp A Vt Z i' N) (fun _ => T) = 0) : 1 ≤ ζ t N + ζ t N := by
  have a := (Prob.sd_le_iff.1 (H i hi Z hZ t Vt N hb).1 T).1
  have b := (Prob.sd_le_iff.1 (H i' hi' Z hZ' t Vt N hb).1 T).2
  have e : ZKCP.Gen.idealExp R Sim Vt Z i N = ZKCP.Gen.idealExp R Sim Vt Z i' N := by
    unfold ZKCP.Gen.idealExp
    rw [hpp]
  rw [h1] at a
  rw [h0, zero_add, ← e] at b
  exact a.trans (add_le_add b le_rfl)

/-- **(2) A prover that tells the index in a proof**, for any scheme: a test ψ on proofs that says
yes to every proof for the instance x at the index i, and no at the index i'. -/
theorem said_not_private (R : ZKCP.Gen.RelPair I X Wn PP) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf)
    (B : ℕ) (hB : 1 ≤ B) (Sim : ZKCP.Gen.Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (ok : I → Prop) (H : ZKCP.Gen.PrivacyOn R A B Sim ζ ok) (i i' : I) (hi : ok i) (hi' : ok i')
    (hpp : R.pp i = R.pp i') (x : X)
    (w : Wn) (hy : R.yes i x w) (hy' : R.yes i' x w) (ψ : Pf → Bool)
    (h1 : AllOut (fun key => AllOut (fun πs => ∀ π ∈ πs.val, ψ π = true) (A.P key.2 [(x, w)]))
      (A.C i))
    (h0 : AllOut (fun key => AllOut (fun πs => ∀ π ∈ πs.val, ψ π = false) (A.P key.2 [(x, w)]))
      (A.C i')) : 1 ≤ ζ 0 1 + ζ 0 1 := by
  have hv : ∀ j, R.yes j x w →
      ZKCP.Gen.ViewEnv.IsValid R B (fun _ => some [(x, w, true)] :
        ZKCP.Gen.ViewEnv S IVK X Wn Pf) j := by
    intro j hj v b hbv
    cases hbv
    refine ⟨hB, ?_⟩
    intro xw hxw
    simp only [ZKCP.Gen.Batch.pairs, List.map_cons, List.map_nil, List.mem_singleton] at hxw
    subst hxw
    exact hj
  have hrel : ∀ πs : ZKCP.Gen.Slots Pf [(x, w)], ∃ π, πs.val = [π] ∧
      ZKCP.Gen.Batch.released [(x, w, true)] πs.val = [(x, π)] := by
    intro πs
    obtain ⟨π, hπ⟩ := List.length_eq_one_iff.1 πs.property
    exact ⟨π, hπ, by rw [hπ]; rfl⟩
  refine not_private_of_event R A B Sim ζ ok H i i' hi hi' hpp (fun _ => some [(x, w, true)])
    (hv i hy)
    (hv i' hy') 0 1 (fun _ => .request fun _ => .halt) (fun _ _ => trivial)
    {v | ∃ s ∈ v.sessions, ∃ e ∈ s, ψ e.2 = true} ?_ ?_
  · refine Pr_outs
      (P := fun v : ZKCP.Gen.View S IVK X Pf => ∃ s ∈ v.sessions, ∃ e ∈ s, ψ e.2 = true) ?_
    show AllOut _ ((A.C i).bind fun key => (A.P key.2 [(x, w)]).bind fun πs =>
      OComp.pure { (⟨key.1, [], [], []⟩ : ZKCP.Gen.View S IVK X Pf) with
        sessions := [] ++ [ZKCP.Gen.Batch.released [(x, w, true)] πs.val] })
    refine AllOut.bind h1 fun key hk => AllOut.bind hk fun πs hπs => ?_
    obtain ⟨π, hπ, hr⟩ := hrel πs
    refine ⟨[(x, π)], ?_, (x, π), List.mem_singleton.2 rfl, hπs π (by rw [hπ]; simp)⟩
    show [(x, π)] ∈ [] ++ [ZKCP.Gen.Batch.released [(x, w, true)] πs.val]
    rw [hr]
    simp
  · refine Pr_outs_not
      (P := fun v : ZKCP.Gen.View S IVK X Pf => ∃ s ∈ v.sessions, ∃ e ∈ s, ψ e.2 = true) ?_
    show AllOut _ ((A.C i').bind fun key => (A.P key.2 [(x, w)]).bind fun πs =>
      OComp.pure { (⟨key.1, [], [], []⟩ : ZKCP.Gen.View S IVK X Pf) with
        sessions := [] ++ [ZKCP.Gen.Batch.released [(x, w, true)] πs.val] })
    refine AllOut.bind h0 fun key hk => AllOut.bind hk fun πs hπs => ?_
    obtain ⟨π, hπ, hr⟩ := hrel πs
    rintro ⟨s, hs, e, he, hψ⟩
    simp only [List.nil_append, List.mem_singleton] at hs
    subst hs
    rw [hr, List.mem_singleton] at he
    subst he
    rw [hπs π (by rw [hπ]; simp)] at hψ
    cases hψ

end Kit

/-! ## (1) A committer that tells the index in the key -/

theorem told_not_private : Spec.told_not_private := by
  intro I X lam L Bd aT aL W S cA r₀ p h Ryes Rno sub B Sim ζ φ ok i i' oi oi' hi hi' H
  have key : ∀ j, AllOut (fun v => ∃ r e, v.ivk.rcd = L.recOf j r e)
      (ZKCP.Gen.realExp (argW W S cA r₀ p h) (fun _ => .halt) (fun _ => none) j 0) := by
    intro j
    have hk : AllOut (fun k : FullKey lam L aT aL × Isk lam L Bd aT aL =>
        ∃ r e, k.1.rcd = L.recOf j r e) (commitW W S cA h j) := by
      unfold commitW commitAt
      refine AllOut.bind (allOut_true _) fun d _ => ?_
      refine AllOut.bind (allOut_true _) fun t₁ _ => ?_
      refine AllOut.bind (allOut_true _) fun ts _ => ?_
      refine AllOut.bind (allOut_true _) fun a _ => ?_
      refine AllOut.bind (allOut_true _) fun ls _ => ?_
      exact ⟨t₁.r, t₁.seed, rfl⟩
    exact AllOut.bind
      (Q := fun v : ZKCP.Gen.View (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (FullKey lam L aT aL) X
        (RequestProof lam L) => ∃ r e, v.ivk.rcd = L.recOf j r e)
      (g := fun k : FullKey lam L aT aL × Isk lam L Bd aT aL =>
        OComp.pure (⟨k.1, [], [], []⟩ : ZKCP.Gen.View (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
          (FullKey lam L aT aL) X (RequestProof lam L)))
      hk fun _ hk => hk
  refine not_private_of_event _ _ B Sim ζ ok H i i' oi oi' rfl (fun _ => none)
    (fun _ _ hb => by cases hb) (fun _ _ hb => by cases hb) 0 0 (fun _ => .halt)
    (fun _ => trivial) {v | φ v.ivk.rcd.2 = true} ?_ ?_
  · refine Pr_outs (P := fun v => φ v.ivk.rcd.2 = true) (AllOut.mono (key i) ?_)
    rintro v ⟨r, e, hv⟩
    show φ v.ivk.rcd.2 = true
    rw [hv]
    exact hi r e
  · refine Pr_outs_not (P := fun v => φ v.ivk.rcd.2 = true) (AllOut.mono (key i') ?_)
    rintro v ⟨r, e, hv⟩
    show ¬ φ v.ivk.rcd.2 = true
    rw [hv]
    show ¬ φ (L.honestOutOfDomainAnswer i' r e) = true
    rw [hi' r e]
    exact Bool.false_ne_true

/-! ## (3) Constant salts -/

/-- **A constant enumeration of salts fails the law on a table's salts**, wherever there is a leaf
and a free bit. -/
theorem saltsLaw_not_const (s : ℕ → Bits) (m ℓ : ℕ) (pre : Bits) (hm : 0 < m) (hℓ : 0 < ℓ) :
    ¬ SaltsLaw ⟨0, fun _ => s⟩ m pre ℓ := by
  intro h
  unfold SaltsLaw at h
  have hs : ∀ u : Fin m → Fin ℓ → Bool, (fun j => pre ++ List.ofFn (u j)) ∈
      ((unif (Fin m → Fin ℓ → Bool)).map fun u => fun j => pre ++ List.ofFn (u j)).support := by
    intro u
    rw [PMF.support_map]
    exact ⟨u, by simp [PMF.support_uniformOfFintype], rfl⟩
  rw [← h] at hs
  have hc : ∀ u : Fin m → Fin ℓ → Bool,
      (fun j : Fin m => pre ++ List.ofFn (u j)) = fun j : Fin m => s j.val := by
    intro u
    have := hs u
    rw [PMF.support_map] at this
    obtain ⟨_, _, e⟩ := this
    exact e.symm
  have e := (hc fun _ _ => true).trans (hc fun _ _ => false).symm
  have e0 := congrFun e ⟨0, hm⟩
  have e1 := List.ofFn_injective (List.append_cancel_left e0)
  have e2 := congrFun e1 ⟨0, hℓ⟩
  cases e2

/-! ## (6) The premise on reads refuses an answer that tells -/

/-- **An object whose honest answers at a seed of Gs tell two indices apart fails the premise on
reads and hiding.** -/
theorem readsG_not_told {I X : Type} (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (b qT qpar qch qon : ℕ)
    (h : Hiop.Seeded.ReadsG L Gs b qT qpar qch qon) (s : L.OutOfDomainSeed) (hs : Gs s) (φ : L.OutOfDomainAnswer → Bool)
    (i i' : I) (hi : ∀ r, φ (L.honestOutOfDomainAnswer i r s) = true) (hi' : ∀ r, φ (L.honestOutOfDomainAnswer i' r s) = false) :
    False := by
  have e := h.hidE ∅ (Nat.zero_le _) s hs i i'
  have e1 := congrArg (fun μ => pr μ {a | φ a.1 = true}) e
  simp only [Prob.pr_map] at e1
  have h1 : (fun r => (L.honestOutOfDomainAnswer i r s, fun p : (∅ : Finset (Fin L.wordLength)) => L.encodeIndex i r p)) ⁻¹'
      {a | φ a.1 = true} = Set.univ := by
    ext r
    simp [hi r]
  have h0 : (fun r => (L.honestOutOfDomainAnswer i' r s, fun p : (∅ : Finset (Fin L.wordLength)) => L.encodeIndex i' r p)) ⁻¹'
      {a | φ a.1 = true} = ∅ := by
    ext r
    simp [hi' r]
  rw [h1, h0, Prob.pr_univ, Prob.pr_empty] at e1
  exact one_ne_zero e1

/-! ## (4) The library's scheme with a trapdoor instance, in the typed form -/

/-- **The scheme with a trapdoor instance fails the property in which the statement is typed**, at
one request a proof: so that property is the strong form. -/
theorem leaky_typed_not_private (lam : ℕ)
    (Sim : ZKCP.Gen.Simulator (rom lam) Unit Unit (ZKCP.Digest lam) (Option Bool))
    (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : ZKCP.Gen.HasIndexPrivacyWith (ZKCP.Special.toPair (ZKCP.Separation.Rall lam))
      (ZKCP.Special.toGen (ZKCP.Separation.leaky lam)) 1 Sim ζ) : 1 ≤ ζ 1 1 + ζ 1 1 :=
  ZKCP.Separation.leaky_not_strong lam _ ζ
    (ZKCP.SpecialAny.strongPrivacy_of_gen (ZKCP.Separation.Rall lam)
      (ZKCP.SpecialAny.agrees_toGen (ZKCP.Separation.leaky lam)) Sim ζ h)

/-! ## (5) Silent honest sides -/

variable {I X : Type}

/-- Honest sides that send each round's fixed message, whatever they are handed, and never stop;
their external strings are the encoded indices. -/
def silent (L : HolographicProtocol I X) : ThreeProvers L where
  T :=
    { Coin := Unit
      ext := fun w => L.encodeIndex w.1 w.2.1
      strat := fun _ _ _ => Strat.dflt _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  Lk :=
    { Coin := Unit
      ext := fun w => (L.encodeIndex w.1 w.2.1.1, L.encodeIndex w.1 w.2.2.1)
      strat := fun _ _ _ => Strat.dflt _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  B :=
    { Coin := Unit
      ext := fun w => L.encodeIndex w.1 w.2.1
      strat := fun _ _ _ => Strat.dflt _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }

/-- The silent honest sides speak of the encodings. -/
theorem extEnc_silent (L : HolographicProtocol I X) : ExtEnc (silent L) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The silent honest sides meet the premises on provers at error 0: there are simulators that are
good for them with errors 0, and their stops have measure 0; for every object, all wires, all sets
of seeds, all relations. The statement; its proof: silent_good. -/
def Spec.silent_good : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (Gs : L.OutOfDomainSeed → Prop)
    (Ryes : I → X → Prop),
    (∃ Sm : Sims L, Sm.Good (silent L) W (fun _ => True) Gs Ryes 0 0 0) ∧
      StopsSmall (silent L) W (fun _ => True) Gs Ryes 0 0 0

open Classical in
/-- The simulator that shows the run of the fixed messages, with the symbols that it is handed. -/
def fixedSim {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) :
    Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q)) :=
  fun x ρ ans => PMF.pure (some ⟨((Strat.dflt Q.shape ()).run ρ).1.plains, ans, fun p =>
    if p ∈ Q.reads x ρ ((Strat.dflt Q.shape ()).run ρ).1.plains ∨ Q.blinded p = false then
      some (((Strat.dflt Q.shape ()).run ρ).1.read p)
    else none⟩)

/-- It is exact for every honest side that sends the fixed messages and never stops. -/
theorem output_fixed {Y Wt : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (H : Honest Q Wt)
    (hB : H.Bad = ∅) (hH : ∀ w y, H.Hid w y = ∅)
    (hs : ∀ w y c, H.strat w y c = Strat.dflt Q.shape ()) (w : Wt) (y : Y) (ρ : Rho Q.shape) :
    H.output w y ρ = fixedSim Q y ρ (Q.extAns y ρ (H.ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ H.withheld w y := by
    unfold Honest.withheld
    rw [hB, hH]
    simp
  have hc : (fun c : H.Coin => some (Q.dview y (H.ext w) ((H.strat w y c).run ρ).1)) =
      Function.const _ (some (Q.dview y (H.ext w) ((Strat.dflt Q.shape ()).run ρ).1)) := by
    funext c
    rw [hs]
    rfl
  rw [if_neg hm, hc, PMF.map_const]
  unfold fixedSim InteractiveOracleProof.dview
  rw [Strat.rho_run]

/-- **(5) Silent honest sides meet the premises on provers at error 0.** -/
theorem silent_good : Spec.silent_good := by
  intro I X lam L Bd aT aL W Gs Ryes
  refine ⟨⟨⟨fixedSim L.offline, fixedSim L.link, fun _ => fixedSim L.onlineBatch.loc⟩, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · exact fun i r e _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_fixed L.offline (silent L).T rfl (fun _ _ => rfl) (fun _ _ _ => rfl) _ _ _))
  · exact fun i r e r' e' _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_fixed L.link (silent L).Lk rfl (fun _ _ => rfl) (fun _ _ _ => rfl) _ _ _))
  · exact fun n i r e x _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_fixed L.onlineBatch.loc (sessionAt (silent L) n) rfl (fun _ _ => rfl)
        (fun _ _ _ => rfl) _ _ _))
  · exact fun _ _ _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)
  · exact fun _ _ _ _ _ _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)
  · exact fun _ _ _ _ _ _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.not_private_of_event
#print axioms OnBytes.WholeKey.said_not_private
#print axioms OnBytes.WholeKey.told_not_private
#print axioms OnBytes.WholeKey.saltsLaw_not_const
#print axioms OnBytes.WholeKey.leaky_typed_not_private
#print axioms OnBytes.WholeKey.extEnc_silent
#print axioms OnBytes.WholeKey.readsG_not_told
#print axioms OnBytes.WholeKey.silent_good
