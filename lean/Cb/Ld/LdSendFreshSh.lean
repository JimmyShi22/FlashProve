-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFreshSh.lean: under the hypotheses of its statements, a sending run by the shared part
of a batch is fresh for the shared masks that it sends; a sending in every slot, for that slot's;
the shared run if the union of the slots' further positions is within the budget `N.budT t`, the
sending in every slot if each slot's are.

The honest side of a reduction that is run in a batch (`IOR.HonestV`, Ior/LinkV.lean) has a strategy
of a shared part, which takes the shared witness, and a strategy for a slot of the batch, which also
takes the explicit part of that slot's statement and its witness. This file treats two ways to run a
one-instance reduction in a batch: in every slot (`Honest.localV`), or once, by the shared part,
under shared verifier messages (`Honest.sharedV`).

Definitions, statements and proofs.
The notions: Ior/KnowCollRulesMask.lean (`Fresh`, for one instance), Cb/Ld/LdSendFresh.lean (under
the hypotheses of its statement, the sending of a family is Fresh for one instance, within the
budget `N.budT t`).

Why: the rule for masked links of a batch (Ior/LinkVMasked.lean) asks of the prefix that, given all
that it shows to a set of slots together, the coming link's masks are still uniform (exactly:
`FreshV`, Ior/LinkVMasked.lean). For an IOR in every slot this follows slot by slot
(Ior/LinkVMaskedRules.lean: `freshV_local`). For an IOR that the shared part runs alone every slot
recomputes its own result (`Honest.sharedV`, Ior/LinkV.lean). (Ior/LinkVMaskedRules.lean:
`freshV_shared` takes a slot of J as the instance that is looked at, asks that a slot's reading is
the shared part's, and takes the law for the empty set of slots as a hypothesis. The rule here takes
an instance of the shared part's own; a slot's further witness may differ from it.)

The idea: a virtual instance. The shared part runs the one-instance prover on an instance "v w0" of
its own (made from what it holds). All slots see that one run, each at its own further positions; so
all that the slots of J see is a function of what the virtual instance's run shows at the union of
their positions. If also
  the explicit part that a slot hands on, and what is read of the witness that it hands on, are
  functions (gx, gk) of what the virtual run hands on, the second one not moved by an overwriting of
  the masks,
  what is read of the shared witness handed on is a function (g0) of the same, and an overwriting of
  the masks goes through it,
then, under the hypotheses below, freshness for the one virtual instance, at the union, gives
freshness for every set of slots.

Main names, each under the hypotheses of its statement:
  `Spec.freshV_virt`: the rule, for any IOR. The masks are shared ones; the slots have none (Unit).
  `ldSendFamSh Sd D wS`: the shared part's strategy for a sending: the family's sender on the
    witness wS (what it holds); it ends with what it held, the samples, the words as sent, the pairs
    (message, randomness).
  `Spec.ldSendFam_freshSh`: the sending of a family, run by the shared part: fresh for own masks of
    a coming link that are coins of the sender, under the conditions of Cb/Ld/LdSendFresh.lean
    (`U.Laws`), `D.Nn.Hides (N.budT t)`, and: a slot's witness gives the same messages as wS
    ("apart"); the readings k0, kj factor as above.
  `Spec.ldSendFam_freshLoc`: the sending of a family in every slot: fresh for each slot's masks,
    jointly over the slots (from `freshV_local`).
  `Spec.ldSendFam_blindSh`, `Spec.ldSendFam_blindLoc`: a later sending does not look at masks sent
    before (`BlindV` of Ior/LinkVMaskedRules.lean), run by the shared part or in every slot, if what
    it lays into its messages does not read them and what it hands on is read as overwritten: so
    `FreshV` is carried through it (`freshV_seq`).
The budget of the shared run: the union of the slots' further positions is within the sender's
budget (as in Ior/LinkV.lean: `exactV_shared`).

Limits: "Together, at the union of the further positions" is the form stated here for batches; the
technical report has a form of its lemma on masks sent in advance for sets of instances; whether it
is the same is not held here.
Three conditions are to be kept in sight where these rules are used:
  before a masked block only the oracle message that holds its masks, and that message's sample
  answers, depend on them, on the pad or on the encoding randomness;
  mask coordinates are pairwise disjoint and none is a pad;
  no test on a group that holds the message comes before the masked block.
This file says nothing on slots that read the shared masks in their own witnesses: kj must not be
moved by them (choose kj so). It says nothing on soundness.
Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdSendFreshProofs
import Cb.Ld.LdSendBlind
import Ior.LinkVMaskedRulesLocal
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] {N : Sig E} {W W' Sh : Type}

/-- The shared part's strategy for a sending. -/
def ldSendFamSh
    (Sd : N.Seeds) (D : N.Sender W W') (wS : Sh → W) (s : Sh) (c : D.Mk × D.Nn.Rnd) :
    Strat (N.sh Sd) (Sh × (N.Smp × N.ext.Str × N.Wit)) :=
  ((D.Nn.enc (D.put (wS s) c.1) c.2, ()),
    fun sd =>
      (((), D.ans Sd sd (wS s) c.1),
        fun _ =>
          (s, ((fun a => (Sd.sd a sd, D.ans Sd sd (wS s) c.1 a)),
              D.Nn.enc (D.put (wS s) c.1) c.2,
              fun a => (D.upM (D.put (wS s) c.1) a, D.upR c.2 a)))))

end

namespace Spec

open Classical in
/-- The rule: a virtual instance of the shared part. -/
def freshV_virt : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type) (H : R.Honest Wi Wo)
      (s0 : W0 → H.Coin → Strat R.shape W0') (Ri : X → Ei.Str → Wi → Prop)
      (RiV : X → Ei.Str → W0 × Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (n : ℕ)
      (Kc K0 Kj : Type) (kc : Wo → Kc) (k0 : W0' → K0) (kj : Wo → Kj) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (put : Mb → Kc → Kc) (put0 : Mb → K0 → K0) (v : W0 → X × Ei.Str × Wi)
      (g0 : W0 → X' → Kc → K0) (gx : W0 → X × Wi → X' → X') (gk : W0 → X × Wi → X' → Kc → Kj),
    H.Fresh Ri bud kc Mb put → H.Bad = ∅ → (∀ w x, H.Hid w x = ∅) → (∀ ρ, bud ρ ∅) →
    (∀ w0, Ri (v w0).1 (v w0).2.1 (v w0).2.2) →
    (∀ w0 c ρ, ((s0 w0 c).run ρ).1 = ((H.strat (v w0).2.2 (v w0).1 c).run ρ).1) →
    (∀ w0 c ρ, k0 ((s0 w0 c).run ρ).2 =
      g0 w0 ((H.strat (v w0).2.2 (v w0).1 c).run ρ).2.1
        (kc ((H.strat (v w0).2.2 (v w0).1 c).run ρ).2.2)) →
    (∀ w0 x' M k, g0 w0 x' (put M k) = put0 M (g0 w0 x' k)) →
    (∀ x y w c ρ, RiV x y w →
      ((H.strat w.2 x c).run ρ).2.1 =
        gx w.1 (x, w.2) ((H.strat (v w.1).2.2 (v w.1).1 c).run ρ).2.1 ∧
      kj ((H.strat w.2 x c).run ρ).2.2 =
        gk w.1 (x, w.2) ((H.strat (v w.1).2.2 (v w.1).1 c).run ρ).2.1
          (kc ((H.strat (v w.1).2.2 (v w.1).1 c).run ρ).2.2)) →
    (∀ w0 a x' M k, gk w0 a x' (put M k) = gk w0 a x' k) →
    (H.sharedV s0).FreshV n RiV (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts))
      k0 kj Mb put0 Unit fun _ k => k

open Classical in
/-- Under the hypotheses below, the sending of a family, run by the shared part, is fresh for the
shared masks that it sends. x₀, y₀: any values (the sender reads neither). -/
def ldSendFam_freshSh : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (X W W' Sh : Type) (E₀ : ExtSpec)
      (D : N.Sender W W') (t : N.O → ℕ) (n : ℕ) (wS : Sh → W) (RiV : X → E₀.Str → Sh × W → Prop)
      (_x₀ : X) (_y₀ : E₀.Str) (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : D.Own Mb)
      (Kc K0 Kj : Type) (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc)
      (k0 : Sh × (N.Smp × N.ext.Str × N.Wit) → K0) (kj : N.Wit × W' → Kj) (put0 : Mb → K0 → K0)
      (g0 : Sh → N.Smp → Kc → K0) (gk : Sh → W → Kc → Kj),
    U.Laws Sd rd put → D.Nn.Hides (N.budT t) →
    (∀ x y w, RiV x y w → ∀ k, D.put w.2 k = D.put (wS w.1) k) →
    (∀ s σ f v, k0 (s, (σ, f, v)) = g0 s σ (rd (N.msgs v) (D.rest (wS s)))) →
    (∀ s σ M k, g0 s σ (put M k) = put0 M (g0 s σ k)) →
    (∀ x y w v, RiV x y w → kj (v, D.rest w.2) = gk w.1 w.2 (rd (N.msgs v) (D.rest (wS w.1)))) →
    (∀ s w M k, gk s w (put M k) = gk s w k) →
    ((ldSendFamHon Sd X E₀ D).sharedV (ldSendFamSh Sd D wS)).FreshV n RiV
      (fun J _ Ts => ∀ _ : J, N.budT t (ldSendFamSet N Sd (Finset.univ.biUnion Ts)))
      k0 kj Mb put0 Unit fun _ k => k

/-- Under the hypotheses below, the sending of a family in every slot is fresh for each slot's
masks, jointly over the slots, within the budget `N.budT t`. -/
def ldSendFam_freshLoc : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (X W W' W0 : Type) (E₀ : ExtSpec)
      (D : N.Sender W W') (t : N.O → ℕ) (n : ℕ) (RiV : X → E₀.Str → W0 × W → Prop) (Mb : Type)
      [Fintype Mb] [Nonempty Mb] (U : D.Own Mb) (Kc K0 : Type) (rd : N.Msg → W' → Kc)
      (put : Mb → Kc → Kc) (k0 : W0 → K0),
    U.Laws Sd rd put → D.Nn.Hides (N.budT t) →
    ((ldSendFamHon Sd X E₀ D).localV W0).FreshV n RiV
      (fun J _ Ts => ∀ j : J, N.budT t (ldSendFamSet N Sd (Ts j))) k0 (fun v => rd (N.msgs v.1) v.2)
      Unit (fun _ k => k) Mb put

/-- Under the hypotheses below, a sending run by the shared part does not look at masks sent before.
-/
def ldSendFam_blindSh : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (X W W' Sh : Type) (E₀ : ExtSpec)
      (D : N.Sender W W') (wS : Sh → W) (K0 Kj K0' Kj' M0 Mj : Type) (k0 : Sh → K0) (kj : W → Kj)
      (k0' : Sh × (N.Smp × N.ext.Str × N.Wit) → K0') (kj' : N.Wit × W' → Kj') (put0 : M0 → K0 → K0)
      (putj : Mj → Kj → Kj) (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj'),
    (∀ s s' M, k0 s' = put0 M (k0 s) → ∀ k, D.put (wS s') k = D.put (wS s) k) →
    (∀ s s' M z, k0 s' = put0 M (k0 s) → k0' (s', z) = put0' M (k0' (s, z))) →
    (∀ w w' Ms, kj w' = putj Ms (kj w) → ∀ k, D.put w' k = D.put w k) →
    (∀ w w' Ms (nw : N.Wit),
      kj w' = putj Ms (kj w) → kj' (nw, D.rest w') = putj' Ms (kj' (nw, D.rest w))) →
    ((ldSendFamHon Sd X E₀ D).sharedV (ldSendFamSh Sd D wS)).BlindV
      k0 kj k0' kj' M0 Mj put0 putj put0' putj'

/-- The same for a sending in every slot; it does not see the shared witness. -/
def ldSendFam_blindLoc : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (X W W' W0 : Type) (E₀ : ExtSpec)
      (D : N.Sender W W') (K0 Ki Ko M0 Mk : Type) (k0 : W0 → K0) (kci : W → Ki)
      (kco : N.Wit × W' → Ko) (put0 : M0 → K0 → K0) (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    (∀ w w' M, kci w' = puti M (kci w) → ∀ k, D.put w' k = D.put w k) →
    (∀ w w' M (nw : N.Wit),
      kci w' = puti M (kci w) → kco (nw, D.rest w') = puto M (kco (nw, D.rest w))) →
    ((ldSendFamHon Sd X E₀ D).localV W0).BlindV k0 kci k0 kco M0 Mk put0 puti put0 puto

end Spec

/-! ## Proof of the rule -/

theorem res_ofStrat :
    ∀ {s : Shape} {β : Type} (σ : Strat s β) (τ : RhoSh s (RoundSplits.const (RAnn.ofShared .sh) s)),
      (SStratR.ofStrat σ).res τ = (σ.run (RhoSh.all s τ)).2
  | [], _, _, _ => rfl
  | _ :: _, _, (_, k), (c, τ) => res_ofStrat (k c) τ

theorem map_unif_proj4 {C D M D' : Type} [Fintype C] [Nonempty C] [Fintype D] [Unique D] [Fintype M]
    [Nonempty M] [Fintype D'] [Unique D'] :
    (unif ((C × D) × (M × D'))).map (fun a => (a.1.1, a.2.1)) = unif (C × M) :=
  map_unif_equiv ((Equiv.prodUnique C D).prodCongr (Equiv.prodUnique M D'))

open Classical in
theorem freshV_virt : Spec.freshV_virt := by
  intro X X' Ei Eo R Wi Wo W0 W0' H s0 Ri RiV bud n Kc K0 Kj kc k0 kj Mb _ _ put put0 v g0 gx gk hF
    hBad hHid hb0 hv hrun h0 h0p hj hjp w0 J as ha ρ Ts hbud
  simp only [BatchSeqZk.slot_eq ρ] at hbud
  have hslot : ∀ j : Fin n, ρ.slot j = RhoSh.all R.shape (BRho.shared ρ) := BatchSeqZk.slot_eq ρ
  generalize hρ' : RhoSh.all R.shape (BRho.shared ρ) = ρ' at hbud hslot
  have hbT : bud ρ' (Finset.univ.biUnion Ts) := by
    by_cases hJ : Nonempty J
    · exact hbud (Classical.choice hJ)
    · haveI : IsEmpty J := not_nonempty_iff.mp hJ
      rw [Finset.univ_eq_empty, Finset.biUnion_empty]
      exact hb0 ρ'
  have hnw : ρ' ∉ H.withheld (v w0).2.2 (v w0).1 := fun h =>
    h.elim (fun h => by rw [hBad] at h; exact h) fun h => by rw [hHid] at h; exact h
  have hFr := hF (v w0).1 (v w0).2.1 (v w0).2.2 (hv w0) ρ' hnw _ hbT
  let Φ : View R × X' × Kc → (J → Option (View R × X' × Kj)) × K0 := fun z =>
    (fun j =>
        some (BatchSeqZk.restrict R ρ' (Ts j) z.1,
            gx w0 ((as j).1, (as j).2.2) z.2.1,
            gk w0 ((as j).1, (as j).2.2) z.2.1 z.2.2),
      g0 w0 z.2.1 z.2.2)
  have hseen : ∀ c : H.Coin × (Fin n → Unit),
      (H.sharedV s0).seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts c =
        Φ (H.seen kc (v w0).2.2 (v w0).1 ρ' (Finset.univ.biUnion Ts) c.1) := by
    intro c
    refine Prod.ext (funext fun j => ?_) ?_
    · refine (if_neg fun h => ?_).trans ?_
      · have h' := (LinkV.shared_withheld H s0 _).mp h
        rw [hBad] at h'
        exact h'
      · rw [hslot j.1, LinkV.shared_run]
        obtain ⟨e1, e2⟩ := hj (as j).1 (as j).2.1 (w0, (as j).2.2) c.1 ρ' (ha j)
        have hr : ((H.strat (v w0).2.2 (v w0).1 c.1).run ρ').1.rho = ρ' := Strat.rho_run _ _
        have h3 := BatchSeqZk.restrict_view R (T := Ts j) (T' := Finset.univ.biUnion Ts)
          (fun p hp => Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hp⟩)
          ((H.strat (v w0).2.2 (v w0).1 c.1).run ρ').1
        rw [hr] at h3
        show some (R.view (Ts j) ((s0 w0 c.1).run ρ').1,
              ((H.strat (as j).2.2 (as j).1 c.1).run ρ').2.1,
              kj ((H.strat (as j).2.2 (as j).1 c.1).run ρ').2.2) = _
        rw [hrun, e1, e2, ← h3]
        rfl
    · show k0 ((SStratR.ofStrat (s0 w0 c.1)).res (BRho.shared ρ)) = _
      rw [res_ofStrat, hρ', h0]
      rfl
  have hover : ∀ (M : Mb × (Fin n → Unit)) (z : View R × X' × Kc),
      HonestV.overV put0 (fun (_ : Unit) (k : Kj) => k) M (Φ z) =
        Φ (z.1, z.2.1, put M.1 z.2.2) := by
    intro M z
    refine Prod.ext (funext fun j => ?_) ?_
    · show some _ = some _
      rw [hjp]
    · exact (h0p _ _ _ _).symm
  have e1 : (fun a : (H.Coin × (Fin n → Unit)) × (Mb × (Fin n → Unit)) =>
        HonestV.overV put0 (fun (_ : Unit) (k : Kj) => k) a.2
          ((H.sharedV s0).seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts a.1)) =
      (Φ ∘ fun b : H.Coin × Mb =>
            ((H.seen kc (v w0).2.2 (v w0).1 ρ' (Finset.univ.biUnion Ts) b.1).1,
              (H.seen kc (v w0).2.2 (v w0).1 ρ' (Finset.univ.biUnion Ts) b.1).2.1,
              put b.2 (H.seen kc (v w0).2.2 (v w0).1 ρ' (Finset.univ.biUnion Ts) b.1).2.2)) ∘
        fun a => (a.1.1, a.2.1) := by
    funext a
    rw [hseen, hover]
    rfl
  have e2 : (H.sharedV s0).seenV k0 kj w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts =
      (Φ ∘ H.seen kc (v w0).2.2 (v w0).1 ρ' (Finset.univ.biUnion Ts)) ∘ Prod.fst := funext hseen
  show (unif ((H.Coin × (Fin n → Unit)) × (Mb × (Fin n → Unit)))).map _ =
    (unif (H.Coin × (Fin n → Unit))).map _
  refine (congrArg
    (fun φ => PMF.map φ (unif ((H.Coin × (Fin n → Unit)) × (Mb × (Fin n → Unit))))) e1).trans ?_
  refine Eq.trans ?_ (congrArg (fun φ => PMF.map φ (unif (H.Coin × (Fin n → Unit)))) e2).symm
  rw [← PMF.map_comp, map_unif_proj4, ← PMF.map_comp, hFr]
  exact ((PMF.map_comp _ _ _).trans
      (congrArg (PMF.map (Φ ∘ H.seen kc (v w0).2.2 (v w0).1 ρ' (Finset.univ.biUnion Ts)))
        (map_fst_unif (C := H.Coin) (D := Fin n → Unit)).symm)).trans
    (PMF.map_comp Prod.fst _ _)

/-! ## The sendings -/

open Classical in
theorem ldSendFam_freshSh : Spec.ldSendFam_freshSh := by
  intro E _ N Sd X W W' Sh E₀ D t n wS RiV x₀ y₀ Mb _ _ U Kc K0 Kj rd put k0 kj put0 g0 gk
    hU hZ hap hk0 hg0 hkj hgk
  refine freshV_virt X (X × N.Smp) E₀ (E₀.prod N.ext) (ldSendFam N Sd X E₀) W (N.Wit × W') Sh
    (Sh × (N.Smp × N.ext.Str × N.Wit)) (ldSendFamHon Sd X E₀ D) (ldSendFamSh Sd D wS)
    (fun _ _ _ => True) RiV (fun _ T => N.budT t (ldSendFamSet N Sd T)) n Kc K0 Kj
    (fun v => rd (N.msgs v.1) v.2) k0 kj Mb put put0 (fun s => (x₀, y₀, wS s))
    (fun s x' k => g0 s x'.2 k) (fun _ a x' => (a.1, x'.2)) (fun s a _ k => gk s a.2 k)
    (ldSendFam_fresh E N Sd X W W' E₀ D t (fun _ _ _ => True) Mb U Kc rd put hU hZ) rfl
    (fun _ _ => rfl) ?_ (fun _ => trivial) ?_ ?_ (fun s x' M k => hg0 s x'.2 M k) ?_
    (fun s a _ M k => hgk s a.2 M k)
  · intro _ a
    exact ⟨∅, Nat.zero_le _, fun p hp => absurd (Finset.mem_toLeft.1 hp) (Finset.notMem_empty _)⟩
  · rintro s c ⟨ρ₁, u, u'⟩
    rfl
  · rintro s c ⟨ρ₁, u, u'⟩
    exact hk0 s _ _ _
  · rintro x y w c ⟨ρ₁, u, u'⟩ hR
    have hp := hap x y w hR c.1
    have ha : D.ans Sd ρ₁ w.2 c.1 = D.ans Sd ρ₁ (wS w.1) c.1 := by
      unfold Sig.Sender.ans
      rw [hp]
    refine ⟨?_, ?_⟩
    · show (x, fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ w.2 c.1 a)) =
        (x, fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ (wS w.1) c.1 a))
      rw [ha]
    · show kj (fun a => (D.upM (D.put w.2 c.1) a, D.upR c.2 a), D.rest w.2) =
        gk w.1 w.2
          (rd (N.msgs fun a => (D.upM (D.put (wS w.1) c.1) a, D.upR c.2 a)) (D.rest (wS w.1)))
      rw [hp]
      exact hkj x y w _ hR

theorem ldSendFam_freshLoc : Spec.ldSendFam_freshLoc := by
  intro E _ N Sd X W W' W0 E₀ D t n RiV Mb _ _ U Kc K0 rd put k0 hU hZ
  exact freshV_local X (X × N.Smp) E₀ (E₀.prod N.ext) (ldSendFam N Sd X E₀) W (N.Wit × W') W0
    (ldSendFamHon Sd X E₀ D) (fun _ _ _ => True) RiV (fun _ T => N.budT t (ldSendFamSet N Sd T))
    n K0 Kc k0 (fun v => rd (N.msgs v.1) v.2) Mb put
    (ldSendFam_fresh E N Sd X W W' E₀ D t (fun _ _ _ => True) Mb U Kc rd put hU hZ)
    (fun _ _ => rfl) fun _ _ _ _ => trivial

theorem ldSendFam_blindSh : Spec.ldSendFam_blindSh := by
  intro E _ N Sd X W W' Sh E₀ D wS K0 Kj K0' Kj' M0 Mj k0 kj k0' kj' put0
    putj put0' putj' h1 h2 h3 h4
  refine ⟨fun s s' M c σ h => ?_, fun s s' w w' M Ms x c ρ h hj => ?_⟩
  · show k0' ((SStratR.ofStrat (ldSendFamSh Sd D wS s' c)).res σ) =
      put0' M (k0' ((SStratR.ofStrat (ldSendFamSh Sd D wS s c)).res σ))
    rw [res_ofStrat, res_ofStrat]
    generalize RhoSh.all (N.sh Sd) σ = ρ
    obtain ⟨ρ₁, u, u'⟩ := ρ
    have hp := h1 s s' M h c.1
    have ha : D.ans Sd ρ₁ (wS s') c.1 = D.ans Sd ρ₁ (wS s) c.1 := by
      unfold Sig.Sender.ans
      rw [hp]
    show k0' (s', ((fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ (wS s') c.1 a)),
            D.Nn.enc (D.put (wS s') c.1) c.2,
            fun a => (D.upM (D.put (wS s') c.1) a, D.upR c.2 a))) = _
    rw [hp, ha]
    exact h2 s s' M _ h
  · rw [LinkV.shared_run, LinkV.shared_run]
    obtain ⟨ρ₁, u, u'⟩ := ρ
    have hp := h1 s s' M h c.1.1
    have ha : D.ans Sd ρ₁ (wS s') c.1.1 = D.ans Sd ρ₁ (wS s) c.1.1 := by
      unfold Sig.Sender.ans
      rw [hp]
    have hq := h3 w w' Ms hj c.1.1
    have hb : D.ans Sd ρ₁ w' c.1.1 = D.ans Sd ρ₁ w c.1.1 := by
      unfold Sig.Sender.ans
      rw [hq]
    refine ⟨?_, ?_, ?_⟩
    · show (((D.Nn.enc (D.put (wS s') c.1.1) c.1.2, ()), ρ₁, ((), D.ans Sd ρ₁ (wS s') c.1.1),
          u, ()) : Tr (N.sh Sd)) =
        ((D.Nn.enc (D.put (wS s) c.1.1) c.1.2, ()), ρ₁, ((), D.ans Sd ρ₁ (wS s) c.1.1), u, ())
      rw [hp, ha]
      rfl
    · show (x, fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ w' c.1.1 a)) =
        (x, fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ w c.1.1 a))
      rw [hb]
    · show kj' (fun a => (D.upM (D.put w' c.1.1) a, D.upR c.1.2 a), D.rest w') =
        putj' Ms (kj' (fun a => (D.upM (D.put w c.1.1) a, D.upR c.1.2 a), D.rest w))
      rw [hq]
      exact h4 w w' Ms _ hj

theorem ldSendFam_blindLoc : Spec.ldSendFam_blindLoc := by
  intro E _ N Sd X W W' W0 E₀ D K0 Ki Ko M0 Mk k0 kci kco put0 puti puto h1 h2
  exact blindV_local X (X × N.Smp) E₀ (E₀.prod N.ext) (ldSendFam N Sd X E₀) W (N.Wit × W') W0
    (ldSendFamHon Sd X E₀ D) K0 Ki Ko k0 kci kco M0 Mk put0 puti puto
    (ldSendFam_blind E N Sd X W W' E₀ D Ki Ko Mk kci kco puti puto h1 h2)

end Cb
