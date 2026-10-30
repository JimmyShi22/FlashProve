-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LawsCompose.lean: THE BLOCKS' LAWS COMPOSE: from a law for each of two blocks,
against two typed verifiers, the law of the two blocks laid as one against the two typed verifiers
one after the other.

The setting. `keyCoreAtGathered` (Johnson/Desc/Sound/KeyAtGathered.lean) lets one proved typed
block stand against several blocks of the fold, laid as one (`Block.andThen`): what is then owed is
ONE law (`DecideLaw`, Johnson/Desc/Sound/KeyDecides.lean) of the gathered block. The kinds' laws
come a kind, not a chain. A typed list's one block is its blocks' reductions one after the other
(`BK.seq`): its goodness is proved of the whole; of what stands between its parts only the VERIFIERS
matter here.

What is said.
  `StepLaw b base ds back R M rdA rdB cA iB`: a block's law against a typed REDUCTION R (no joint,
    no relation, no goodness): at every statement with cA and every transcript at which the stage's
    own tests pass, every word shown is below the prime and what is shown has the declared shape: if
    `decide` returns s', then iB holds of (s', the oracles left), and R at `M.view τ` puts out its
    reading. `decideLaw_iff`: `DecideLaw` IS that, at R := the typed block's reduction and cA :=
    "the typed condition, read, and the invariant".
  `StepsCompose`, `stepsCompose`: THE RULE: `StepLaw` of p from cA to iM and of q from iM to iB give
    `StepLaw` of `p.andThen name q`, at the two stretches in a row, against the two reductions one
    after the other, along `M₁.app M₂`, from cA to iB. Asked besides, of the first stretch alone:
    its trees are listed, it opens no tree that is sent behind it, it has as many rounds as p
    declares and opens as many leaves as p reads (the clauses of `Tiled`).
  `decideLaw_seq`: so `DecideLaw` of the gathered block against `k₁.seq k₂ d`.
SO BETWEEN TWO PARTS OF ONE PROVED TYPED BLOCK A ROW OF THE TABLE OF JOINTS IS A READING AND AN
INVARIANT ALONE: no condition, no relation, and no goodness of a part is asked.
Beneath: `step_andThen_inv`: the step of two blocks laid as one returns only where both steps
return.

Limits. A rule, for two blocks. THE SECOND LAW IS ASKED WITHOUT THE TYPED CONDITION of the joint
between: what it needs of the statement between must lie in iM. The first law owes iM under cA,
wherever the first block's tests pass and it returns: so a condition on what the first stretch
leaves unturned (the public part; the stored table: "no collision at the record's seed") can ride in
iM; a condition on what the first stretch itself sends, which holds only up to an error, cannot: a
kind that needs such a condition sits as a seat of its own.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyAtGathered
import OnBytes.Flat.KindsRow
import Ior.SeqProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl : Type} {F : Frame}

/-! ## 1 The step of two blocks laid as one returns only where both return -/

theorem roundsFit_app_inv : ∀ (ds₁ ds₂ : List Fmt.DeclaredRound) (rs₁ rs₂ : List Fmt.RoundView),
    rs₁.length = ds₁.length → roundsFit (ds₁ ++ ds₂) (rs₁ ++ rs₂) = true →
    roundsFit ds₁ rs₁ = true ∧ roundsFit ds₂ rs₂ = true
  | [], _, [], _, _, h => ⟨rfl, h⟩
  | [], _, _ :: _, _, h, _ => by cases h
  | _ :: _, _, [], _, h, _ => by cases h
  | _ :: ds₁, ds₂, _ :: rs₁, rs₂, hl, h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 h
    obtain ⟨h1, h2⟩ := roundsFit_app_inv ds₁ ds₂ rs₁ rs₂ (Nat.succ.inj hl) hb
    exact ⟨Bool.and_eq_true_iff.2 ⟨ha, h1⟩, h2⟩

/-- **The converse of `step_andThen`.** -/
theorem step_andThen_inv (ft : ℕ) (name : String) (p q : Block S Cl) (s s₂ : S)
    (R₁ R₂ : List Fmt.RoundView) (c : List OpenedColumn) (k : ℕ) (l₁ : R₁.length = p.rounds.length)
    (h : (p.andThen name q).step ft s (R₁ ++ R₂) c = .ok (s₂, k)) :
    ∃ s₁ k₁ k₂, p.step ft s R₁ c = .ok (s₁, k₁) ∧ q.step ft s₁ R₂ (c.drop k₁) = .ok (s₂, k₂) ∧
      k = k₁ + k₂ := by
  obtain ⟨f, e, hk, dd⟩ := (step_ok_iff ft (p.andThen name q) s s₂ (R₁ ++ R₂) c k).1 h
  obtain ⟨f₁, f₂⟩ := roundsFit_app_inv p.rounds q.rounds R₁ R₂ l₁ f
  have hG : groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn)) =
      groupsOf ft p.rounds (R₁.map (·.drawn)) ++ groupsOf ft q.rounds (R₂.map (·.drawn)) := by
    rw [List.map_append, groupsOf_app ft _ _ _ _ (by rw [List.length_map, l₁])]
  generalize hG₁ : groupsOf ft p.rounds (R₁.map (·.drawn)) = G₁ at hG
  generalize hG₂ : groupsOf ft q.rounds (R₂.map (·.drawn)) = G₂ at hG
  have e' : (c.take k).map (fun x => (x.1, x.2.1, x.2.2.length)) =
      G₁.flatMap id ++ G₂.flatMap id := by
    have e0 : (c.take k).map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn))).flatMap id := e
    rw [e0, hG, List.flatMap_append]
  have hk' : k = (G₁.flatMap id).length + (G₂.flatMap id).length := by
    have hk0 : k = ((groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn))).flatMap
      id).length := hk
    rw [hk0, hG, List.flatMap_append, List.length_append]
  have hT : c.take k = c.take (G₁.flatMap id).length ++
      (c.drop (G₁.flatMap id).length).take (G₂.flatMap id).length := by
    rw [hk']
    exact List.take_add
  have hlen : (c.take k).length = k := by
    have := congrArg List.length e'
    rw [List.length_map, List.length_append, ← hk'] at this
    exact this
  have hck : k ≤ c.length := by
    rw [List.length_take] at hlen
    omega
  have hl₁ : (c.take (G₁.flatMap id).length).length = (G₁.flatMap id).length := by
    rw [List.length_take]
    omega
  rw [hT, List.map_append] at e'
  obtain ⟨e₁, e₂⟩ := List.append_inj e' (by rw [List.length_map, hl₁])
  have hn : (R₁.map noDigest).length = p.rounds.length := by rw [List.length_map, l₁]
  have ho : (regroup (G₁.map (·.length)) (c.take (G₁.flatMap id).length)).length =
      p.openings := by
    rw [regroup_len, List.length_map, ← hG₁, groupsOf_len ft _ _ (by rw [List.length_map, l₁]),
      openings_eq]
  have dd' : (p.decide s (((R₁ ++ R₂).map noDigest).take p.rounds.length)
        ((regroup ((groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn))).map (·.length))
          (c.take k)).take p.openings)).bind (fun s' =>
      q.decide s' (((R₁ ++ R₂).map noDigest).drop p.rounds.length)
        ((regroup ((groupsOf ft (p.rounds ++ q.rounds) ((R₁ ++ R₂).map (·.drawn))).map (·.length))
          (c.take k)).drop p.openings)) = .ok s₂ := dd
  rw [hG, hT, List.map_append, List.map_append,
    regroup_app _ _ _ _ (by rw [hl₁, flat_len]),
    List.take_left' hn, List.drop_left' hn, List.take_left' ho, List.drop_left' ho] at dd'
  cases hd₁ : p.decide s (R₁.map noDigest)
      (regroup (G₁.map (·.length)) (c.take (G₁.flatMap id).length)) with
  | error er =>
    rw [hd₁] at dd'
    cases dd'
  | ok s₁ =>
    rw [hd₁] at dd'
    refine ⟨s₁, (G₁.flatMap id).length, (G₂.flatMap id).length, ?_, ?_, hk'⟩
    · refine (step_ok_iff ft p s s₁ R₁ c _).2 ⟨f₁, ?_, ?_, ?_⟩
      · rw [hG₁]
        exact e₁
      · rw [hG₁]
      · unfold groupsAt
        rw [hG₁]
        exact hd₁
    · refine (step_ok_iff ft q s₁ s₂ R₂ _ _).2 ⟨f₂, ?_, ?_, ?_⟩
      · rw [hG₂]
        exact e₂
      · rw [hG₂]
      · unfold groupsAt
        rw [hG₂]
        exact dd'

/-! ## 2 A block's law against a typed reduction -/

/-- **A block's law against a typed reduction.** -/
def StepLaw (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) {XA XB : Type}
    (R : Reduction XA XB) (M : Maps ds R.shape) (rdA : S × F.E.Str → XA)
    (rdB : S × F.E.Str → XB) (cA iB : S × F.E.Str → Prop) : Prop :=
  ∀ (s s' : S) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds)),
    cA (s, y) →
    sTests (ckP .two) (stg F base ds) y τ = true →
    viewWordsBelowPrime (sView (ckP .two) (stg F base ds) y τ) = true →
    Shown F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
      (sView (ckP .two) (stg F base ds) y τ).opened →
    b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened) = .ok s' →
    iB (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) ∧
      R.out (rdA (s, y)) (M.view τ) =
        some (rdB (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)))

/-- `DecideLaw` is that. -/
theorem decideLaw_iff (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {A B : JK} (k : BK A B) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) :
    DecideLaw b base ds back k M rdA rdB iA iB ↔
      StepLaw b base ds back k.R.red M rdA rdB (fun a => A.on (rdA a) ∧ iA a) iB :=
  ⟨fun h s s' y τ hc => h s s' y τ hc.1 hc.2, fun h s s' y τ ha hi => h s s' y τ ⟨ha, hi⟩⟩

theorem trL_join : ∀ (ds es : List RDT) (π : Iop.Tr (uLT (ckP .two) ds))
    (σ : Iop.Tr (uLT (ckP .two) es)), Maps.trL ds es (joinR (ckP .two) ds es π σ) = π
  | [], _, (), _ => rfl
  | _ :: ds, es, (m, c, π), σ => congrArg (fun x => (m, c, x)) (trL_join ds es π σ)

theorem trR_join : ∀ (ds es : List RDT) (π : Iop.Tr (uLT (ckP .two) ds))
    (σ : Iop.Tr (uLT (ckP .two) es)), Maps.trR ds es (joinR (ckP .two) ds es π σ) = σ
  | [], _, _, _ => rfl
  | _ :: ds, es, (_, _, π), σ => trR_join ds es π σ

/-! ## 3 The rule -/

/-- **The blocks' laws compose.** -/
def StepsCompose : Prop :=
  ∀ (S Cl : Type) (F : Frame) (name : String) (p q : Block S Cl) (base : ℕ) (ds es : List RDT)
    (back : List Fmt.RoundView) (XA XM XB : Type) (R₁ : Reduction XA XM) (R₂ : Reduction XM XB)
    (M₁ : Maps ds R₁.shape) (M₂ : Maps es R₂.shape) (rdA : S × F.E.Str → XA)
    (rdM : S × F.E.Str → XM) (rdB : S × F.E.Str → XB) (cA iM iB : S × F.E.Str → Prop),
    ListedAt F base ds → OpensBelow base ds → ds.length = p.rounds.length →
    (∀ (y : F.E.Str) (π : Iop.Tr (uLT (ckP .two) ds)),
      ((p.reads F.ft ((sView (ckP .two) (stg F base ds) y π).rounds.map (·.drawn))).flatMap
        id).length = (sView (ckP .two) (stg F base ds) y π).opened.length) →
    StepLaw p base ds [] R₁ M₁ rdA rdM cA iM →
    StepLaw q (base + nTrees ds) es back R₂ M₂ rdM rdB iM iB →
    StepLaw (p.andThen name q) base (ds ++ es) back (R₁.seq R₂) (M₁.app M₂) rdA rdB cA iB

theorem stepsCompose : StepsCompose := by
  intro S Cl F name p q base ds es back XA XM XB R₁ R₂ M₁ M₂ rdA rdM rdB cA iM iB hL hO hlen hOw
    law₁ law₂ s s₂ y τ hc ht hw hS hd
  obtain ⟨π, σ, rfl⟩ : ∃ π σ, τ = joinR (ckP .two) ds es π σ :=
    ⟨_, _, (joinR_split (ckP .two) ds es τ).symm⟩
  have eR := sView_rounds_join (ckP .two) F base y
    (y.1, sLeft (ckP .two) (stg F base ds) y π) π σ
  have eC := sView_opened_join (ckP .two) F base hL hO y π σ
  rw [sTests_join (ckP .two) F base hL hO y π σ] at ht
  obtain ⟨ht₁, ht₂⟩ := Bool.and_eq_true_iff.1 ht
  generalize hV : sView (ckP .two) (stg F base (ds ++ es)) y (joinR (ckP .two) ds es π σ) = V
    at eR eC hw hS hd
  obtain ⟨Vr, Vc⟩ := V
  have eR' : Vr = _ := eR
  have eC' : Vc = _ := eC
  subst eR' eC'
  rw [okViewW_app] at hw
  obtain ⟨hw₁, hw₂⟩ := Bool.and_eq_true_iff.1 hw
  have l₁ : (sView (ckP .two) (stg F base ds) y π).rounds.length = p.rounds.length :=
    (rvT_length (ckP .two) ds π).trans hlen
  -- the gathered block's step, and its two parts
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hst := (step_ok_iff F.ft (p.andThen name q) s s₂ _ _ _).2
    ⟨hS2, by rw [List.take_length]; exact hS3, by rw [← hS3, List.length_map],
      by rw [List.take_length]; exact hd⟩
  rw [List.append_assoc] at hst
  obtain ⟨s₁, k₁, k₂, st₁, st₂, hk⟩ := step_andThen_inv F.ft name p q s s₂ _ _ _ _ l₁ hst
  have hk₁ : k₁ = (sView (ckP .two) (stg F base ds) y π).opened.length :=
    (step_count F.ft p s _ _ s₁ k₁ st₁).trans (hOw y π)
  obtain ⟨a1, a2, -, a4⟩ := (step_ok_iff F.ft p s s₁ _ _ k₁).1 st₁
  obtain ⟨b1, b2, -, b4⟩ := (step_ok_iff F.ft q s₁ s₂ _ _ k₂).1 st₂
  have hk₂ : k₂ = (sView (ckP .two) (stg F (base + nTrees ds) es)
      (y.1, sLeft (ckP .two) (stg F base ds) y π) σ).opened.length := by
    rw [List.length_append] at hk
    omega
  rw [hk₁, List.take_left] at a2 a4
  rw [hk₁, List.drop_left, hk₂, List.take_length] at b2 b4
  obtain ⟨i₁, o₁⟩ := law₁ s s₁ y π hc ht₁ hw₁
    ⟨by rw [List.append_nil]; exact l₁, by rw [List.append_nil]; exact a1,
      by rw [List.append_nil]; exact a2⟩ (by rw [List.append_nil]; exact a4)
  obtain ⟨i₂, o₂⟩ := law₂ s₁ s₂ (y.1, sLeft (ckP .two) (stg F base ds) y π) σ i₁ ht₂ hw₂
    ⟨roundsFit_len _ _ b1, b1, b2⟩ b4
  rw [sLeft_join (ckP .two) F base y π σ]
  refine ⟨i₂, ?_⟩
  rw [Maps.view_app, trL_join, trR_join]
  show (R₁.out (rdA (s, y)) (Iop.Tr.fst (Iop.Tr.app (M₁.view π) (M₂.view σ)))).bind (fun b =>
    R₂.out b (Iop.Tr.snd (s := R₁.shape) (Iop.Tr.app (M₁.view π) (M₂.view σ)))) = _
  rw [Iop.Tr.fst_app, Iop.Tr.snd_app, o₁]
  exact o₂

/-- **So the one law of two blocks laid as one, against two typed blocks one after the other**: from
the first block's law and the second's law against its typed block's reduction. -/
theorem decideLaw_seq (name : String) (p q : Block S Cl) (base : ℕ) (ds es : List RDT)
    (back : List Fmt.RoundView) {A Bm B : JK} (k₁ : BK A Bm) (k₂ : BK Bm B) (d : A.W)
    (M₁ : Maps ds k₁.R.red.shape) (M₂ : Maps es k₂.R.red.shape)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdM : S × F.E.Str → Bm.X × Bm.E.Str)
    (rdB : S × F.E.Str → B.X × B.E.Str) (iA iM iB : S × F.E.Str → Prop)
    (hL : ListedAt F base ds) (hO : OpensBelow base ds) (hlen : ds.length = p.rounds.length)
    (hOw : ∀ (y : F.E.Str) (π : Iop.Tr (uLT (ckP .two) ds)),
      ((p.reads F.ft ((sView (ckP .two) (stg F base ds) y π).rounds.map (·.drawn))).flatMap
        id).length = (sView (ckP .two) (stg F base ds) y π).opened.length)
    (law₁ : DecideLaw p base ds [] k₁ M₁ rdA rdM iA iM)
    (law₂ : StepLaw q (base + nTrees ds) es back k₂.R.red M₂ rdM rdB iM iB) :
    DecideLaw (p.andThen name q) base (ds ++ es) back (k₁.seq k₂ d) (M₁.app M₂) rdA rdB iA iB := by
  intro s s' y τ ha hi ht hw hS hd
  obtain ⟨h1, h2⟩ := stepsCompose S Cl F name p q base ds es back _ _ _ k₁.R.red k₂.R.red M₁ M₂ rdA
    rdM rdB _ iM iB hL hO hlen hOw ((decideLaw_iff p base ds [] k₁ M₁ rdA rdM iA iM).1 law₁) law₂
    s s' y τ ⟨ha, hi⟩ ht hw hS hd
  exact ⟨h1, (IOR.red_seq_out k₁.R k₂.R _ _).trans h2⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.decideLaw_seq
#print axioms VerifiableInference.Desc.Sound.step_andThen_inv
#print axioms VerifiableInference.Desc.Sound.decideLaw_iff
#print axioms VerifiableInference.Desc.Sound.stepsCompose
