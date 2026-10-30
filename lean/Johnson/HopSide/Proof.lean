-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HopSide/Proof.lean: from the real experiment of the scheme with the whole key published to
mode I of the token challenger: the proofs of the two statements of Johnson/HopSide/Spec.lean.

General lemmas. This file states no goal of the release. The experiments between (stepC, stepD,
twinW) are a device of this proof and stand in no statement on the scheme.

The way, each step an equality of the adversary's output distributions but the last:
  real_cut    the real experiment, and the same with the kept key passed through cut.
  cut_drop    what is not shown is not made: a batch of one request that is not the adversary's own
              runs no program (Rom.forgetCall).
  twin_drop   the token challenger's steps, as ordinary oracle algorithms with the store of all
              strings in the state, against that experiment: the map of states reads the scheme's
              key off the key with tokens and the store (lump_gAdm, Compile/DeferRun/Lump.lean;
              SameStep at lazy sampling).
  realTwin    these three, and the general step to mode R behind the exchange of queries
              (viaErased_modeR, Compile/DeferRun/Hop.lean).
  hopTwin     the hop (real_to_modeI), at the counts of Spec.withinTwin
              (Johnson/TokenRules/Spec.lean), which is a hypothesis here. (It is proved in
              Johnson/TokenRules/Closed.lean: countTwinT.)
  sess_noCopies   a small member of SameStep's clause sess: at a key without copies it holds.

Limits. realTwin and hopTwin are called by nothing on the way to the statement of index privacy:
that way calls real_twinW and the general lemma under hopTwin, at other counts (hop_prem,
Johnson/LateSide/Whole.lean). The price in hopTwin is a formula (Rom.costTotal); no number is
evaluated.
Follows the pattern of Compile/Batch/PubProgReal.lean.

-/
import Johnson.HopSide.Spec
import Compile.DeferRun.Hop
import Compile.DeferRun.Lump
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.HopSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open _root_.Compile.GlueB (GCall GIn GAdm realW ownPf)
open _root_.Compile.DeferRun (erasedStep)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## Tools -/

section Tools
variable {S : OSpec} {σ α β : Type}

/-- A property of all outputs holds of every outcome of a run, under any rule. -/
theorem post_interp {P : α → Prop} (hd : Handler S σ) :
    ∀ {c : OComp S α}, Post P c → ∀ (s : σ), ∀ y ∈ (c.interp hd s).support, P y.1
  | .pure _, h, _, y, hy => by
    simp only [OComp.interp, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact h
  | .query _ _ _, h, _, y, hy => by
    simp only [OComp.interp, PMF.mem_support_bind_iff] at hy
    obtain ⟨p, _, hy⟩ := hy
    exact post_interp hd (h p.1) p.2 y hy
  | .sample _ _, h, s, y, hy => by
    simp only [OComp.interp, PMF.mem_support_bind_iff] at hy
    obtain ⟨r, _, hy⟩ := hy
    exact post_interp hd (h r) s y hy

theorem post_runLazy {P : α → Prop} {c : OComp S α} (h : Post P c) (T : Table S) :
    ∀ y ∈ (c.runLazy T).support, P y.1 := by
  rw [← OComp.interp_lazy]
  exact post_interp Handler.lazy h T

theorem map_congr_support (p : PMF α) {f g : α → β} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g :=
  Rom.bind_congr_support p fun a ha => congrArg PMF.pure (h a ha)

end Tools

/-! ## Reading a key off a store -/

section Keys
variable {I X : Type} {lam : ℕ}

theorem toK_prefix {L' : BatchProtocolWithLeafBody I X} {vs vs' : List Bits} (hp : vs <+: vs') (pre : Bits)
    (T : TreeT lam L') (hT : ∀ a ∈ T.tok, a.1 < vs.length) :
    T.toK (fun t => vs'.getD t []) pre = T.toK (fun t => vs.getD t []) pre := by
  refine congrArg (fun f => (⟨f, T.lv⟩ : TreeK lam L')) (funext fun j => ?_)
  cases hj : T.tok[j]? with
  | none => rfl
  | some a =>
    show (⟨T.body j, pre ++ vs'.getD a.1 []⟩ : LeafIn L') = ⟨T.body j, pre ++ vs.getD a.1 []⟩
    rw [TokenSide.getD_of_prefix hp (hT a (List.mem_of_getElem? hj))]

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

theorem iskOf_prefix {k : IskT lam L Bd aT aL} {vs vs' : List Bits} (hk : KeyIn k vs)
    (hp : vs <+: vs') (pre : Bits) : iskOf pre k vs' = iskOf pre k vs := by
  refine congrArg (fun c => (⟨k.i, c⟩ : Isk lam L Bd aT aL))
    (List.map_congr_left fun t ht => ?_)
  show (⟨t.r, t.tree.toK (fun u => vs'.getD u []) pre, t.seed⟩ : TabK lam L Bd aT aL) =
    ⟨t.r, t.tree.toK (fun u => vs.getD u []) pre, t.seed⟩
  rw [toK_prefix hp pre t.tree (hk t ht)]

theorem KeyIn.mono {k : IskT lam L Bd aT aL} {vs vs' : List Bits} (hk : KeyIn k vs)
    (hp : vs <+: vs') : KeyIn k vs' :=
  fun t ht a ha => lt_of_lt_of_le (hk t ht a ha) hp.length_le

end Keys

/-! ## A routed step with exchanged queries -/

section Via
variable {I X : Type} {lam : ℕ} {L' : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L') {Out In : Type}

theorem via_erasedStep (C : Chall (typedOracleFamily lam W.K L') (splitT lam W.K L') Out In)
    (s : C.τ × List Bits) (m : Out) (hR : RoutedT W (C.step s.1 m)) :
    (erasedStep C s m).via (ghost W) =
      (plainOf (C.step s.1 m) s.2).bind fun o => pure (o.1.1, (o.1.2, o.2)) := by
  have h1 : Routed W (erasedStep C s m) :=
    Routed.bind (routedErase _ _ _ _ W _ _ s.2 hR) fun _ => trivial
  rw [← realQ_via _ _ _ _ W _ _ h1]
  exact realQ_bind _ _

end Via

/-! ## The experiments between -/

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
  (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
  (cut : Isk lam L Bd aT aL → Isk lam L Bd aT aL) (i : I)

/-- The steps of the real experiment, the kept key passed through cut. -/
def stepC (s : Option (Isk lam L Bd aT aL)) (c : GCall X Unit) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
      (GIn (FullKey lam L aT aL) (RequestProof lam L) × Option (Isk lam L Bd aT aL)) :=
  match c, s with
  | .setup, _ => (commitW W S cA h i).bind fun o => pure (.inl o.1, some (cut o.2))
  | .batch _, none => pure (.inr [], none)
  | .batch b, some k =>
      (proveW W cA r₀ h k b.pairs).bind fun πs => pure (.inr (ownPf b πs.val), some k)

/-- A batch of one request that is not the adversary's own. -/
def unseen : GCall X Unit → Bool
  | .batch [(_, _, false)] => true
  | _ => false

/-- The same steps; of a batch of which nothing is shown nothing is made. -/
def stepD (s : Option (Isk lam L Bd aT aL)) (c : GCall X Unit) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
      (GIn (FullKey lam L aT aL) (RequestProof lam L) × Option (Isk lam L Bd aT aL)) :=
  if unseen c then pure (.inr [], s) else stepC W S cA r₀ h cut i s c

variable {α : Type}

theorem real_cut (hc : ∀ (k : Isk lam L Bd aT aL) (b : List (X × Unit)),
      proveW W cA r₀ h (cut k) b = proveW W cA r₀ h k b)
    (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (interact (realW (argW W S cA r₀ p h) i) A (none, T)).map Prod.fst =
      (interact (World.ofOComp (stepC W S cA r₀ h cut i)) A (none, T)).map Prod.fst := by
  have e := interact_lump (realW (argW W S cA r₀ p h) i) (World.ofOComp (stepC W S cA r₀ h cut i))
    (fun x => (x.1.map cut, x.2)) (fun _ => True)
    (fun x o q _ => by
      show ((lazyAnswer x.2 o q).map _).map _ = (lazyAnswer x.2 o q).map _
      rw [PMF.map_comp]
      rfl)
    (fun x m _ => by
      obtain ⟨s, T⟩ := x
      rcases m with _ | b
      · show ((((commitW W S cA h i).bind fun o => pure (Sum.inl o.1, some o.2)).runLazy T).map
            _).map _ =
          (((commitW W S cA h i).bind fun o => pure (Sum.inl o.1, some (cut o.2))).runLazy T).map _
        rw [Life2.runLazy_bind_pure, Life2.runLazy_bind_pure, PMF.map_comp, PMF.map_comp,
          PMF.map_comp]
        rfl
      · rcases s with _ | k
        · show ((PMF.pure ((Sum.inr [], none), T)).map _).map _ =
            (PMF.pure ((Sum.inr [], none), T)).map _
          simp only [PMF.pure_map]
          rfl
        · show ((((proveW W cA r₀ h k b.pairs).bind fun πs =>
              pure (Sum.inr (ownPf b πs.val), some k)).runLazy T).map _).map _ =
            (((proveW W cA r₀ h (cut k) b.pairs).bind fun πs =>
              pure (Sum.inr (ownPf b πs.val), some (cut k))).runLazy T).map _
          rw [hc, Life2.runLazy_bind_pure, Life2.runLazy_bind_pure, PMF.map_comp, PMF.map_comp,
            PMF.map_comp]
          rfl)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) A (none, T) trivial
  exact (congrArg (PMF.map Prod.fst) e).symm.trans (PMF.map_comp _ _ _) |>.symm

/-- **What is not shown is not made**: an equality of the adversary's output distributions, from
every state and table. The two experiments part at one kind of call alone: a batch of one request
that is not the adversary's own, after the setup. There the first runs the scheme's prover, drops
the proof, replies with the empty list (ownPf of such a batch is empty whatever the proof is) and
keeps its state; the second gives that reply at once. That is the form which the library's lemma
asks of a step: "an algorithm, its result dropped, then a constant reply and the state as it was"
(Rom.forgetCall, Rom/Forget.lean; its statement: Rom.Spec.forgetCall, Rom/SpecForget.lean). Both
experiments answer by oracle algorithms over one lazily sampled table (World.ofOComp), as that lemma
asks. Why it is exact: an entry of a lazily sampled table that was drawn and never shown has the law
of an entry that is drawn later. -/
theorem cut_drop (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (s : Option (Isk lam L Bd aT aL))
    (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (interact (World.ofOComp (stepC W S cA r₀ h cut i)) A (s, T)).map Prod.fst =
      (interact (World.ofOComp (stepD W S cA r₀ h cut i)) A (s, T)).map Prod.fst := by
  refine Rom.forgetCall _ _ _ _ _ (stepC W S cA r₀ h cut i) (stepD W S cA r₀ h cut i)
    (fun s m => ?_) A s T
  rcases m with _ | b
  · exact Or.inl rfl
  · rcases b with _ | ⟨⟨x, u, own⟩, _ | ⟨v, l⟩⟩
    · exact Or.inl rfl
    · cases own
      · rcases s with _ | k
        · exact Or.inl rfl
        · refine Or.inr ⟨_, proveW W cA r₀ h k [(x, u)], .inr [], ?_, rfl⟩
          show ((proveW W cA r₀ h k [(x, u)]).bind fun πs =>
            pure (Sum.inr (ownPf [(x, u, false)] πs.val), some k)) = _
          refine congrArg _ (funext fun πs => ?_)
          have e : ownPf [(x, u, false)] πs.val = [] := by
            rcases πs.val with _ | ⟨a, l⟩ <;> rfl
          rw [e]
          rfl
      · exact Or.inl rfl
    · cases own <;> exact Or.inl rfl

/-! ## The token challenger's steps against that experiment -/

/-- The token challenger's steps as ordinary oracle algorithms, with exchanged queries. -/
abbrev twinW : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (GIn (FullKey lam L aT aL) (RequestProof lam L)) :=
  World.ofOComp fun s m => (erasedStep (challT W S cA r₀ h tl i) s m).via (ghost W)

variable {W S cA r₀ h tl cut i}

theorem reply_twin (hR : ∀ s c, RoutedT W ((challT W S cA r₀ h tl i).step s c))
    (s : Option (IskT lam L Bd aT aL)) (vs : List Bits)
    (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (m : GCall X Unit) :
    (twinW W S cA r₀ h tl i).reply ((s, vs), T) m =
      ((plainOf ((challT W S cA r₀ h tl i).step s m) vs).runLazy T).map fun y =>
        (y.1.1.1, ((y.1.1.2, y.1.2), y.2)) := by
  show (((erasedStep (challT W S cA r₀ h tl i) (s, vs) m).via (ghost W)).runLazy T).map _ = _
  rw [via_erasedStep W (challT W S cA r₀ h tl i) (s, vs) m (hR s m)]
  refine (congrArg (PMF.map _) (Life2.runLazy_bind_pure _ _ T)).trans ?_
  exact PMF.map_comp _ _ _

theorem reply_twin_setup (hR : ∀ s c, RoutedT W ((challT W S cA r₀ h tl i).step s c))
    (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (twinW W S cA r₀ h tl i).reply ((none, []), T) .setup =
      ((plainOf (commitT W S cA h tl i) []).runLazy T).map fun y =>
        (.inl y.1.1.1, ((some y.1.1.2, y.1.2), y.2)) := by
  have e1 : plainOf ((challT W S cA r₀ h tl i).step none .setup) [] =
      (plainOf (commitT W S cA h tl i) []).bind fun q =>
        pure ((Sum.inl q.1.1, some q.1.2), q.2) := plainOf_bind _ _ _
  rw [reply_twin hR, e1]
  refine (congrArg (PMF.map _) (Life2.runLazy_bind_pure (plainOf (commitT W S cA h tl i) [])
    (fun q => ((Sum.inl q.1.1, some q.1.2), q.2)) T)).trans ?_
  exact PMF.map_comp _ _ _

theorem reply_twin_batch (hR : ∀ s c, RoutedT W ((challT W S cA r₀ h tl i).step s c))
    (k : IskT lam L Bd aT aL) (vs : List Bits) (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (b : ZKCP.Gen.Batch X Unit) :
    (twinW W S cA r₀ h tl i).reply ((some k, vs), T) (.batch b) =
      ((plainOf (proveWT W cA r₀ h tl k b) vs).runLazy T).map fun y =>
        (.inr (ownPf b y.1.1), ((some k, y.1.2), y.2)) := by
  have e1 : plainOf ((challT W S cA r₀ h tl i).step (some k) (.batch b)) vs =
      (plainOf (proveWT W cA r₀ h tl k b) vs).bind fun q =>
        pure ((Sum.inr (ownPf b q.1), some k), q.2) := plainOf_bind _ _ _
  rw [reply_twin hR, e1]
  refine (congrArg (PMF.map _) (Life2.runLazy_bind_pure (plainOf (proveWT W cA r₀ h tl k b) vs)
    (fun q => ((Sum.inr (ownPf b q.1), some k), q.2)) T)).trans ?_
  exact PMF.map_comp _ _ _

/-- The map of states: the scheme's key, read off the key with tokens and the store. -/
def readOff (pre : Bits)
    (x : (Option (IskT lam L Bd aT aL) × List Bits) × Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    Option (Isk lam L Bd aT aL) × Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) :=
  (x.1.1.map fun k => iskOf pre k x.1.2, x.2)

/-- The invariant: before the setup no key and no string; after it a key whose tokens are in the
store. -/
def InvR : Bool →
    (Option (IskT lam L Bd aT aL) × List Bits) × Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop
  | false, x => x.1 = (none, [])
  | true, x => ∃ k, x.1.1 = some k ∧ KeyIn k x.1.2

/-- a batch that is not one request of the adversary's own: fixed proofs, no program -/
theorem batch_fixed (hR : ∀ s c, RoutedT W ((challT W S cA r₀ h tl i).step s c))
    (k : IskT lam L Bd aT aL) (vs : List Bits) (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (b : ZKCP.Gen.Batch X Unit)
    (e3 : proveWT W cA r₀ h tl k b = .pure (b.map fun _ => ⟨0, 0, none⟩))
    (e4 : (stepD W S cA r₀ h cut i (some (iskOf tl.preE k vs)) (.batch b)).runLazy T =
      PMF.pure ((.inr (ownPf b (b.map fun _ => ⟨0, 0, none⟩)), some (iskOf tl.preE k vs)), T)) :
    ((twinW W S cA r₀ h tl i).reply ((some k, vs), T) (.batch b)).map
        (Prod.map id (readOff tl.preE)) =
      (World.ofOComp (stepD W S cA r₀ h cut i)).reply (readOff tl.preE ((some k, vs), T))
        (.batch b) := by
  rw [reply_twin_batch hR, e3]
  refine (PMF.map_comp _ _ _).trans ?_
  refine Eq.trans (PMF.pure_map _ ((b.map fun _ => (⟨0, 0, none⟩ : RequestProof lam L), vs), T)) ?_
  refine Eq.trans ?_ (congrArg (PMF.map fun q : (GIn (FullKey lam L aT aL) (RequestProof lam L) ×
      Option (Isk lam L Bd aT aL)) × Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) =>
    (q.1.1, (q.1.2, q.2))) e4).symm
  rw [PMF.pure_map]
  rfl

theorem proveWT_long (k : IskT lam L Bd aT aL) (a v : X × Unit × Bool)
    (l : List (X × Unit × Bool)) :
    proveWT W cA r₀ h tl k (a :: v :: l) = .pure ((a :: v :: l).map fun _ => ⟨0, 0, none⟩) := by
  obtain ⟨x, u, own⟩ := a
  cases own <;> rfl

theorem stepD_long (K : Isk lam L Bd aT aL) (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (a v : X × Unit × Bool) (l : List (X × Unit × Bool)) :
    (stepD W S cA r₀ h cut i (some K) (.batch (a :: v :: l))).runLazy T =
      PMF.pure ((.inr (ownPf (a :: v :: l) ((a :: v :: l).map fun _ => ⟨0, 0, none⟩)), some K),
        T) := by
  obtain ⟨x, u, own⟩ := a
  have e : stepD W S cA r₀ h cut i (some K) (.batch ((x, u, own) :: v :: l)) =
      stepC W S cA r₀ h cut i (some K) (.batch ((x, u, own) :: v :: l)) := by
    cases own <;> rfl
  rw [e]
  show PMF.pure ((Sum.inr (ownPf ((x, u, own) :: v :: l)
    ((ZKCP.Gen.Batch.pairs ((x, u, own) :: v :: l)).map fun _ => (⟨0, 0, none⟩ : RequestProof lam L))),
      some K), T) = _
  rw [ZKCP.Gen.Batch.pairs, List.map_map]
  rfl

theorem twin_drop (hS : SameStep W S cA r₀ h tl cut)
    (hR : ∀ s c, RoutedT W ((challT W S cA r₀ h tl i).step s c))
    (ok : ZKCP.Gen.Batch X Unit → Prop)
    (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ) (hA : GAdm ok A false n)
    (T : Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (interact (twinW W S cA r₀ h tl i) A ((none, []), T)).map Prod.fst =
      (interact (World.ofOComp (stepD W S cA r₀ h cut i)) A (none, T)).map Prod.fst := by
  refine DeferRun.lump_gAdm_fst ok (twinW W S cA r₀ h tl i)
    (World.ofOComp (stepD W S cA r₀ h cut i)) (readOff tl.preE) InvR ?_ ?_ ?_ ?_ ?_ ?_ A false n
    ((none, []), T) hA rfl
  · intro f x o q _
    show ((lazyAnswer x.2 o q).map _).map _ = (lazyAnswer x.2 o q).map _
    rw [PMF.map_comp]
    rfl
  · intro f x o q hI y hy
    obtain ⟨z, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    cases f
    · exact hI
    · exact hI
  · rintro ⟨⟨s, vs⟩, T⟩ hI
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (s, vs) = (none, []) from hI)
    have e2 := congrArg (PMF.map fun z : (FullKey lam L aT aL × Isk lam L Bd aT aL) ×
        Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) =>
      ((Sum.inl z.1.1 : GIn (FullKey lam L aT aL) (RequestProof lam L)), (some z.1.2, z.2)))
      (hS.setup i _ Handler.lazy T)
    rw [OComp.interp_lazy, OComp.interp_lazy, PMF.map_comp, PMF.map_comp] at e2
    rw [reply_twin_setup hR]
    refine (PMF.map_comp _ _ _).trans (Eq.trans e2 ?_)
    refine Eq.trans ?_ (congrArg (PMF.map fun q : (GIn (FullKey lam L aT aL) (RequestProof lam L) ×
        Option (Isk lam L Bd aT aL)) × Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) =>
      (q.1.1, (q.1.2, q.2))) (Life2.runLazy_bind_pure (commitW W S cA h i)
        (fun o => ((Sum.inl o.1 : GIn (FullKey lam L aT aL) (RequestProof lam L)), some (cut o.2))) T)).symm
    rw [PMF.map_comp]
    rfl
  · rintro ⟨⟨s, vs⟩, T⟩ hI y hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (s, vs) = (none, []) from hI)
    rw [reply_twin_setup hR] at hy
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    exact ⟨z.1.1.2, rfl, post_runLazy (hS.keyIn i) T z hz⟩
  · rintro ⟨⟨s, vs⟩, T⟩ b _ ⟨k, hk', hk⟩
    obtain rfl : s = some k := hk'
    rcases b with _ | ⟨⟨x, u, own⟩, _ | ⟨v, l⟩⟩
    · exact batch_fixed hR k vs T [] rfl rfl
    · cases own
      · exact batch_fixed hR k vs T [(x, u, false)] rfl rfl
      · cases u
        have e2 := congrArg (PMF.map fun z : List (RequestProof lam L) ×
            Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) =>
          ((Sum.inr (ownPf [(x, (), true)] z.1) : GIn (FullKey lam L aT aL) (RequestProof lam L)),
            (some (iskOf tl.preE k vs), z.2)))
          (hS.sess k vs hk x _ Handler.lazy T)
        rw [OComp.interp_lazy, OComp.interp_lazy, PMF.map_comp, PMF.map_comp] at e2
        rw [reply_twin_batch hR]
        refine (PMF.map_comp _ _ _).trans ?_
        refine Eq.trans (map_congr_support _ fun y hy => ?_) (Eq.trans e2 ?_)
        · show ((Sum.inr (ownPf [(x, (), true)] y.1.1) : GIn (FullKey lam L aT aL) (RequestProof lam L)),
              (some (iskOf tl.preE k y.1.2), y.2)) = (Sum.inr _, (some (iskOf tl.preE k vs), y.2))
          rw [iskOf_prefix hk (post_runLazy (plainOf_grows _ vs) T y hy)]
        · refine Eq.trans ?_ (congrArg (PMF.map fun q : (GIn (FullKey lam L aT aL) (RequestProof lam L) ×
              Option (Isk lam L Bd aT aL)) × Table (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) =>
            (q.1.1, (q.1.2, q.2))) (Life2.runLazy_bind_pure
              (proveW W cA r₀ h (iskOf tl.preE k vs) [(x, ())])
              (fun πs => ((Sum.inr (ownPf [(x, (), true)] πs.val) :
                GIn (FullKey lam L aT aL) (RequestProof lam L)), some (iskOf tl.preE k vs))) T)).symm
          rw [PMF.map_comp]
          rfl
    · exact batch_fixed hR k vs T _ (proveWT_long k _ v l) (stepD_long _ T _ v l)
  · rintro ⟨⟨s, vs⟩, T⟩ b _ ⟨k, hk', hk⟩ y hy
    obtain rfl : s = some k := hk'
    rw [reply_twin_batch hR] at hy
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    exact ⟨k, rfl, hk.mono (post_runLazy (plainOf_grows _ vs) T z hz)⟩

/-! ## The two statements -/

theorem real_twinW (p : Params) (hS : SameStep W S cA r₀ h tl cut)
    (hR : ∀ s c, RoutedT W ((challT W S cA r₀ h tl i).step s c))
    (ok : ZKCP.Gen.Batch X Unit → Prop)
    (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ) (hA : GAdm ok A false n) :
    (interact (realW (argW W S cA r₀ p h) i) A (none, Table.empty _)).map Prod.fst =
      (interact (twinW W S cA r₀ h tl i) A ((none, []), Table.empty _)).map Prod.fst :=
  (real_cut W S cA r₀ p h cut i hS.cutFree A _).trans
    ((cut_drop W S cA r₀ h cut i A none _).trans (twin_drop hS hR ok A n hA _).symm)

theorem realTwin : Spec.realTwin := by
  intro I X lam L Bd aT aL W S cA r₀ p h tl cut i α ok A n hS hG hA
  have hR := (routedTwin I X lam L Bd aT aL W S cA r₀ h tl hG).2.2 i
  rw [real_twinW p hS hR ok A n hA]
  exact DeferRun.viaErased_modeR (challT W S cA r₀ h tl i) (ghostPerm _ _ _ _ W) A none

theorem hopTwin (hW : TokenRules.Spec.withinTwin) : Spec.hopTwin := by
  intro I X lam L Bd aT aL W S cA r₀ p h tl cut bl bf i α ok A t n hS hG hL hT hA
  have hR := (routedTwin I X lam L Bd aT aL W S cA r₀ h tl hG).2.2 i
  exact DeferRun.real_to_modeI (challT W S cA r₀ h tl i) none (ghostPerm _ _ _ _ W) _ _ _ _
    (realW (argW W S cA r₀ p h) i) (none, Table.empty _) A t (n + 1) hT
    (real_twinW p hS hR ok A n hA)
    (hW I X lam L Bd aT aL W S cA r₀ h tl bl bf i true α ok (A.via (ghost W)) n hL
      (DeferRun.gAdm_via ok (ghost W) A false n hA))

/-! ## A small member of SameStep's clause sess -/

/-- At a key without copies the clause sess holds, under every rule and at every store: both sides
draw a place and the strategy's coins and hand out "no proof"; the scheme's prover draws the run's
coins besides and does not read them. -/
theorem sess_noCopies (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (cA : L.OutOfDomainAnswer → List (Dig lam))
    (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (i₀ : I) (vs : List Bits) (x : X)
    (σ : Type) (hd : Handler (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) σ) (s : σ) :
    ((plainOf (proveWT W cA r₀ h tl ⟨i₀, []⟩ [(x, (), true)]) vs).interp hd s).map
        (fun y => (y.1.1, y.2)) =
      ((proveW W cA r₀ h (iskOf tl.preE ⟨i₀, []⟩ vs) [(x, ())]).interp hd s).map
        fun y => (y.1.val, y.2) := by
  show (((OComp.sample h.M fun j => OComp.sample h.kB.n fun _ =>
      OComp.pure ([(⟨j.val, h.nm j.val, none⟩ : RequestProof lam L)], vs)) :
        TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) _).interp hd s).map _ =
    (((OComp.sample h.M fun j => OComp.sample h.kB.n fun _ => OComp.sample h.coB.n fun _ =>
      OComp.pure (⟨[⟨j.val, h.nm j.val, none⟩], rfl⟩ :
        ZKCP.Gen.Slots (RequestProof lam L) [(x, ())])) :
        TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) _).interp hd s).map _
  simp only [OComp.interp_sample, OComp.interp_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]

end OnBytes.HopSide

#print axioms OnBytes.HopSide.cut_drop
#print axioms OnBytes.HopSide.real_twinW
#print axioms OnBytes.HopSide.realTwin
#print axioms OnBytes.HopSide.hopTwin
#print axioms OnBytes.HopSide.sess_noCopies
