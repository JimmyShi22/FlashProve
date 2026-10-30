-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/BoundNoInst.lean: a written protocol that lays NO instance into its queries has a
lane, whatever the interface's round "late" is.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why. The round in whose query the rest of an instance is laid (`late`, Iop/Batch.lean) is one field
of the interface, for the chains of all tags. A proof file has such a round, far down its first
chain. A key file in the same world has no such round: it may be shorter than that, and its rounds
are shared from some round on. So (Snd-B) in the late form at that round is false of it: its first
clause asks that the rounds up to "late" exist and are local. The lemma on one protocol
(`mem_of_accepted_ours`, OnBytes/TypedOracleCompiler/Compile/Batch/SoundOurs.lean) asks that clause only of a
verifier that lays an instance into its queries. A file whose instance stands in the list of outer
roots alone lays none. For such a file (Snd-B) at early = id and late = none is enough.

Main names:
  `instX_none`: a chain without an instance holds none in every round; `instAt_id`;
  `mem_of_sndC_noInst`: `mem_of_sndC` (OnBytes/TypedOracleCompiler/Joined/BoundC.lean) from `SndLaws` at (id, none),
    with no hypothesis on `L.late`;
  `laneForC_noInst`: the lane; `SoundLaneC`: "V has a lane", at a predicate on list and instance;
    `SoundLaneC.mono`: a greater bound on the round errors is weaker;
  `xoutCode`, `ReadBackC.ofCode`: the read-back where the instance stands, by a one-to-one code, in
    the list of outer roots behind its first k places;
  `soundLaneC_noInst_of_snd`: from `BatchInteractiveOracleProof.SndBL N id none`;
  `soundLaneC_noInst_of_sound`: from plain round-by-round soundness, shared rounds paying once for
    each slot; `soundLaneC_noInst_one`: at depth 0 of the tag's request tree: the protocol's own
    errors.

  `SoundLane.toC`, `Sound3C`, `sound3C`: three verifiers with a lane each, under three different
    tags, share one event: a file with an instance in its queries beside files without.

The read-back is that of OnBytes/TypedOracleCompiler/Joined/BoundC.lean: `xout` is handed the list of outer roots.
With no instance in the queries its law reads: at a list that fits the instance x, `xout cms none`
is x. So the list determines the instance, wherever `okX` holds.

Limits: as in OnBytes/TypedOracleCompiler/Joined/Bound.lean and BoundC.lean. What the list of outer roots holds
behind its first two places occurs in the first query, and in the first query of the shared rounds;
that the reading of the external strings looks at the first two places alone is `ExtReads`' matter.
`instX_none` has no caller yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.BoundC
import OnBytes.TypedOracleCompiler.Joined.BoundProto

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Joined Rom
  Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- A chain without an instance holds none in every round. -/
theorem instX_none (L : BatchProtocolWithLeafBody I X) (i : ℕ) : instX L none i = none := by
  unfold instX
  cases L.late with
  | none => rfl
  | some n => by_cases h : n ≤ i <;> simp [h]

/-- Where the first query holds the whole instance, every round holds it. -/
theorem instAt_id {Y : Type} (late : Option ℕ) (x : Y) (i : ℕ) : instAt id late x i = x := by
  unfold instAt
  cases late with
  | none => rfl
  | some n => by_cases h : n ≤ i <;> simp [h]

section Lane
variable {Y : Type} {E : ExtSpec} {okX : List (Dig lam) → Y → Prop}

/-- One protocol that lays no instance into its queries: outside the three events a yes means "in
the language", from the laws of a state function at early = id and late = none. Nothing is asked of
`L.late`. -/
theorem mem_of_sndC_noInst (Z : Written W Y E) (R : ReadBackC Z id okX)
    (hxin : ∀ x, Z.xin x = none) (hOK : Z.wq.OKG) (hloc : Z.Q.loc.IsLocal)
    (hco : Z.Q.ann.Coherent) {Lg : Y → E.Str → Prop} (ε : Err Z.Q.loc.shape)
    (State : E.Str → Y → PTr Z.Q.loc.shape → Bool) (hl : SndLaws Z.Q id none Lg State)
    (extY : Tc W → List (Dig lam) → E.Str) {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (laneJC Z R ε State extY).step tr) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Z.Q) (hC : okX cms x) (hrun : RunsIn tr (Z.verifyLax cms x π) true)
    (hext : ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE
      extY) :
    Lg x (extY tr cms) :=
  mem_of_accepted_oursC Z.t Z.Q Z.wq Z.embS Z.embP Z.xin Z.embE hOK hloc hco (Lg := Lg) State
    R.prjS R.prjS_emb R.prjP R.prjP_emb R.xout extY ε hM hF hS cms x π (fun _ => x)
    (fun i => by rw [R.xout_in cms x i hC, instAt_id]) (fun _ _ hne => absurd (hxin x) hne)
    (fun y hL => hl.start y x hL) (fun y τ m _ h => hl.prover y x τ m h)
    (fun y τ hL h => hl.full y x τ hL h) hrun hext.stable hext.agrees

/-- The lane of a protocol that lays no instance into its queries. -/
theorem laneForC_noInst (Z : Written W Y E) (R : ReadBackC Z id okX)
    (hxin : ∀ x, Z.xin x = none) {N : ℕ} {Lg : Y → E.Str → Prop} {ε : Err Z.Q.loc.shape}
    {εs : ℝ≥0∞} (State : E.Str → Y → PTr Z.Q.loc.shape → Bool)
    (hl : SndLaws Z.Q id none Lg State)
    (hj : ∀ y cms (xs : Fin N → Option (Option X)),
      JointLaw N Z.Q.loc.shape Z.Q.ann ε fun j => ((xs j).bind (R.xout cms)).map (State y))
    (hε : Err.Below ε εs) (hOK : Z.wq.OKG) (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent)
    (extY : Tc W → List (Dig lam) → E.Str)
    (hext : ∀ (tr : Tc W) cms x (π : OneProtocolProof lam Z.Q), okX cms x → ¬ EM tr →
      ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE extY) :
    LaneForC W Z.t N Z.verifyLax okX Lg extY εs (laneJC Z R ε State extY) :=
  ⟨rfl, laneOfC_ok hOK.sh hj, hε, fun tr cms x π hC hM hF hS hrun =>
    mem_of_sndC_noInst Z R hxin hOK hloc hco ε State hl extY hM hF hS cms x π hC hrun
      (hext tr cms x π hC hM)⟩

end Lane

/-! ## A read-back from the list of outer roots -/

section Code
variable {Y : Type} {E : ExtSpec}

open Classical in
/-- The instance whose code stands in the list of outer roots behind the first k places, if there is
one. What the chain's queries hold of an instance is not looked at. It is picked by choice: an
object of the analysis, which no verifier computes. -/
def xoutCode (code : Y → List (Dig lam)) (k : ℕ) (cms : List (Dig lam)) (_ : Option X) : Option Y :=
  if h : ∃ x, cms.drop k = code x then some h.choose else none

/-- A one-to-one code is read back. -/
theorem xoutCode_eq {code : Y → List (Dig lam)} (hinj : Function.Injective code) {k : ℕ}
    {cms : List (Dig lam)} {x : Y} (h : cms.drop k = code x) (xo : Option X) :
    xoutCode code k cms xo = some x := by
  have hex : ∃ x, cms.drop k = code x := ⟨x, h⟩
  unfold xoutCode
  rw [dif_pos hex]
  exact congrArg some (hinj (hex.choose_spec.symm.trans h))

/-- The read-back of a protocol whose instance stands, by a one-to-one code, in the list of outer
roots behind the first k places: `okX cms x` says just that. -/
def ReadBackC.ofCode (Z : Written W Y E)
    (prjS : (p : OPos Z.Q.loc.shape) → Body L → Option (OSym Z.Q.loc.shape p))
    (prjP : PlainPart (shapeOf L Z.t) (annOf L Z.t) → Option (PlainPart Z.Q.loc.shape Z.Q.ann))
    (hS : ∀ p a, prjS p (Z.embS p a) = some a) (hP : ∀ z, prjP (Z.embP z) = some z)
    (code : Y → List (Dig lam)) (hinj : Function.Injective code) (k : ℕ) :
    ReadBackC Z id fun cms x => cms.drop k = code x where
  prjS := prjS
  prjP := prjP
  xout := xoutCode code k
  prjS_emb := hS
  prjP_emb := hP
  xout_in := fun _ x i h => by rw [xoutCode_eq hinj h, instAt_id]

end Code

/-- **A compiled verifier V has a lane**, at the calls with `okX cms x`: `SoundLane`
(OnBytes/TypedOracleCompiler/Joined/BoundFiles.lean) with a predicate on the list of outer roots and the instance.
-/
def SoundLaneC (W : QueryLayout lam L) (t : Tag) {Y P : Type} {E : ExtSpec}
    (V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool) (okX : List (Dig lam) → Y → Prop)
    (Lg : Y → E.Str → Prop) (extY : Tc W → List (Dig lam) → E.Str) (εs : ℝ≥0∞) : Prop :=
  ∃ (ℓ : Lane W) (N : ℕ), N = 2 ^ W.dReq t ∧ LaneForC W t N V okX Lg extY εs ℓ

/-- A greater bound on the round errors is weaker. -/
theorem SoundLaneC.mono {t : Tag} {Y P : Type} {E : ExtSpec}
    {V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool} {okX : List (Dig lam) → Y → Prop}
    {Lg : Y → E.Str → Prop} {extY : Tc W → List (Dig lam) → E.Str} {εs εs' : ℝ≥0∞}
    (h : SoundLaneC W t V okX Lg extY εs) (hε : εs ≤ εs') :
    SoundLaneC W t V okX Lg extY εs' := by
  obtain ⟨ℓ, N, hN, hl⟩ := h
  exact ⟨ℓ, N, hN, hl.tag, hl.ok, Err.Below.mono_bound hε hl.below, hl.yes⟩

section File
variable {Y : Type} {E : ExtSpec} {okX : List (Dig lam) → Y → Prop} (Z : Written W Y E)
  (R : ReadBackC Z id okX) (hxin : ∀ x, Z.xin x = none) {Lg : Y → E.Str → Prop}
  {ε : Err Z.Q.loc.shape} {εs : ℝ≥0∞} (hOK : Z.wq.OKG) (hloc : Z.Q.loc.IsLocal)
  (hco : Z.Q.ann.Coherent) (extY : Tc W → List (Dig lam) → E.Str)
  (hext : ∀ (tr : Tc W) cms x (π : OneProtocolProof lam Z.Q), okX cms x → ¬ EM tr →
    ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE extY)
include R hxin hOK hloc hco hext

/-- From (Snd-B) at early = id and late = none, whatever `L.late` is. -/
theorem soundLaneC_noInst_of_snd (hsnd : Z.Q.SndBL (2 ^ W.dReq Z.t) id none Lg ε)
    (hε : Err.Below ε εs) : SoundLaneC W Z.t Z.verifyLax okX Lg extY εs := by
  obtain ⟨h0, State, h1, h2, hs, h3, h4⟩ := hsnd
  exact ⟨_, _, rfl, laneForC_noInst Z R hxin State ⟨h0, h1, h2, hs, h3⟩
    (fun y cms xs => h4 y fun j => (xs j).bind (R.xout cms)) hε hOK hloc hco extY hext⟩

/-- From plain round-by-round soundness: a shared round pays once for each slot. -/
theorem soundLaneC_noInst_of_sound (hsnd : Z.Q.loc.Sound Lg ε)
    (hε : Err.Below (Err.timesShared (2 ^ W.dReq Z.t) Z.Q.ann ε) εs) :
    SoundLaneC W Z.t Z.verifyLax okX Lg extY εs :=
  soundLaneC_noInst_of_snd Z R hxin hOK hloc hco extY hext
    (sndBL_of_sound Z.Q.loc Z.Q.ann (2 ^ W.dReq Z.t) hsnd) hε

/-- **One slot, no instance in the queries**: at a tag whose request tree has depth 0, from plain
round-by-round soundness with the protocol's own errors, whatever `L.late` is. -/
theorem soundLaneC_noInst_one (hsnd : Z.Q.loc.Sound Lg ε) (h0 : W.dReq Z.t = 0)
    (hε : Err.Below ε εs) : SoundLaneC W Z.t Z.verifyLax okX Lg extY εs :=
  soundLaneC_noInst_of_sound Z R hxin hOK hloc hco extY hext hsnd
    (by rw [h0, pow_zero, timesShared_one]; exact hε)

end File

/-! ## Three verifiers together -/

section Three
variable {Y₁ Y₂ Y₃ P₁ P₂ P₃ : Type} {E₁ E₂ E₃ : ExtSpec}

/-- `SoundLane` is `SoundLaneC` at a predicate that does not look at the instance. -/
theorem SoundLane.toC {t : Tag} {V : List (Dig lam) → Y₁ → P₁ → TypedOracleComputation lam W.K L Bool}
    {okC : List (Dig lam) → Prop} {Lg : Y₁ → E₁.Str → Prop}
    {extY : Tc W → List (Dig lam) → E₁.Str} {εs : ℝ≥0∞} (h : SoundLane W t V okC Lg extY εs) :
    SoundLaneC W t V (fun cms _ => okC cms) Lg extY εs := by
  obtain ⟨ℓ, N, hN, hl⟩ := h
  exact ⟨ℓ, N, hN, hl.toC⟩

/-- `Sound3` (OnBytes/TypedOracleCompiler/Joined/BoundFiles.lean) with predicates on the list of outer roots and the
instance. The three predicates are free letters: whoever states a theorem pins them to the calls of
the verifier that runs. -/
def Sound3C (W : QueryLayout lam L) (V₁ : List (Dig lam) → Y₁ → P₁ → TypedOracleComputation lam W.K L Bool)
    (V₂ : List (Dig lam) → Y₂ → P₂ → TypedOracleComputation lam W.K L Bool)
    (V₃ : List (Dig lam) → Y₃ → P₃ → TypedOracleComputation lam W.K L Bool) (ok₁ : List (Dig lam) → Y₁ → Prop)
    (ok₂ : List (Dig lam) → Y₂ → Prop) (ok₃ : List (Dig lam) → Y₃ → Prop)
    (Lg₁ : Y₁ → E₁.Str → Prop) (Lg₂ : Y₂ → E₂.Str → Prop) (Lg₃ : Y₃ → E₃.Str → Prop)
    (ext₁ : Tc W → List (Dig lam) → E₁.Str) (ext₂ : Tc W → List (Dig lam) → E₂.Str)
    (ext₃ : Tc W → List (Dig lam) → E₃.Str) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (n : ℕ), A.QueryBound n →
      pr A.withTrace.law {o | Bad o.2} ≤ _root_.Compile.Joined.bound n εs lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cms x π, ok₁ cms x → ¬ Bad tr → RunsIn tr (V₁ cms x π) true → Lg₁ x (ext₁ tr cms)) ∧
    (∀ tr cms x π, ok₂ cms x → ¬ Bad tr → RunsIn tr (V₂ cms x π) true → Lg₂ x (ext₂ tr cms)) ∧
    ∀ tr cms x π, ok₃ cms x → ¬ Bad tr → RunsIn tr (V₃ cms x π) true → Lg₃ x (ext₃ tr cms)

/-- Three verifiers with a lane each, under three different tags: one event, the hash term paid
once, εs once for each query. -/
theorem sound3C {t₁ t₂ t₃ : Tag} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    {V₁ : List (Dig lam) → Y₁ → P₁ → TypedOracleComputation lam W.K L Bool}
    {V₂ : List (Dig lam) → Y₂ → P₂ → TypedOracleComputation lam W.K L Bool}
    {V₃ : List (Dig lam) → Y₃ → P₃ → TypedOracleComputation lam W.K L Bool} {ok₁ : List (Dig lam) → Y₁ → Prop}
    {ok₂ : List (Dig lam) → Y₂ → Prop} {ok₃ : List (Dig lam) → Y₃ → Prop}
    {Lg₁ : Y₁ → E₁.Str → Prop} {Lg₂ : Y₂ → E₂.Str → Prop} {Lg₃ : Y₃ → E₃.Str → Prop}
    {ext₁ : Tc W → List (Dig lam) → E₁.Str} {ext₂ : Tc W → List (Dig lam) → E₂.Str}
    {ext₃ : Tc W → List (Dig lam) → E₃.Str} {εs : ℝ≥0∞}
    (l₁ : SoundLaneC W t₁ V₁ ok₁ Lg₁ ext₁ εs) (l₂ : SoundLaneC W t₂ V₂ ok₂ Lg₂ ext₂ εs)
    (l₃ : SoundLaneC W t₃ V₃ ok₃ Lg₃ ext₃ εs) :
    Sound3C W V₁ V₂ V₃ ok₁ ok₂ ok₃ Lg₁ Lg₂ Lg₃ ext₁ ext₂ ext₃ εs := by
  obtain ⟨a, N₁, hN₁, ha⟩ := l₁
  obtain ⟨b, N₂, hN₂, hb⟩ := l₂
  obtain ⟨c, N₃, hN₃, hc⟩ := l₃
  have hall : ∀ ℓ ∈ [a, b, c], ℓ.OK (2 ^ W.dReq ℓ.t) ∧ Err.Below ℓ.ε εs := by
    intro ℓ hℓ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact ⟨by rw [ha.tag, ← hN₁]; exact ha.ok, ha.below⟩
    · exact ⟨by rw [hb.tag, ← hN₂]; exact hb.ok, hb.below⟩
    · exact ⟨by rw [hc.tag, ← hN₃]; exact hc.ok, hc.below⟩
  have htag : [a, b, c].Pairwise fun x y => x.t ≠ y.t := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    exact ⟨⟨by rw [ha.tag, hb.tag]; exact h12, by rw [ha.tag, hc.tag]; exact h13⟩,
      by rw [hb.tag, hc.tag]; exact h23⟩
  refine ⟨BadL [a, b, c],
    badL_rare_of_tags htag (fun ℓ h => (hall ℓ h).1) fun ℓ h => (hall ℓ h).2,
    fun tr tr' => badL_mono tr tr', fun tr cms x π hC hB hr => ha.mem (by simp) hB hC hr,
    fun tr cms x π hC hB hr => hb.mem (by simp) hB hC hr,
    fun tr cms x π hC hB hr => hc.mem (by simp) hB hC hr⟩

end Three

end TypedOracleCompiler.Joined
