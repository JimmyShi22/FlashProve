-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingFlags.lean: what the three chains of a file have as their values under fixed
oracle functions has as many roots as trees, and the component of each round's kind.

OnBytes/Maker/TypingHolds.lean and OnBytes/Maker/TypingOpened.lean take, of what the chains have
yielded, two properties: in each component that is sent there are as many roots as trees
(`RtFlagsAll`, OnBytes/TypedOracleCompiler/Joined/Clauses.lean), and the component of each round's kind is sent
(`SentK`, OnBytes/Maker/TypingTr.lean). Both are laws of a run in a trace. The closing statements of
OnBytes/TypedOracleCompiler/Joined/K/ speak of values under fixed oracle functions g: "(run₁ ..).det g = some a".
This file goes from such values to the two properties: a chain has no coins, so it runs, in some
trace, to its value under g (OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean, `runsIn_log'`).

  `flags_of_det`     one chain: from a value of `recomputeChain` under g.
  `flags₁_of_det`, `flags₂_of_det`, `flags₃_of_det`
                     the three chains of a file, each at its own rounds.
  `flags_glue_of_det`
                     the two properties over the whole file, at the three values laid in a row.

Not claimed. That a chain has a value. Nothing on soundness.


-/
import OnBytes.Maker.TypingTr
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Tag)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **One chain.** -/
theorem flags_of_det (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (i : ℕ) (ph : Phase lam)
    (rts : List (Dig lam)) (pls : Plains s) (z : Out lam s)
    (h : (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls).det g = some z) :
    RtFlagsAll s A W z.2.1 ∧ SentK s A z.2.1 := by
  obtain ⟨tr, -, hr⟩ := runsIn_log' g (noCoin_chainB t cms x salt rtreq s A W embP i ph rts pls) h
  exact ⟨rtFlags_of_runsIn s A W embP i ph z.2.2 rts pls z.1 z.2.1 hr,
    sentK_of_runsIn s A W embP i ph z.2.2 rts pls z.1 z.2.1 hr⟩

section File
variable {Y : Type} {E : ExtSpec} {G : Chains} {D : Desc G Y E} {wq : ProtocolQueryLayout lam K D.batch}
  {π : OneProtocolProof lam D.batch} {a : Out lam G.c₁} {b : Out lam G.c₂} {e : Out lam G.c₃}
  (g : Fam (typedOracleFamily lam K L)) {t : Tag}
  {embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Y → Option X}
  {cms : List (Dig lam)} {x : Y}

theorem flags₁_of_det (h : (run₁ t D wq embP xin cms x π).det g = some a) :
    RtFlagsAll G.c₁ G.A₁ (wire₁ wq) a.2.1 ∧ SentK G.c₁ G.A₁ a.2.1 :=
  flags_of_det g _ _ _ _ _ _ _ _ _ _ _ _ _ a h

theorem flags₂_of_det (h : (run₂ t D wq embP xin cms x π a).det g = some b) :
    RtFlagsAll G.c₂ G.A₂ (wire₂ wq) b.2.1 ∧ SentK G.c₂ G.A₂ b.2.1 :=
  flags_of_det g _ _ _ _ _ _ _ _ _ _ _ _ _ b h

theorem flags₃_of_det (h : (run₃ t D wq embP xin cms x π a b).det g = some e) :
    RtFlagsAll G.c₃ G.A₃ (wire₃ wq) e.2.1 ∧ SentK G.c₃ G.A₃ e.2.1 :=
  flags_of_det g _ _ _ _ _ _ _ _ _ _ _ _ _ e h

/-- The two properties chain by chain give them over the whole, at the three values in a row. -/
theorem flags_glue (f₁ : RtFlagsAll G.c₁ G.A₁ (wire₁ wq) a.2.1 ∧ SentK G.c₁ G.A₁ a.2.1)
    (f₂ : RtFlagsAll G.c₂ G.A₂ (wire₂ wq) b.2.1 ∧ SentK G.c₂ G.A₂ b.2.1)
    (f₃ : RtFlagsAll G.c₃ G.A₃ (wire₃ wq) e.2.1 ∧ SentK G.c₃ G.A₃ e.2.1) :
    RtFlagsAll G.sh G.ann wq.sh (glue a b e).2.1 ∧ SentK G.sh G.ann (glue a b e).2.1 := by
  constructor
  · show RtFlagsAll (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh
      (RT.app a.2.1 (RT.app b.2.1 e.2.1))
    rw [rtFlags_app, rtFlags_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
    exact ⟨f₁.1, f₂.1, f₃.1⟩
  · show SentK (G.c₁ ++ (G.c₂ ++ G.c₃)) (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃))
      (RT.app a.2.1 (RT.app b.2.1 e.2.1))
    rw [sentK_app, sentK_app, RT.fst_app, RT.snd_app, RT.fst_app, RT.snd_app]
    exact ⟨f₁.2, f₂.2, f₃.2⟩

/-- **Over the whole file, from the three values under g.** -/
theorem flags_glue_of_det (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e) :
    RtFlagsAll G.sh G.ann wq.sh (glue a b e).2.1 ∧ SentK G.sh G.ann (glue a b e).2.1 :=
  flags_glue (flags₁_of_det g h₁) (flags₂_of_det g h₂) (flags₃_of_det g h₃)

end File

end OnBytes.Maker
