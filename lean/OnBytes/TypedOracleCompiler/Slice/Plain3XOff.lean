-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3XOff.lean: the protocol in three stretches with an instance of which one
part stands in no query: from soundness instance by instance to the named set's laws of
OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean.

Instances are pairs (a, s). The interface `LX3` (OnBytes/TypedOracleCompiler/Slice/Plain3X.lean) is taken at
`early := fun x => (x.1, d)`: the first query holds the first part, with a fixed d beside it. The
decision `dec x` sees the whole pair. The state function is `replySt` at the identity, the counts
are ε.
 - `x3Off_rare`: the named set is reached with small probability, IF every count of ε and of the
   second lane is at most the share e, the wiring is lawful, no tree is deeper than 63, the second
   lane obeys the laws of a lane at one slot and does not stand under the tag of Batch;
 - `x3Off_lang`: IF for each instance x the protocol `Plain3 G (dec x)` is round-by-round sound for
   Lg x with the one list of counts ε, the wiring is lawful and no tree is deeper than 63: outside
   the named set, for a string whose external openings the reading keeps and whose run is in the
   trace, UNDER `SeedFirst`: the value that `extS` reads off the trace is not x.2, or Lg x holds of
   the string read.

Main theorems: `x3Off_rare`, `x3Off_lang`.

Not claimed. NO SOUNDNESS IS PROVED. What the heads of BatchClauseOff.lean and Plain3X.lean do not
claim; above all: `SeedFirst` is a hypothesis on the trace, which a maker can break at no cost; no
`extS`, no second lane and no Test T are given; nothing is drawn from the second lane's step event;
nothing speaks of a record, of a key file, or of the program. The compiler under OnBytes/TypedOracleCompiler/ is the
one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3X
import OnBytes.TypedOracleCompiler.Slice.BatchClauseOff

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (replySt below_timesShared_one)
open scoped ENNReal

variable {A Sd : Type} (G : Stretches) (dec : A × Sd → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones) (salt : ℕ) (d : Sd)
  (T : InteractiveOracleProof Unit (oneExternalString (2 ^ G.a) PQ.SgX))
  (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)
  (wT : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → List Bool)
  (pT : (p : OPos T.shape) → List Bool → Option (OSym T.shape p))

/-- What the first query holds of an instance: its first part, with d beside it. -/
abbrev earlyWith (x : A × Sd) : A × Sd := (x.1, d)

/-- The wire at that `early`. -/
abbrev WXo := WX3 G dec K chal o salt (earlyWith d) T embE prjE wT eT pT

/-- The written protocol at that `early`. -/
abbrev ZXo := ZX3 G dec K chal o salt (earlyWith d) T embE prjE wT eT pT

variable (R : Reading (Strings.strung (LX3 G dec (earlyWith d) T)) embE)
  (extS : Tc (WXo G dec K chal o salt d T embE prjE wT eT pT) → List (Dig 256) → Sd)
  (Lg : A × Sd → (oneExternalString (2 ^ G.a) PQ.SgX).Str → Prop) (ε : Err G.sh)
  (ℓ : Lane (WXo G dec K chal o salt d T embE prjE wT eT pT))

/-- The named set at the protocol in three stretches: at the state function `replySt` at the
identity and the counts ε. -/
def x3BadOff : Tc (WXo G dec K chal o salt d T embE prjE wT eT pT) → Prop :=
  batBadOff (ZXo G dec K chal o salt d T embE prjE wT eT pT) R extS d
    (Err.timesShared 1 (RoundSplits.allLocal G.sh) ε) (replySt (Plain3X G dec) ε id Lg) ℓ

/-- The named set is reached with small probability: by an algorithm of at most t queries with
probability at most t εs + 2 (t + 1)² / 2 ^ 256. Asked: every count of ε and of the second lane is
at most εs; no tree is deeper than 63; the wiring is lawful; the second lane does not stand under
the tag of Batch and obeys the laws of a lane at one slot. -/
theorem x3Off_rare (εs : ℝ≥0∞) (hb : Err.Below ε εs) (hs : G.Shallow)
    (hw : (wq3X G dec K chal o).OKG) (hne : Tag.onl ≠ ℓ.t) (oℓ : ℓ.OK 1)
    (bℓ : Err.Below ℓ.ε εs) (β : Type)
    (Alg : TypedOracleComputation 256 (K + 1) (Strings.strung (LX3 G dec (earlyWith d) T)) β) (t : ℕ)
    (hA : Alg.QueryBound t) :
    pr Alg.withTrace.law
        {z | x3BadOff G dec K chal o salt d T embE prjE wT eT pT R extS Lg ε ℓ z.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  have h1 : Err.Below (Err.timesShared 1 (RoundSplits.allLocal G.sh) ε) (((1 : ℕ) : ℝ≥0∞) * εs) :=
    below_timesShared_one le_rfl _ ε εs hb
  rw [Nat.cast_one, one_mul] at h1
  exact batBadOff_rare (ZXo G dec K chal o salt d T embE prjE wT eT pT) R extS d _ _ ℓ εs h1
    (joint_reply_id (ZXo G dec K chal o salt d T embE prjE wT eT pT) Lg ε)
    (ZX3_ok G dec K chal o salt (earlyWith d) T embE prjE wT eT pT hs hw) rfl
    (by generalize ℓ.t = u; cases u <;> rfl) hne oℓ bℓ β Alg t hA

/-- From soundness instance by instance: IF for each instance x the protocol `Plain3 G (dec x)`
is round-by-round sound for Lg x with the one list of counts ε, no tree is deeper than 63 and the
wiring is lawful: outside the named set, under `SeedFirst`, an accepted string whose external
openings R keeps means: the value that `extS` reads off the trace is not the instance's second part,
or the language holds. -/
theorem x3Off_lang (hS : ∀ x, (Plain3 G (dec x)).Sound (fun _ => Lg x) ε) (hs : G.Shallow)
    (hw : (wq3X G dec K chal o).OKG)
    (tr : Tc (WXo G dec K chal o salt d T embE prjE wT eT pT)) (cm : Dig 256) (x : A × Sd)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (Plain3X G dec)))
    (hB : ¬ x3BadOff G dec K chal o salt d T embE prjE wT eT pT R extS Lg ε ℓ tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr ((ZXo G dec K chal o salt d T embE prjE wT eT pT).verifier cm x π) true)
    (hsf : SeedFirst (ZXo G dec K chal o salt d T embE prjE wT eT pT) extS tr cm x π) :
    extS tr [cm] ≠ x.2 ∨
      Lg x (R.at (WXo G dec K chal o salt d T embE prjE wT eT pT) tr cm) :=
  batBadOff_lang (ZXo G dec K chal o salt d T embE prjE wT eT pT) R extS d _ _ ℓ Lg
    (stLawsOwn_reply (ZXo G dec K chal o salt d T embE prjE wT eT pT) Lg ε
      ((plain3X_sound_iff G dec Lg ε).2 hS))
    (ZX3_ok G dec K chal o salt (earlyWith d) T embE prjE wT eT pT hs hw) (fun _ => rfl) rfl tr cm
    x π hB hk hrun hsf

end TypedOracleCompiler.Slice
