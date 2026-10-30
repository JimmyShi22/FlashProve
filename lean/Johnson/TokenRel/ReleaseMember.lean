-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/ReleaseMember.lean: A MEMBER FOR THE RULE OF RELEASE IN ITS LIVE CASE: a run whose
hashing has a value and is not stopped, on a table's tree that has leaves.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

The rule of release (Spec.release, Johnson/TokenRules/ReleaseSpec.lean) speaks of a run whose
hashing has a value and which no test stops. That its premises can be met together there is shown at
a small protocol:
  readsOnly E rd, wireOnly   a protocol WITHOUT ROUNDS whose verifier reads the positions rd of the
                  external strings, and its wire. Its chain is empty, so its hashing always has a
                  value (hash_live).
  release_live    From the first state: one table is made (tabT); then a run of that protocol on the
                  table's tree, never stopped. All premises of the rule hold; its conclusion gives:
                  a string is handed out, and AFTER THE RUN THE INPUT OF EACH LEAF THAT IS READ HAS
                  AN ENTRY IN THE TABLE. This of every outcome of the two runs.
  release_live_member   There are such outcomes.
Limits. The member has no round: no tree of the run's own, no Fiat-Shamir query. A member with
rounds is not typed.

-/
import Johnson.TokenRel.Holds

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

/-- A protocol without rounds whose verifier reads the positions rd of the external strings. -/
abbrev readsOnly (E : ExtSpec) (rd : Finset E.Pos) : BatchInteractiveOracleProof Unit E :=
  ⟨⟨[], (fun p => nomatch p), fun _ _ => rd, fun _ _ _ => ∅, fun _ _ _ => true⟩, PUnit.unit⟩

/-- its wire -/
def wireOnly (lam K : ℕ) (E : ExtSpec) (rd : Finset E.Pos) (we : WireE E) :
    ProtocolQueryLayout lam K (readsOnly E rd) := ⟨(), we, (fun p => nomatch p), 0, 0⟩

section Generic
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The hashing of a run of that protocol always has a value. -/
theorem hash_live {Rl : Rules (typedOracleFamily lam K L)} (t : Tag) (E : ExtSpec) (rd : Finset E.Pos)
    (we : WireE E) (embS : (p : OPos (readsOnly E rd).loc.shape) →
      OSym (readsOnly E rd).loc.shape p → Body L)
    (embP : PlainPart (readsOnly E rd).loc.shape (readsOnly E rd).ann → PlainPart (shapeOf L t) (annOf L t))
    (xin : Unit → Option X) (cms : List (Dig lam)) (ln : RunLen lam L)
    (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ) (d : DSt (typedOracleFamily lam K L)) :
    SafeO Rl (hashT t (readsOnly E rd) (wireOnly lam K E rd we) embS embP xin cms () () ln pre cap)
      d fun a _ => ∃ z, a.2.2 = Res.ok z := by
  unfold hashT
  intro u
  refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_drawD ln _))
  rintro cd _ ⟨rfl, _⟩
  exact ⟨_, rfl⟩

end Generic

/-- **The live case**: see the head. -/
theorem release_live {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
    (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (t : Tag) (E : ExtSpec) (rd : Finset E.Pos) (we : WireE E)
    (hwe : ∀ p, we.leaf p < 2 ^ W.depth) (hall : ∀ p, p ∈ we.all)
    (embS : (p : OPos (readsOnly E rd).loc.shape) → OSym (readsOnly E rd).loc.shape p →
      Body (typedOracleCarrier L Bd aT aL))
    (embP : PlainPart (readsOnly E rd).loc.shape (readsOnly E rd).ann →
      PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t))
    (xin : Unit → Option L.XC) (cms : List (Dig lam)) (y : E.Str)
    (ln : RunLen lam (typedOracleCarrier L Bd aT aL)) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ) :
    ∀ v ∈ ((tabT W S h tl b₀ i r).run true (DSt.init _)).support,
    ∀ u ∈ ((hashT t (readsOnly E rd) (wireOnly lam W.K E rd we) embS embP xin cms () () ln pre
      cap).run true v.2).support,
    ∃ π D₂, (endC (readsOnly E rd) (wireOnly lam W.K E rd we) () y (fun _ => v.1.tree) tl.preE pre
        (fun _ => false) u.1).run true u.2 = PMF.pure (some π, D₂) ∧
      ∀ p ∈ rd, D₂.table OracleName.leaf ((v.1.tree.toK u.2.val tl.preE).inp (we.leaf p)) ≠ none := by
  intro v hv u hu
  obtain ⟨hH, hlen⟩ := holdsTab I X lam L Bd aT aL W S h tl 0 0 b₀ i r _ [] (Nat.zero_le _)
    (holdsStart _ _ _ _ _ _ _) v hv
  obtain ⟨z, hz⟩ := safeRunO _ _ _ _ _ _ _ true
    (hash_live (Rl := rulesT W.K (typedOracleCarrier L Bd aT aL) lam 0 0 (seedPts W S)) t E rd we embS embP
      xin cms ln pre cap v.2) u hu
  have hT := hH.2.2 v.1.tree List.mem_cons_self
  obtain ⟨D₂, hrun, htab, _⟩ := release _ _ lam W.K (typedOracleCarrier L Bd aT aL) 0 0 (seedPts W S) t Unit E
    (readsOnly E rd) (wireOnly lam W.K E rd we) embS embP xin cms () y (fun _ => v.1.tree) tl.preE
    () ln pre cap (fun _ => false) v.2 u.2 u.1 z (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (fun p => by rw [hlen]; exact hwe p) hH.1 hH.2.1 (fun _ => hT.1) (fun _ => hT.2) hu hz rfl
  refine ⟨_, D₂, hrun, fun p hp => ?_⟩
  rw [htab]
  exact lay_mem_ne_none _ _ (entryK (v.1.tree.toK u.2.val tl.preE) (we.leaf p))
    (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hall p, by
      simp only [decide_eq_true_eq]
      exact hp⟩, rfl⟩)

/-- **There is such a run**: a law has an outcome, so the statement above is about something. -/
theorem release_live_member {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
    (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (t : Tag) (E : ExtSpec) (rd : Finset E.Pos) (we : WireE E)
    (hwe : ∀ p, we.leaf p < 2 ^ W.depth) (hall : ∀ p, p ∈ we.all)
    (embS : (p : OPos (readsOnly E rd).loc.shape) → OSym (readsOnly E rd).loc.shape p →
      Body (typedOracleCarrier L Bd aT aL))
    (embP : PlainPart (readsOnly E rd).loc.shape (readsOnly E rd).ann →
      PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t))
    (xin : Unit → Option L.XC) (cms : List (Dig lam)) (y : E.Str)
    (ln : RunLen lam (typedOracleCarrier L Bd aT aL)) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ) :
    ∃ v ∈ ((tabT W S h tl b₀ i r).run true (DSt.init _)).support,
    ∃ u ∈ ((hashT t (readsOnly E rd) (wireOnly lam W.K E rd we) embS embP xin cms () () ln pre
      cap).run true v.2).support,
    ∃ π D₂, (endC (readsOnly E rd) (wireOnly lam W.K E rd we) () y (fun _ => v.1.tree) tl.preE pre
        (fun _ => false) u.1).run true u.2 = PMF.pure (some π, D₂) ∧
      ∀ p ∈ rd, D₂.table OracleName.leaf ((v.1.tree.toK u.2.val tl.preE).inp (we.leaf p)) ≠ none := by
  obtain ⟨v, hv⟩ := ((tabT W S h tl b₀ i r).run true (DSt.init _)).support_nonempty
  obtain ⟨u, hu⟩ := ((hashT t (readsOnly E rd) (wireOnly lam W.K E rd we) embS embP xin cms () ()
    ln pre cap).run true v.2).support_nonempty
  exact ⟨v, hv, u, hu, release_live W S h tl b₀ i r t E rd we hwe hall embS embP xin cms y ln pre
    cap v hv u hu⟩

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.release_live
#print axioms OnBytes.TokenRel.release_live_member
