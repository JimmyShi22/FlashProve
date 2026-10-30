-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/DrawsOfLine.lean: what OnBytes/Maker/AcceptAtA.lean asks of the verifier's messages
(`DrawsHeldA`), at the values that the three chains of a file have under fixed oracle functions,
from three yeses of the strict reader and laws on these functions.

OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean computes the three chains' values under g
(`whole_line_read`), under the hypotheses of its record `ReadL`: the draws of the first and of the
third chain are those read, the second chain's but for the last digest, and the proofs of work pass.
It speaks of rounds' data without stored tables, in the letters of OnBytes/TypedOracleCompiler/Run/. The rounds of a
whole file are these by unfolding (OnBytes/Maker/TreesLine.lean, LineAt.lean). This file carries the
outcome over.

Main theorems.
  `take_dropLast`: a list without its last member, as its first members.
  `drawsHeldA_of_line`: `DrawsHeldA` at three values laid in a row, from the six clauses in which
    `whole_line_read` ends. n: the number of the first chain's rounds before the seal.
  `rounds_length`: a chain that the strict reader has read has as many rounds as its description.
  `held_of_readL`: from `ReadL` at a whole file's description and wire record, and at the three
    chains of a reading r: the three runs' values, the whole chain's value, the slot's value, and
    `DrawsHeldA`.
  `draws_of_readL`: `DrawsHeldA` at whatever values the three chains have under g.
  `sealRead_of_seal`, `sealAt_of_readL`: g answers the query that holds the chaining value in which
    the first chain ends with that chain's seal as read.

Beside `ReadL`, `held_of_readL`, `draws_of_readL` and `sealAt_of_readL` take: that the answers of O
have 32 bytes; that one kit of verifier messages fits the three plans' fields (`KitFits`);
`sealAt_of_readL` also the first chain's seal as read.

THE TWO SEALS. Nothing in `DrawsHeldA` ties either seal's value. The first: `sealAt_of_readL`. The
second: its value enters in the field `s3` of `ReadL` alone; no statement here gives the second seal
of the typed run.

What is not claimed. `ReadL`: its laws on g above all. Nothing on soundness.


-/
import OnBytes.Maker.DrawsOfRuns
import OnBytes.Maker.SameButSeal
import OnBytes.Maker.LineAt
import OnBytes.TypedOracleCompiler.Joined.K.RunsLineRead

set_option autoImplicit false

namespace OnBytes.Maker

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.TwoLaws (LAlike DrawnAlike)

/-- A list without its last member is its first members. -/
theorem take_dropLast {α : Type} (l : List α) (n : ℕ) (h : n + 1 = l.length) :
    l.take n = l.dropLast := by
  rw [List.dropLast_eq_take]
  congr 1
  omega

/-- **What is asked of the verifier's messages, from the six clauses in which `whole_line_read`
ends.** -/
theorem drawsHeldA_of_line (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (r : Proof.TailRead) (n : ℕ) (hn : n + 1 = r.first.out.rounds.toList.length)
    (a : Out 256 (chainsOf C D tF tJ t3).c₁) (b : Out 256 (chainsOf C D tF tJ t3).c₂)
    (e : Out 256 (chainsOf C D tF tJ t3).c₃)
    (d₁ : TypedOracleCompiler.Run.PQ.drawnSL C (toRDs D.ds₁) a.1.2 =
      (r.first.out.rounds.toList.take n).map (·.drawn))
    (d₂ : TypedOracleCompiler.Run.PQ.SameButSeal (TypedOracleCompiler.Run.PQ.drawnSL C (toRDs D.ds₂) b.1.2)
      (r.shared.out.rounds.toList.map (·.drawn)))
    (d₃ : TypedOracleCompiler.Run.PQ.drawnSL C (toRDs D.ds₃) e.1.2 = r.second.out.rounds.toList.map (·.drawn))
    (w₁ : TypedOracleCompiler.Run.PQ.passSL C (toRDs D.ds₁) a.1.2 = true)
    (w₂ : TypedOracleCompiler.Run.PQ.passSL C (toRDs D.ds₂) b.1.2 = true)
    (w₃ : TypedOracleCompiler.Run.PQ.passSL C (toRDs D.ds₃) e.1.2 = true) :
    DrawsHeldA C D tF tJ t3 r (glue a b e).1 := by
  rw [take_dropLast _ n hn] at d₁
  refine drawsHeldA_of_runs C D tF tJ t3 r a b e ?_ (lAlike_of_sameButSeal _ _ d₂) ?_ w₁ w₂ w₃
  · show LAlike DrawnAlike _ (TypedOracleCompiler.Run.PQ.drawnSL C (toRDs D.ds₁) a.1.2)
    rw [d₁]
    exact LAlike.refl DrawnAlike.refl _
  · show LAlike DrawnAlike _ (TypedOracleCompiler.Run.PQ.drawnSL C (toRDs D.ds₃) e.1.2)
    rw [d₃]
    exact LAlike.refl DrawnAlike.refl _

/-- A chain that the strict reader has read has as many rounds as its description. -/
theorem rounds_length (h : HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    o.rounds.toList.length = S.base.rounds.length := by
  obtain ⟨hok, H⟩ := readX_read h S seen b i o j e
  rw [← H.length_eq, List.length_zip, stored_length hok, Nat.min_self]

/-- **From `ReadL` at a whole file's description and wire record, at the three chains of a reading
r.** a, b, e are fixed by the three equations on the runs. -/
theorem held_of_readL {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF)
    (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (g : Fam (typedOracleFamily 256 (K + 1) L))
    (O : ByteArray → ByteArray) (rest : List (Dig 256)) (S₁ S₂ S₃ : Fmt.SpecX)
    (r : Proof.TailRead) (rs₁ : List Fmt.Round) (rS : Fmt.Round) (hO : ∀ s, (O s).size = 32)
    (hkit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field C K chal)
    (hkit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field C K chal)
    (hkit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field C K chal)
    (A : ReadL (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs D.ds₁) (ds₂ := toRDs D.ds₂)
      (ds₃ := toRDs D.ds₃) (D := wholeDesc C D tF tJ t3 silent run)
      (wqWhole C K chal D tF tJ t3 silent run) embP xin cms x π g O chal
      (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _) (wireSilent (K + 1) T3 t3 _)
      [] [] rest S₁ S₂ S₃ r.first.out r.shared.out r.second.out rs₁ rS) :
    ∃ (a : Out 256 (chainsOf C D tF tJ t3).c₁) (b : Out 256 (chainsOf C D tF tJ t3).c₂)
      (e : Out 256 (chainsOf C D tF tJ t3).c₃),
      (run₁ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP xin
        cms x π).det g = some a ∧
      (run₂ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP xin
        cms x π a).det g = some b ∧
      (run₃ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP xin
        cms x π a b).det g = some e ∧
      (recomputeChainOfProof t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embP xin cms x π).det g = some (glue a b e) ∧
      (glue a b e).2.2.slotVal = some (bytesToDig (TypedOracleCompiler.Run.PQ.sealRead r.first.out)) ∧
      DrawsHeldA C D tF tJ t3 r (glue a b e).1 := by
  obtain ⟨a, b, e, v', E1, E2, E3, EW, hph, -, -, -, d1, d2, d3, p1, p2, p3⟩ :=
    whole_line_read hO hkit₁ hkit₂ hkit₃ A
  obtain ⟨sn, bb, i, j, e₁⟩ := A.read₁
  have hn : rs₁.length + 1 = r.first.out.rounds.toList.length := by
    rw [rounds_length _ S₁ sn bb i _ j e₁, A.rounds₁, List.length_append]
    rfl
  refine ⟨a, b, e, E1, E2, E3, EW, ?_, drawsHeldA_of_line C D tF tJ t3 r rs₁.length hn a b e d1 d2
    d3 p1 p2 p3⟩
  rw [hph]
  rfl

/-- **The draws, at whatever values the three chains have under g**: the form in which
Johnson/Maker/LeftAtKey.lean owes them. -/
theorem draws_of_readL {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF)
    (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (g : Fam (typedOracleFamily 256 (K + 1) L))
    (O : ByteArray → ByteArray) (rest : List (Dig 256)) (S₁ S₂ S₃ : Fmt.SpecX)
    (r : Proof.TailRead) (rs₁ : List Fmt.Round) (rS : Fmt.Round) (hO : ∀ s, (O s).size = 32)
    (hkit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field C K chal)
    (hkit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field C K chal)
    (hkit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field C K chal)
    (A : ReadL (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs D.ds₁) (ds₂ := toRDs D.ds₂)
      (ds₃ := toRDs D.ds₃) (D := wholeDesc C D tF tJ t3 silent run)
      (wqWhole C K chal D tF tJ t3 silent run) embP xin cms x π g O chal
      (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _) (wireSilent (K + 1) T3 t3 _)
      [] [] rest S₁ S₂ S₃ r.first.out r.shared.out r.second.out rs₁ rS)
    (a : Out 256 (chainsOf C D tF tJ t3).c₁) (b : Out 256 (chainsOf C D tF tJ t3).c₂)
    (e : Out 256 (chainsOf C D tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP
      xin
      cms x π).det g = some a)
    (h₂ : (run₂ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP
      xin
      cms x π a).det g = some b)
    (h₃ : (run₃ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP
      xin
      cms x π a b).det g = some e) :
    DrawsHeldA C D tF tJ t3 r (glue a b e).1 := by
  obtain ⟨a', b', e', k₁, k₂, k₃, -, -, H⟩ := held_of_readL C K chal D tF tJ t3 silent run embP xin
    cms x π g O rest S₁ S₂ S₃ r rs₁ rS hO hkit₁ hkit₂ hkit₃ A
  obtain ⟨rfl, rfl, rfl⟩ := runs_unique h₁ h₂ h₃ k₁ k₂ k₃
  exact H

/-- The seal of a chain as read, in two spellings. -/
theorem sealRead_of_seal (c : ChainRead) (s : ByteArray) (h : c.seal = some s) :
    TypedOracleCompiler.Run.PQ.sealRead c.out = s := by
  unfold ChainRead.seal at h
  unfold TypedOracleCompiler.Run.PQ.sealRead
  rw [← Array.getLast?_toList] at h
  rw [h]
  rfl

/-- **g answers the query that holds the chaining value in which the first chain ends with that
chain's seal as read**: the row `sealAt` of OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean. -/
theorem sealAt_of_readL {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF)
    (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (g : Fam (typedOracleFamily 256 (K + 1) L))
    (O : ByteArray → ByteArray) (rest : List (Dig 256)) (S₁ S₂ S₃ : Fmt.SpecX)
    (r : Proof.TailRead) (rs₁ : List Fmt.Round) (rS : Fmt.Round) (hO : ∀ s, (O s).size = 32)
    (hkit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field C K chal)
    (hkit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field C K chal)
    (hkit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field C K chal)
    (A : ReadL (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs D.ds₁) (ds₂ := toRDs D.ds₂)
      (ds₃ := toRDs D.ds₃) (D := wholeDesc C D tF tJ t3 silent run)
      (wqWhole C K chal D tF tJ t3 silent run) embP xin cms x π g O chal
      (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _) (wireSilent (K + 1) T3 t3 _)
      [] [] rest S₁ S₂ S₃ r.first.out r.shared.out r.second.out rs₁ rS)
    (a : Out 256 (chainsOf C D tF tJ t3).c₁) (b : Out 256 (chainsOf C D tF tJ t3).c₂)
    (e : Out 256 (chainsOf C D tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP
      xin
      cms x π).det g = some a)
    (h₂ : (run₂ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP
      xin
      cms x π a).det g = some b)
    (h₃ : (run₃ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) embP
      xin
      cms x π a b).det g = some e)
    (seal1 : ByteArray) (hs : r.first.seal = some seal1) :
    ∀ ρ₁, a.2.2 = .loc ρ₁ →
      g (OracleName.g t) (qSeal₁ t (wholeDesc C D tF tJ t3 silent run) embP π ρ₁
                (rtJ (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run) π a)) =
        bytesToDig seal1 := by
  obtain ⟨a', b', e', -, -, -, hz, hc, -⟩ := held_of_readL C K chal D tF tJ t3 silent run embP xin
    cms x π g O rest S₁ S₂ S₃ r rs₁ rS hO hkit₁ hkit₂ hkit₃ A
  rw [sealRead_of_seal r.first seal1 hs] at hc
  exact (seal_of_whole (chainsOf_laws C D tF tJ t3) hz hc h₁ h₂ h₃).2

end OnBytes.Maker
