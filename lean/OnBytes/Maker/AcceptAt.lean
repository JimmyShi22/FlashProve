-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/AcceptAt.lean: tools for the yes of a file's description at the transcript that the
compiled verifier builds from a typed proof string: the silent rounds' plain parts, and what is
asked of the data and of the reading.

OnBytes/Maker/AcceptAtA.lean shows the decision's yes at that transcript. This file has what it
needs of the three silent rounds, and the record of its hypotheses that name neither a table nor a
transcript.

Main definition.
  `ReadFits`: what is asked of the data and of the reading: two tests on the data; the three
    descriptions' stored tables and numbers of their first trees; that the three chains' views as
    read are `Fmt.viewX` of what was read; `ListedAsDrawn` and `PartsWithin`
    (OnBytes/Maker/ReadFacts.lean) of the three chains.
Main theorems.
  `effPlain_lo`, `effPlain_sh`, `msgF_mkTr`, `msgJ_mkTr`, `msg3_mkTr`, `plAF`, `plAJ1`, `plA31`: the
    plain parts of the three silent rounds of that transcript are those of the string.

What is not claimed. `ReadFits` at any reading: `readFits_chain` (OnBytes/Maker/ReadFitsOf.lean)
gives it from the equations by which the program describes and reads the three chains and three
tests on the data; OnBytes/Maker/OfThreeChains.lean has these equations from the program's own
reading. That the tests pass. Nothing on soundness.


-/
import OnBytes.Maker.TypingHolds
import OnBytes.Maker.AcceptOfYes

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-! ## The silent rounds' plain parts -/

section Eff
variable {lam : ℕ}

/-- In a local round whose slot's component is sent, the plain part is the string's. -/
theorem effPlain_lo (r : Round) (rt : RtC lam × RtC lam) (pl : r.Plain) (h : rt.2.isSome = true) :
    effPlain (RAnn.allLocal r) rt pl = pl := by
  unfold effPlain
  rw [h]
  rfl

/-- In a shared round whose shared component is sent, the plain part is the string's. -/
theorem effPlain_sh (r : Round) (rt : RtC lam × RtC lam) (pl : r.Plain) (h : rt.1.isSome = true) :
    effPlain (RAnn.ofShared .sh r) rt pl = pl := by
  unfold effPlain
  rw [h]
  rfl

end Eff

section Silent
variable {lam K : ℕ} {G : Chains} (V : Wires lam K G) (R : RootsOfChain lam G.sh) (pls : Plains G.sh)
  (ρ : Rho G.sh) (f : (p : OPos G.sh) → Option (Opening lam (OSym G.sh p)))

/-- The front's plain part of the transcript that the compiled verifier builds. -/
theorem msgF_mkTr (hK : SentK G.sh G.ann R) :
    (G.msgF (mkTr G.sh G.ann V.sh R pls ρ f)).2 = G.plF pls := by
  obtain ⟨rt, R⟩ := R
  obtain ⟨pl, pls⟩ := pls
  obtain ⟨c, ρ⟩ := ρ
  exact effPlain_lo G.rF rt pl (hK.1 rfl)

/-- The joining round's, where that round's annotation is "shared". -/
theorem msgJ_mkTr (hJ : G.aJ = RAnn.ofShared .sh G.rJ) (hK : SentK G.sh G.ann R) :
    (G.msgJ (mkTr G.sh G.ann V.sh R pls ρ f)).2 = G.plJ pls := by
  have kJ : SentK G.shJ G.annJ (rtSJ G R) := by
    obtain ⟨rt, R⟩ := R
    exact ((sentK_app (A := RoundSplits.allLocal G.s₁) (B := G.annJ) R).1 hK.2.2).2
  unfold Chains.msgJ Chains.plJ
  rw [trJ_mkTr]
  generalize rtSJ G R = RJ at kJ ⊢
  generalize G.plJ' pls = plJ
  generalize G.rhoJ ρ = ρJ
  generalize opSJ G f = fJ
  obtain ⟨rt, RJ⟩ := RJ
  obtain ⟨pl, plJ⟩ := plJ
  obtain ⟨c, ρJ⟩ := ρJ
  show effPlain G.aJ rt pl = pl
  have h1 : rt.1.isSome = true := kJ.2.1 (by show G.aJ.kind = .sh; rw [hJ]; rfl)
  rw [hJ]
  exact effPlain_sh G.rJ rt pl h1

/-- The seam's. -/
theorem msg3_mkTr (hK : SentK G.sh G.ann R) :
    (G.msg3 (mkTr G.sh G.ann V.sh R pls ρ f)).2 = G.pl3 pls := by
  have kJ : SentK G.shJ G.annJ (rtSJ G R) := by
    obtain ⟨rt, R⟩ := R
    exact ((sentK_app (A := RoundSplits.allLocal G.s₁) (B := G.annJ) R).1 hK.2.2).2
  unfold Chains.msg3 Chains.pl3
  rw [trJ_mkTr]
  generalize rtSJ G R = RJ at kJ ⊢
  generalize G.plJ' pls = plJ
  generalize G.rhoJ ρ = ρJ
  generalize opSJ G f = fJ
  obtain ⟨rt, RJ⟩ := RJ
  obtain ⟨pl, plJ⟩ := plJ
  obtain ⟨c, ρJ⟩ := ρJ
  have k3 : SentK G.sh₃ G.ann₃ (RT.snd (s := G.s₂) RJ) :=
    ((sentK_app (A := RoundSplits.const (RAnn.ofShared .sh) G.s₂) (B := G.ann₃) RJ).1 kJ.2.2).2
  show ((Tr.snd (s := G.s₂) (mkTr (G.s₂ ++ G.sh₃)
    (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃)
    (WireSB.app V.W₂ V.sh₃) RJ plJ ρJ fun p => fJ (.inr p))).1).2 = (Plains.snd (s := G.s₂) plJ).1
  rw [mkTr_app, Tr.snd_app, WireSB.snd_app]
  generalize RT.snd (s := G.s₂) RJ = R3 at k3 ⊢
  generalize Plains.snd (s := G.s₂) plJ = pl3
  generalize Rho.snd (s := G.s₂) ρJ = ρ3
  obtain ⟨rt3, R3⟩ := R3
  obtain ⟨p3, pl3⟩ := pl3
  obtain ⟨c3, ρ3⟩ := ρ3
  exact effPlain_lo G.r3 rt3 p3 (k3.1 rfl)

end Silent

section Parts
variable {lam : ℕ} (G : Chains) (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂)
  (k₃ : ChainStr lam G.c₃)

/-- The front's plain part of three chains' strings in a row is the first string's first. -/
theorem plAF : G.plF (plainsA G k₁ k₂ k₃) = k₁.plains.1 := by
  obtain ⟨_, ⟨pF, pl₁⟩, _⟩ := k₁
  rfl

/-- The joining round's is the second string's first. -/
theorem plAJ1 : G.plJ (plainsA G k₁ k₂ k₃) = k₂.plains.1 := by
  unfold Chains.plJ
  rw [plAJ]
  obtain ⟨_, ⟨pJ, pl₂⟩, _⟩ := k₂
  rfl

/-- The seam's is the third string's first. -/
theorem plA31 : G.pl3 (plainsA G k₁ k₂ k₃) = k₃.plains.1 := by
  unfold Chains.pl3
  rw [plAJ]
  obtain ⟨_, ⟨pJ, pl₂⟩, _⟩ := k₂
  exact congrArg Prod.fst (Plains.snd_app (s := G.s₂) (t := G.c₃) pl₂ k₃.plains)

end Parts

/-! ## The decision at the typed string -/

/-- **What is asked of the data and of the reading**, beside the typing: the fields of `FileHeldA`
(OnBytes/Maker/ViewsAlike.lean) that name neither a table nor a transcript. -/
structure ReadFits (a : ℕ) (W : Three.Whole) (r : Proof.TailRead) (S₁ S₂ S₃ : Fmt.SpecX) :
    Prop where
  shape : shapesFit a W = true
  bare : sealBare W = true
  st₁ : S₁.stored = W.ds₁.map (·.stored)
  st₂ : S₂.stored = W.ds₂.map (·.stored)
  st₃ : S₃.stored = W.ds₃.map (·.stored)
  ft₁ : S₁.base.firstTree = 0
  ft₂ : S₂.base.firstTree = 0
  ft₃ : S₃.base.firstTree = Three.first₃ W.t₁
  ls₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList
  ls₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList
  ls₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList
  v₁ : r.first.view = Fmt.viewX S₁ r.first.out
  v₂ : r.shared.view = Fmt.viewX S₂ r.shared.out
  v₃ : r.second.view = Fmt.viewX S₃ r.second.out
  pw₁ : PartsWithin W.ds₁ r.first.out.rounds.toList
  pw₂ : PartsWithin W.ds₂ r.shared.out.rounds.toList
  pw₃ : PartsWithin W.ds₃ r.second.out.rounds.toList

end OnBytes.Maker
