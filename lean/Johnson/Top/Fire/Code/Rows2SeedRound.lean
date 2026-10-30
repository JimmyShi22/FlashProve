-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2SeedRound.lean: THE KEY FILE's SHARED CHAIN, SUB-PROTOCOLS 2 | 5 (the two
sendings): PUBLIC FACTS ON THE STRETCH OF THE FILE's OWN DATA THAT THE MAKER CUTS FOR THEM, AND ON
THEIR PIECES' BASES. For rows 2.2 | 2.5 at the name's terms. IT PAYS NO FIELD.
  two_of_send      general in the IOP as written in Lean: where a sub-protocol of the shared chain
                   declares the sending kind's two rounds at Q, its stretch is two rounds' data
                   [d₁, d₂]: d₁ bears the entry of the seeds, the kind «seeds» and as many trees as
                   Q lays; d₂ the entry of the answers
  rounds22 | rounds25   sub-protocols 2 | 5 declare these rounds, at the key file's own parameters
  data22_of | data25_of   so the stretches are two rounds' data
  seed22 | seed25  the same said of given [d₁, d₂], at p14At X P
  free_key         the sending's parameters do not read «before the point»
  trees2 | trees5 | seeds_key   CLOSED FACTS, by Lean's kernel, at the typed key: 1 | 2 trees; one
                   seed at both
  seed22_key | seed25_key   the same at the typed key's letters, with the trees' numbers 1 | 2
  …_held           where the cut is said at the held sub-protocols
  none2_d | one2_d   CLOSED FACTS, by Lean's kernel: the written data's first round of the shared
                   chain sends no tree; its first four send one
  base22 | base25  in scope, at the written data: the pieces' bases are 6 | 7
After Johnson/Top/Fire/Code/Row117Paid.lean's data17_of, Row117Eight.lean's data17_more and
RowBaseFull.lean's treeAt_full (the like at the first chain's sub-protocol 17).
OBJECT: the maker's cut of the key file's own data · USER: rows 2.2 | 2.5 at the name's terms
(seed_draws' he | hk | h1; the frame's reader at base + n) · LETTERS: X N P · file D · c₂ k₂ ·
sentU · d₁ d₂. base22 | base25 FIX THE RELEASE's ONE CONFIGURATION.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowStretchPairs
import Johnson.Top.Fire.Code.Rows2Public
import Johnson.Top.Fire.Code.RowBaseFull
import Johnson.Top.Fire.Code.KeyRoundsAtSeat
import Johnson.RunOne.KeyRow22AtSeat
import Johnson.RunOne.KeySendCond
import Johnson.RunOne.KeyScopeNums
import Johnson.RunOne.KeyOn2Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃
  seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open Johnson.RunOne.KeyRows23 (shared_2 shared_5 sends_at_blocks p14Key p14At_key sentUKey withU_key
  P2K P5K)
open VerifiableInference.Desc.K1 (seedEntry answerEntry)
open _root_.Desc.K14 (parK1 withU withOmega)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq sum_eq_sumE)
open Johnson.RunOne.KeyLetters (t1_d)

/-- **The stretch of a sending: two rounds' data.** -/
theorem two_of_send {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl))
    (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b)
    (Q : K1.Par) (hr : b.rounds = K1.rounds Q) :
    ∃ d₁ d₂, cutDs D.ds₂ c₂ k₂ n = [d₁, d₂] ∧ d₁.entry = seedEntry Q ∧ d₁.kind = .seeds ∧
      d₁.trees.length = Q.trees.length ∧ d₂.entry = answerEntry Q := by
  have has := stretch_of_data₂ F file D h c₂ k₂ q₂ n b hb
  rw [hr] at has
  have has' : List.Forall₂ RoundAsG (cutDs D.ds₂ c₂ k₂ n)
      [{ entry := seedEntry Q }, { entry := answerEntry Q }] := has
  obtain ⟨d₁, l₁, h1, t1, e1⟩ := List.forall₂_cons_right_iff.1 has'
  obtain ⟨d₂, l₂, h2, t2, e2⟩ := List.forall₂_cons_right_iff.1 t1
  obtain rfl := List.forall₂_nil_right_iff.1 t2
  subst e2
  exact ⟨d₁, d₂, e1, h1.1,
    (Option.some.inj ((Johnson.RunOne.KeySendGood.seed_kind Q).symm.trans h1.2.1)).symm,
    h1.2.2.2.1, h2.1⟩

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (file : String) (D : WholeD)
    (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))

/-- Sub-protocol 2 declares the sending kind's two rounds. -/
theorem rounds22 (hp : (Fk X N P).planOk = true) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    ∃ sentU b, withU (p14At X P).S = some sentU ∧ (c₂ :: k₂)[2]? = some b ∧
      b.rounds = K1.rounds (parK1 (p14At X P) 2 "o_u and the first mask" sentU) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  obtain ⟨sentU, hU, e2, -⟩ := sends_at_blocks (p14At X P) b1 b2 b3 b4 b5 b6 b7 b8 h8
  refine ⟨sentU, seat b2, hU, ?_, ?_⟩
  · rw [← q₂]
    exact shared_2 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8
  · rw [e2]
    rfl

/-- Sub-protocol 5 declares the sending kind's two rounds. -/
theorem rounds25 (hp : (Fk X N P).planOk = true) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    ∃ b, (c₂ :: k₂)[5]? = some b ∧
      b.rounds = K1.rounds (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  obtain ⟨sentU, -, -, e5⟩ := sends_at_blocks (p14At X P) b1 b2 b3 b4 b5 b6 b7 b8 h8
  refine ⟨seat b5, ?_, ?_⟩
  · rw [← q₂]
    exact shared_5 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8
  · rw [e5]
    rfl

/-- **The stretch at sub-protocol 2 is two rounds' data.** -/
theorem data22_of (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    ∃ sentU d₁ d₂, withU (p14At X P).S = some sentU ∧ cutDs D.ds₂ c₂ k₂ 2 = [d₁, d₂] ∧
      d₁.entry = seedEntry (parK1 (p14At X P) 2 "o_u and the first mask" sentU) ∧
      d₁.kind = .seeds ∧
      d₁.trees.length = (parK1 (p14At X P) 2 "o_u and the first mask" sentU).trees.length ∧
      d₂.entry = answerEntry (parK1 (p14At X P) 2 "o_u and the first mask" sentU) := by
  obtain ⟨sentU, b, hU, hb, hr⟩ := rounds22 X N P c₂ k₂ hp q₂
  obtain ⟨d₁, d₂, hc, a⟩ := two_of_send (Fk X N P) file D hdata c₂ k₂ q₂ 2 b hb _ hr
  exact ⟨sentU, d₁, d₂, hU, hc, a⟩

/-- **The stretch at sub-protocol 5 is two rounds' data.** -/
theorem data25_of (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    ∃ d₁ d₂, cutDs D.ds₂ c₂ k₂ 5 = [d₁, d₂] ∧
      d₁.entry = seedEntry (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) ∧
      d₁.kind = .seeds ∧
      d₁.trees.length =
        (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)).trees.length ∧
      d₂.entry =
        answerEntry (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) := by
  obtain ⟨b, hb, hr⟩ := rounds25 X N P c₂ k₂ hp q₂
  exact two_of_send (Fk X N P) file D hdata c₂ k₂ q₂ 5 b hb _ hr

/-- **The same said of given data, at sub-protocol 2.** -/
theorem seed22 (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (sentU : Array OnBytes.OracleNotice)
    (hU : withU (p14At X P).S = some sentU) (d₁ d₂ : RDT)
    (hcut : cutDs D.ds₂ c₂ k₂ 2 = [d₁, d₂]) :
    d₁.entry = seedEntry (parK1 (p14At X P) 2 "o_u and the first mask" sentU) ∧
      d₁.kind = .seeds ∧
      d₁.trees.length = (parK1 (p14At X P) 2 "o_u and the first mask" sentU).trees.length ∧
      d₂.entry = answerEntry (parK1 (p14At X P) 2 "o_u and the first mask" sentU) := by
  obtain ⟨s', e₁, e₂, hU', hc, a⟩ := data22_of X N P file D c₂ k₂ hdata hp q₂
  obtain rfl : s' = sentU := Option.some.inj (hU'.symm.trans hU)
  have e := hc.symm.trans hcut
  obtain rfl : e₁ = d₁ := (List.cons.inj e).1
  obtain rfl : e₂ = d₂ := (List.cons.inj (List.cons.inj e).2).1
  exact a

/-- **The same said of given data, at sub-protocol 5.** -/
theorem seed25 (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (d₁ d₂ : RDT)
    (hcut : cutDs D.ds₂ c₂ k₂ 5 = [d₁, d₂]) :
    d₁.entry = seedEntry (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) ∧
      d₁.kind = .seeds ∧
      d₁.trees.length =
        (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)).trees.length ∧
      d₂.entry =
        answerEntry (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) := by
  obtain ⟨e₁, e₂, hc, a⟩ := data25_of X N P file D c₂ k₂ hdata hp q₂
  have e := hc.symm.trans hcut
  obtain rfl : e₁ = d₁ := (List.cons.inj e).1
  obtain rfl : e₂ = d₂ := (List.cons.inj (List.cons.inj e).2).1
  exact a

end

/-! ## At the typed key -/

/-- The sending's parameters do not read «before the point». -/
theorem free_key (bp : List (ℕ × ℕ)) (i : ℕ) (s : String) (sent : Array OnBytes.OracleNotice) :
    parK1 (p14Key bp) i s sent = parK1 (p14Key []) i s sent := rfl

theorem trees2 : P2K.trees.length = 1 := by decide +kernel
theorem trees5 : P5K.trees.length = 2 := by decide +kernel
theorem seeds_key : P2K.seeds = 1 ∧ P5K.seeds = 1 := by decide +kernel

/-- Trials that such comparisons can fail. -/
theorem trees2_no : ¬ P2K.trees.length = 2 := by decide +kernel
theorem trees5_no : ¬ P5K.trees.length = 1 := by decide +kernel

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (file : String) (D : WholeD)
    (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))

/-- **Sub-protocol 2's stretch, at the typed key's letters.** -/
theorem seed22_key (hkey : X.chains.made.sized.key = keyFull)
    (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (d₁ d₂ : RDT)
    (hcut : cutDs D.ds₂ c₂ k₂ 2 = [d₁, d₂]) :
    d₁.entry = seedEntry (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask"
        sentUKey) ∧ d₁.kind = .seeds ∧ d₁.trees.length = 1 ∧
      d₂.entry = answerEntry (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask"
        sentUKey) := by
  have hU : withU (p14At X P).S = some sentUKey := by
    rw [p14At_key hkey P]
    exact withU_key
  have H := seed22 X N P file D c₂ k₂ hdata hp q₂ sentUKey hU d₁ d₂ hcut
  rw [p14At_key hkey P] at H
  refine ⟨H.1, H.2.1, H.2.2.1.trans ?_, H.2.2.2⟩
  rw [free_key]
  exact trees2

/-- **Sub-protocol 5's stretch, at the typed key's letters.** -/
theorem seed25_key (hkey : X.chains.made.sized.key = keyFull)
    (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (d₁ d₂ : RDT)
    (hcut : cutDs D.ds₂ c₂ k₂ 5 = [d₁, d₂]) :
    d₁.entry = seedEntry (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp"
        (withOmega keyFull.once.shape)) ∧ d₁.kind = .seeds ∧ d₁.trees.length = 2 ∧
      d₂.entry = answerEntry (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp"
        (withOmega keyFull.once.shape)) := by
  have H := seed25 X N P file D c₂ k₂ hdata hp q₂ d₁ d₂ hcut
  rw [p14At_key hkey P] at H
  refine ⟨H.1, H.2.1, H.2.2.1.trans ?_, H.2.2.2⟩
  show (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp"
    (withOmega keyFull.once.shape)).trees.length = 2
  rw [free_key]
  exact trees5

/-- One seed at both, at the typed key's letters. -/
theorem seeds_at_key :
    (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask" sentUKey).seeds = 1 ∧
      (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp"
        (withOmega keyFull.once.shape)).seeds = 1 := by
  rw [free_key, free_key]
  exact seeds_key

/-- The same where the cut is said at the held sub-protocols. -/
theorem seed22_key_held (hkey : X.chains.made.sized.key = keyFull)
    (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (d₁ d₂ : RDT)
    (hcut : cutDs D.ds₂ (held c₂ :
      Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl)
      (k₂.map held) 2 = [d₁, d₂]) :
    d₁.entry = seedEntry (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask"
        sentUKey) ∧ d₁.kind = .seeds ∧ d₁.trees.length = 1 ∧
      d₂.entry = answerEntry (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask"
        sentUKey) :=
  seed22_key X N P file D c₂ k₂ hkey hdata hp q₂ d₁ d₂ ((cutDs_held k₂ 2 _ c₂).symm.trans hcut)

theorem seed25_key_held (hkey : X.chains.made.sized.key = keyFull)
    (hdata : (Fk X N P).data file = .ok D) (hp : (Fk X N P).planOk = true)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (d₁ d₂ : RDT)
    (hcut : cutDs D.ds₂ (held c₂ :
      Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl)
      (k₂.map held) 5 = [d₁, d₂]) :
    d₁.entry = seedEntry (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp"
        (withOmega keyFull.once.shape)) ∧ d₁.kind = .seeds ∧ d₁.trees.length = 2 ∧
      d₂.entry = answerEntry (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp"
        (withOmega keyFull.once.shape)) :=
  seed25_key X N P file D c₂ k₂ hkey hdata hp q₂ d₁ d₂ ((cutDs_held k₂ 5 _ c₂).symm.trans hcut)

end

/-! ## The bases -/

set_option maxRecDepth 1000000 in
theorem none2_d : nTrees (dKeyFull.ds₂.take 1) = 0 := by
  show ((dKeyFull.ds₂.take 1).map (·.trees.length)).sum = 0
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem one2_d : nTrees (dKeyFull.ds₂.take 4) = 1 := by
  show ((dKeyFull.ds₂.take 4).map (·.trees.length)).sum = 1
  rw [sum_eq_sumE]
  decide +kernel

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {D : WholeD}
    (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}

/-- **The base of the shared chain's piece 2 is 6**, in scope, at the written data. -/
theorem base22 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀)
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hD : D = writtenKFull)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    cutBase D.t₁ D.ds₂ (held c₂ :
      Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl)
      (k₂.map held) 2 = 6 := by
  have hL := (rounds_in_scope hZ hP hm hX hp hw).2.1
  have hlen : 2 ≤ k₂.length := by
    have h := congrArg List.length hL
    rw [List.length_map, q₂] at h
    have h' : k₂.length + 1 = 12 := h
    omega
  rw [cutBase_held, cutBase_eq k₂ 2 _ _ c₂ hlen, before_sum, ← q₂, hL, hD, writtenKFull_eq, t1_d]
  show 6 + nTrees (dKeyFull.ds₂.take 1) = 6
  rw [none2_d]

/-- **The base of the shared chain's piece 5 is 7**, in scope, at the written data. -/
theorem base25 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀)
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hD : D = writtenKFull)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    cutBase D.t₁ D.ds₂ (held c₂ :
      Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl)
      (k₂.map held) 5 = 7 := by
  have hL := (rounds_in_scope hZ hP hm hX hp hw).2.1
  have hlen : 5 ≤ k₂.length := by
    have h := congrArg List.length hL
    rw [List.length_map, q₂] at h
    have h' : k₂.length + 1 = 12 := h
    omega
  rw [cutBase_held, cutBase_eq k₂ 5 _ _ c₂ hlen, before_sum, ← q₂, hL, hD, writtenKFull_eq, t1_d]
  show 6 + nTrees (dKeyFull.ds₂.take 4) = 7
  rw [one2_d]

end

end LPFD

#print axioms LPFD.two_of_send
#print axioms LPFD.rounds22
#print axioms LPFD.rounds25
#print axioms LPFD.data22_of
#print axioms LPFD.data25_of
#print axioms LPFD.seed22
#print axioms LPFD.seed25
#print axioms LPFD.free_key
#print axioms LPFD.trees2
#print axioms LPFD.trees5
#print axioms LPFD.seeds_key
#print axioms LPFD.trees2_no
#print axioms LPFD.trees5_no
#print axioms LPFD.seed22_key
#print axioms LPFD.seed25_key
#print axioms LPFD.seeds_at_key
#print axioms LPFD.seed22_key_held
#print axioms LPFD.seed25_key_held
#print axioms LPFD.none2_d
#print axioms LPFD.one2_d
#print axioms LPFD.base22
#print axioms LPFD.base25
