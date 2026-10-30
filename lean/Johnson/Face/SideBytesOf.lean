-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/SideBytesOf.lean: the clauses of SideBytes (Johnson/Face/BytesOfSide.lean) on the coins
of a compiled run, from plain laws on the letters, at coins of the form with a public start and free
bits (coinsPre, Johnson/WholeKey/CoinLaws.lean): so that SideBytes can be met at such letters.

Main names (namespace Johnson.Face).
  dress_eq_coinsOf   the coins that a compiled run is handed are the coins of byte coins, field by
    field.
  RunForm   what a run's letters owe: the start of a leaf's salt is the run value of its round, the
    free bits and the fixed string fill a whole number of bytes, the word behind the slot's string
    is the place's index.
  byteCoinsOf, dress_coinsPre   the byte coins of drawn coins; the coins handed on are theirs.
  fit_byteCoinsOf   their lengths.
  sideBytes_of   SideBytes from these laws.
  not_zeroRun_of_honest   the exception off the coins, at every hash function, with no verifier: the
    form in which its chance can be bounded.

A note for whoever writes the settings. rtail is one function of the slot for all three kinds of run,
and RunForm asks rtail slot = the index's bytes, 2 ^ depth + slot. Where two kinds have different
depths their slots must differ. At the key's and the link's depth 0 the slot is 0, so at the proof
file's depth 6 the slot can't be 0: it is one of 1 to 63. A value of the settings with slot 0 there
meets no RunForm.
-/
import Johnson.Face.BytesOfSide
import Johnson.WholeKey.CoinLaws
import Johnson.WholeKey.EndsOfYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Face

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print OnBytes.WholeKey
open Johnson.Prover.Print

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- **The coins handed on are the coins of byte coins, field by field.** -/
theorem dress_eq_coinsOf (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits) (nR nK nJ : ℕ)
    (fill : Bits) (co : Coins 256 L) (nJ' n3 depth : ℕ) (bc : ByteCoins L)
    (h1 : co.salt = bytesToBits bc.run1)
    (h2 : ∀ i b k j, start i b co.salt ++
        (if i < nR ∧ k < nK ∧ j < nJ then co.leaf i b k j else fill) =
      leafSalt (bc.runAt nJ' n3 i) (bc.leaf i b k j))
    (h3 : co.pad = bc.pad) (h4 : co.slot = bc.place) (h5 : co.path = bc.slotPath)
    (h6 : co.rsalt ++ rtail co.slot = rsOf (2 ^ depth + bc.place) bc.slotSalt) :
    dress start rtail nR nK nJ fill co = coinsOf nJ' n3 depth bc := by
  obtain ⟨salt, leaf, pad, slot, path, rsalt⟩ := co
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h3 h4 h5
  exact congrArg₂ (fun l r => (⟨bytesToBits bc.run1, l, bc.pad, bc.place, bc.slotPath, r⟩ :
    Coins 256 L)) (funext fun i => funext fun b => funext fun k => funext fun j => h2 i b k j) h6

/-- The lengths and the starts that a run's letters owe, at a run's numbers. -/
structure RunForm (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits) (nR nK nJ ℓr dq : ℕ)
    (fill : Bits) (saltB slot nJ' n3 depth saltR : ℕ) (r2 r3 : ByteArray) : Prop where
  /-- a leaf's salt starts with the run value of its round; the first chain's is the first salt -/
  start : ∀ i b (s : Bits), s.length = 256 →
    start i b s = bytesToBits (if i < nJ' then bitsToBytes s else if i < n3 then r2 else r3)
  fillLen : fill.length = 8 * saltB
  rsaltLen : ℓr = 8 * saltR
  tail : rtail slot = bytesToBits (Fmt.u64n (2 ^ depth + slot))
  slotLt : slot < 2 ^ depth
  pathLen : dq = depth
  r2Size : r2.size = 32
  r3Size : r3.size = 32

/-- The byte coins of drawn coins. -/
def byteCoinsOf (co : Coins 256 L) (r2 r3 : ByteArray) : ByteCoins L where
  run1 := bitsToBytes co.salt
  run2 := r2
  run3 := r3
  leaf := fun i b k j => bitsToBytes (co.leaf i b k j)
  pad := co.pad
  place := co.slot
  slotPath := co.path
  slotSalt := bitsToBytes co.rsalt

variable {start : ℕ → Bool → Bits → Bits} {rtail : ℕ → Bits} {nR nK nJ ℓr dq : ℕ} {fill : Bits}
  {saltB slot nJ' n3 depth saltR : ℕ} {r2 r3 : ByteArray} {pad : Body L}

theorem whole_of_len {l : List Bool} {n : ℕ} (h : l.length = 8 * n) : whole l = true :=
  (whole_iff l).2 ⟨n, h⟩

/-- What a drawn value of coinsPre holds. -/
structure PreCoins (co : Coins 256 L) (nR nK nJ ℓ ℓr dq : ℕ) (fill : Bits) (pad : Body L)
    (slot : ℕ) : Prop where
  salt : co.salt.length = 256
  leaf : ∀ i b k j, (co.leaf i b k j).length = ℓ ∨ co.leaf i b k j = fill
  out : ∀ i b k j, ¬ (i < nR ∧ k < nK ∧ j < nJ) → co.leaf i b k j = fill
  pad : co.pad = pad
  slot : co.slot = slot
  path : co.path.length = dq
  rsalt : co.rsalt.length = ℓr

theorem preCoins_coinsPre (sFS ℓ : ℕ) (hs : sFS = 256)
    (E : Enum (RunBits 256 nR nK nJ sFS ℓ ℓr dq)) (a : Fin (E.n + 1)) :
    PreCoins ((coinsPre nR nK nJ sFS ℓ ℓr dq pad slot fill E).e a) nR nK nJ ℓ ℓr dq fill pad
      slot := by
  refine ⟨?_, fun i b k j => ?_, fun i b k j h => dif_neg h, rfl, rfl, ?_, ?_⟩
  · show (List.ofFn (E.e a).1).length = 256
    rw [List.length_ofFn]
    exact hs
  · show ((if h : i < nR ∧ k < nK ∧ j < nJ then
      List.ofFn ((E.e a).2.1 ⟨i, h.1⟩ b ⟨k, h.2.1⟩ ⟨j, h.2.2⟩) else fill).length = ℓ) ∨
      (if h : i < nR ∧ k < nK ∧ j < nJ then
        List.ofFn ((E.e a).2.1 ⟨i, h.1⟩ b ⟨k, h.2.1⟩ ⟨j, h.2.2⟩) else fill) = fill
    split
    · exact Or.inl List.length_ofFn
    · exact Or.inr rfl
  · exact List.length_ofFn
  · exact List.length_ofFn

/-- **The coins handed on are the coins of their byte coins.** -/
theorem dress_coinsPre (co : Coins 256 L)
    (hp : PreCoins co nR nK nJ (8 * saltB) ℓr dq fill pad slot)
    (hf : RunForm start rtail nR nK nJ ℓr dq fill saltB slot nJ' n3 depth saltR r2 r3) :
    dress start rtail nR nK nJ fill co = coinsOf nJ' n3 depth (byteCoinsOf co r2 r3) := by
  have hw : ∀ i b k j, whole (co.leaf i b k j) = true := fun i b k j => by
    rcases hp.leaf i b k j with h | h
    · exact whole_of_len h
    · rw [h]
      exact whole_of_len hf.fillLen
  refine dress_eq_coinsOf start rtail nR nK nJ fill co nJ' n3 depth _
    (bytesToBits_bitsToBytes _ (whole_of_len (n := 32) hp.salt)).symm (fun i b k j => ?_) rfl rfl
    rfl ?_
  · have hl : (if i < nR ∧ k < nK ∧ j < nJ then co.leaf i b k j else fill) = co.leaf i b k j := by
      split
      · rfl
      · rename_i h
        exact (hp.out i b k j h).symm
    rw [hl, hf.start i b co.salt hp.salt]
    show _ = bytesToBits _ ++ bytesToBits (bitsToBytes (co.leaf i b k j))
    rw [bytesToBits_bitsToBytes _ (hw i b k j)]
    rfl
  · rw [hp.slot, hf.tail]
    show _ = bytesToBits (bitsToBytes co.rsalt) ++ _
    rw [bytesToBits_bitsToBytes _ (whole_of_len (n := saltR) (by rw [hp.rsalt]; exact hf.rsaltLen))]
    rw [← hp.slot]
    rfl

/-- **Their lengths.** -/
theorem fit_byteCoinsOf (co : Coins 256 L)
    (hp : PreCoins co nR nK nJ (8 * saltB) ℓr dq fill pad slot)
    (hf : RunForm start rtail nR nK nJ ℓr dq fill saltB slot nJ' n3 depth saltR r2 r3)
    (s : OnBytes.Params.LinBindingShape) (hd : s.logLeaves = depth) (hs : s.saltBytes = saltR) :
    (byteCoinsOf co r2 r3).Fit saltB s where
  run1 := size_bitsToBytes _ 32 hp.salt
  run2 := hf.r2Size
  run3 := hf.r3Size
  leaf := fun i b k j => by
    rcases hp.leaf i b k j with h | h
    · exact size_bitsToBytes _ _ h
    · show (bitsToBytes (co.leaf i b k j)).size = saltB
      rw [h]
      exact size_bitsToBytes _ _ hf.fillLen
  place := by
    show co.slot < 2 ^ s.logLeaves
    rw [hp.slot, hd]
    exact hf.slotLt
  slotPath := by
    show co.path.length = s.logLeaves
    rw [hp.path, hd]
    exact hf.pathLen
  slotSalt := by
    rw [hs]
    exact size_bitsToBytes _ _ (by rw [hp.rsalt]; exact hf.rsaltLen)

section Letters

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- the ground input -/
local notation "ℜ" => R S c₀ m₀

/-- **SideBytes from plain laws**: at letters whose drawn coins are of the form PreCoins, and whose
starts, words and slots are of the form RunForm. -/
theorem sideBytes_of (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) (cB : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (runsT : H.KT → ByteArray × ByteArray)
    (runsB : H.KB → ByteArray × ByteArray) (rL : H.KL → ByteArray × ByteArray)
    (hc : cB.size = 32) (hL : sL.logLeaves = 0)
    (salts : ∀ b j, j < 2 ^ frS.P.T.a →
      ∃ o : ByteArray, o.size = saltG S.G ∧ H.sl.e b j = leafSalt cB o)
    (ℓrT ℓrL ℓrB dT dL dB slotT slotL slotB : ℕ) (padT padL padB : Body (LC S c₀ m₀))
    (pT : ∀ a, PreCoins (H.coT.e a) H.nR H.nK H.nJ (8 * saltG S.G) ℓrT dT H.fill padT slotT)
    (pL : ∀ a, PreCoins (H.coL.e a) H.nR H.nK H.nJ (8 * saltG S.G) ℓrL dL H.fill padL slotL)
    (pB : ∀ a, PreCoins (H.coB.e a) H.nR H.nK H.nJ (8 * saltG S.G) ℓrB dB H.fill padB slotB)
    (fT : ∀ κ, RunForm (H.startT (H.rvT κ)) H.rtail H.nR H.nK H.nJ ℓrT dT H.fill (saltG S.G) slotT
      (GT S).nJ (GT S).n3 (sTG S.G).logLeaves (sTG S.G).saltBytes (runsT κ).1 (runsT κ).2)
    (fL : ∀ κ, RunForm (H.startL (H.rvL κ)) H.rtail H.nR H.nK H.nJ ℓrL dL H.fill (saltG S.G) slotL
      (dsF.length + 1) (dsF.length + 1) sL.logLeaves sL.saltBytes (rL κ).1 (rL κ).2)
    (fB : ∀ κ, RunForm (H.startB (H.rvB κ)) H.rtail H.nR H.nK H.nJ ℓrB dB H.fill (saltG S.G) slotB
      (GB S).nJ (GB S).n3 (sBG S.G).logLeaves (sBG S.G).saltBytes (runsB κ).1 (runsB κ).2)
    (capT : ∀ j, H.capT j < 2 ^ 64) (capL : ∀ j, H.capL j < 2 ^ 64)
    (capB : ∀ j, H.capB j < 2 ^ 64) (number : ∀ j, j < H.M + 1 → H.nm j < 2 ^ 64) :
    SideBytes S c₀ m₀ H cB sL runsT runsB where
  c32 := hc
  depthL := hL
  tableSalts := salts
  coinsT := fun a k => ⟨byteCoinsOf (H.coT.e a) (runsT (H.kT.e k)).1 (runsT (H.kT.e k)).2,
    dress_coinsPre _ (pT a) (fT _), fit_byteCoinsOf _ (pT a) (fT _) _ rfl rfl, rfl, rfl⟩
  coinsL := fun a k => ⟨byteCoinsOf (H.coL.e a) (rL (H.kL.e k)).1 (rL (H.kL.e k)).2,
    dress_coinsPre _ (pL a) (fL _), fit_byteCoinsOf _ (pL a) (fL _) _ rfl rfl⟩
  coinsB := fun a k => ⟨byteCoinsOf (H.coB.e a) (runsB (H.kB.e k)).1 (runsB (H.kB.e k)).2,
    dress_coinsPre _ (pB a) (fB _), fit_byteCoinsOf _ (pB a) (fB _) _ rfl rfl, rfl, rfl⟩
  capT := capT
  capL := capL
  capB := capB
  number := number

/-- the told record -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading S c₀ m₀

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

set_option maxRecDepth 20000 in
/-- **The exception, read off the coins, with no verifier.** Where the six values that the coins fix
pass the format's test, what the honest side returns is not excepted: at every hash function, at an
index of ok and an instance of Tr. -/
theorem not_zeroRun_of_honest (d : OnBytes.K.Arm.Pub.D8)
    (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (g : Fam (typedOracleFamily 256 (ℜ).queryLayout.K (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)))
    (runsT : H.KT → ByteArray × ByteArray) (runsB : H.KB → ByteArray × ByteArray)
    (ok : (ℜ).Index → Prop) (Tr : (ℜ).Index → (ℜ).Instance → Prop) (hP : StratsPrint S c₀ m₀ H runsT runsB ok Tr)
    (i : (ℜ).Index) (x : XF) (hi : ok i) (hTr : Tr i x)
    (c : DrawC 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits H.KT H.KL) (hc : DrawCOf H c)
    (dP : DrawP 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits H.KB) (hdP : DrawPOf H dP)
    (okT1 : Fmt.runOk (bitsToBytes c.co.salt) = true)
    (okB1 : Fmt.runOk (bitsToBytes dP.co.salt) = true)
    (okT2 : Fmt.runOk (runsT c.κ).1 = true) (okT3 : Fmt.runOk (runsT c.κ).2 = true)
    (okB2 : Fmt.runOk (runsB dP.κ).1 = true) (okB3 : Fmt.runOk (runsB dP.κ).2 = true) :
    ¬ ZeroRun S c₀ m₀ ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).1
      ((proveAt (ℜ).queryLayout ((𝔗).cA d) (ℜ).fixedSample H ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2 x
        dP).det g) := by
  rintro (⟨a, ha, hb⟩ | ⟨b, hb', hb⟩)
  · rw [det_commitAt] at ha
    dsimp only at ha
    obtain ⟨⟨a', τ⟩, hv, e, -⟩ := shown_some ha
    obtain rfl : a' = a := e
    have r := hv
    rw [proveTA_fullD] at r
    have so := stratOwes_of_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (byteCoinsOf (H.dressT (H.rvT c.κ) c.co) (runsT c.κ).1 (runsT c.κ).2) _ _ _ _ r
      (hP.T i c.r _ c.κ hi)
    obtain ⟨z, -, e₀, -⟩ := (proveX_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 r
    refine hb ⟨?_, ?_, ?_⟩
    · rw [e₀]
      exact okT1
    · rw [so.run2]
      exact okT2
    · rw [so.run3]
      exact okT3
  · obtain ⟨-, -, hlen, -⟩ := hc
    obtain ⟨hj, -⟩ := hdP
    have hj' : dP.j < c.copies.length := by rw [hlen]; exact hj
    have atPlace : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj'
    generalize c.copies[dP.j] = e at atPlace
    have ft : ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2.copies[dP.j]? =
        some (tabG (ℜ).queryLayout ((𝔗).Sd d) H g i e.r e.s) := by
      rw [det_commitAt]
      show (c.copies.map fun e => tabG (ℜ).queryLayout ((𝔗).Sd d) H g i e.r e.s)[dP.j]? = _
      rw [List.getElem?_map, atPlace]
      rfl
    have hi' : ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2.i = i := by
      rw [det_commitAt]
    have hproof := det_proveAt (ℜ).queryLayout ((𝔗).cA d) (ℜ).fixedSample H g ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H
                         i c).det g).2 x dP _ ft
    rw [hi'] at hproof
    rw [hproof] at hb'
    dsimp only at hb'
    obtain ⟨⟨b', τ⟩, hv, e', -⟩ := shown_some hb'
    obtain rfl : b' = b := e'
    have r := hv
    rw [proveBA_fullD] at r
    have so := stratOwes_of_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (byteCoinsOf (H.dressB (H.rvB dP.κ) dP.co) (runsB dP.κ).1 (runsB dP.κ).2) _ _ _ _ r
      (hP.B i e.r _ x (H.nm dP.j) dP.κ hTr)
    obtain ⟨z, -, e₀, -⟩ := (proveX_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 r
    refine hb ⟨?_, ?_, ?_⟩
    · rw [e₀]
      exact okB1
    · rw [so.run2]
      exact okB2
    · rw [so.run3]
      exact okB3

end Letters

end Johnson.Face

#print axioms Johnson.Face.dress_eq_coinsOf
#print axioms Johnson.Face.dress_coinsPre
#print axioms Johnson.Face.fit_byteCoinsOf
#print axioms Johnson.Face.sideBytes_of
#print axioms Johnson.Face.not_zeroRun_of_honest
