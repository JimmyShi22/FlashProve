-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsAtFiles.lean: an implication that joins the folder's lemmas on the
private aborts of provG, the prover of the sessions. Its premises are public conditions, two
conditions on the rows and the prover, a named condition P on the hidden input and its trace, one
premise for each of two chains that covers every part in it, and two sums of stated shares. It
concludes the field sessionStops of PremWDebts (E2E/BridgeDebts.lean). The measure is over the
verifier's messages; the bound is asked at every index and every value of the committer's
randomness. It is glue, with no bound of its own. It is idle at P := everything or nothing, at rows
that never abort privately, and so at rows that always abort publicly.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
sessionStops_at_files has its premises in four groups. G are the rows (the library's structure
Sides), H is the prover of parts.
(1) Public. Z is in scope. The library's reader returns its table at Z. protocolDataWellFormed accepts Z's public
head. LaidAt holds at Zp, Np, cF.
(2) On the rows G and the prover H. ready, run at provG, succeeds at some input and some coins (hR).
No row of G's first chain is at a place of the kind frame (hn).
(3) On the hidden input. Every tied request of Yes (TiedYes, E2E/BridgeJoinAtFiles.lean), with the
trace that H.trace returns, meets P (hP). It is asked at every request of Yes, whatever the range of
indices.
(4) On the parts. At every v that meets P, PartsHeld holds at the first chain without its last
member and at the second chain. The sums of the shares that the two chains' parts state (sharesSum,
which names no input) are at most z₁ and z₃.
It concludes that HidSmall holds for the family famG at the relation TiedIn, with the bound z₁ + z₃,
for every range ok of indices and every set Gs of OOD seeds. At Gs := fun _ => True this is the
field sessionStops of PremWDebts, with hO' := z₁ + z₃.
  premWDebts_stops   from the list PremWDebts at any number in that field's place, the reader's
      table and groups (2) to (4): the list at z₁ + z₃. Group (1) is read off the list. So Lean
      holds that the conclusion above is that field.
  dropLast_of_cut   a list that is pre followed by one member has pre as its dropLast.

How it fits. stopsFit_provG (Johnson/FrontRoad/SessionStopsFit.lean) gives StopsFit at some list
pre; by the cut that list is the first chain's list without its last member, so the premises on the
first chain can be stated there. That last member, the sealing round, has no half of the prover (the
field bare of StopsFit). hidSmall_of_parts (Johnson/FrontRoad/SessionStopsOfParts.lean) and
hidSmall_in (E2E/BridgeJoinAtFiles.lean) do the rest. Group (1) is made of fields of PremWDebts and
a premise of Spec.roadPrivate_of_debts (Johnson/FrontRoad/FromDebtsSpec.lean).
Groups (3) and (4) share P, and group (4) also fixes z₁ and z₃, so P is chosen first. It must be
provable of every tied request of Yes (group 3), and strong enough that each part's local bound
holds wherever P holds (group 4). Terms on whoever chooses P are quoted in the head of
Johnson/Desc/ProofFile/Honest/Law/SharesOn.lean.
A lemma toward the condition HidSmall (E2E/BridgePrivacy.lean); not one of the release's goal
statements.

Limits.
  No parameters are known at which its premises hold together.
  It proves no probability bound of its own: it passes on the bounds that its premises state. No
      value is given for z₁ + z₃, and no target for it is named: in PremWDebts the number in that
      field's place, hO', is a free parameter (E2E/BridgeDebts.lean).
  P reads the hidden input. That every tied request of Yes, with its trace, meets P is the premise
      hP; it is not proved here.
  hR follows from the field rows of PremWDebts together with two things more: one input of the rows'
      relation, and one list of challenges at which the prover does not abort at that input
      (ready_of_rows, Johnson/FrontRoad/SessionStopsFit.lean, whose Limits say more). Neither is
      proved here.
  If Yes holds of no pair, or ok of no index, the conclusion holds of nothing. All limits of
      Johnson/FrontRoad/SessionStopsOfHeld.lean, SessionStopsOfParts.lean and SessionStopsFit.lean
      hold, those on the two degenerate choices of P among them.
  What ties a part's local bound to the probability that a combination leaves its window at one
      place of the approximate range proof (Johnson/FrontRoad/WindowAtChecks.lean [not in this
      library]) is not here.
-/
import Johnson.FrontRoad.SessionStopsOfParts
import Johnson.FrontRoad.SessionStopsFit

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open ProofFile.Honest (Prover ProverCoinCounts Sides Local Face Why StopsFit ChainHeld chainGates Placed StopDebt
  chainHeld_of stopDebt_no_hid)
open OnBytes.Maker (RDT WholeD)
open VerifiableInference.Desc (KindName)
open ProofFile.Honest (Ready Coins ready)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_atFiles : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_atFiles {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- A list that is pre followed by one member has pre as its dropLast. -/
theorem dropLast_of_cut {α : Type} {l pre : List α} {e : α} (h : l = pre ++ [e]) :
    pre = l.dropLast := by
  rw [h, List.dropLast_concat]

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **An implication: the field sessionStops of PremWDebts**, from public conditions, two conditions
on the rows and the prover, a named condition P on the hidden input and its trace, one premise for
each of the two chains that covers every part in it, and two sums of stated shares. The measure is
over the verifier's messages; the bound is asked at every index and every value of the committer's
randomness. It is glue, with no bound of its own. It is idle at P := everything or nothing, at rows
that never abort privately, and so at rows that always abort publicly. -/
theorem sessionStops_at_files (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst} {k : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr → P ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (p₁ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first (descZ Zp Np cF).first.blocksInOrder.dropLast
      (dataZ Z).ds₁ ≤ z₁)
    (p₃ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder
      (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤
      z₃)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (z₁ + z₃) := by
  obtain ⟨pre, e, cut, -, Sf⟩ := stopsFit_provG Z Zp Np cF B G H scope hr live L hR hn
  obtain rfl := dropLast_of_cut cut
  exact hidSmall_in Z Zp Np cF run₂ run₃ B G H
    (hidSmall_of_parts Z Zp Np cF run₂ run₃ B G H Sf _ P z₁ z₃ hP p₁ s₁ p₃ s₃)

/-- **In the list PremWDebts the field sessionStops can be replaced**: from the list at any number z
in that field's place, and groups (2) to (4) of sessionStops_at_files with the reader's table, the
list at z₁ + z₃. So Lean holds that the conclusion of sessionStops_at_files, at Gs := fun _ => True,
is that field. The measure, and the ways in which it is idle, are those of sessionStops_at_files. -/
theorem premWDebts_stops (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ)
    (Fx : VerifiableInference.Desc.FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts)
    [Fintype Q₂] [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
    (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
    (c : OnBytes.WholeKey.CoinNums (List Bool))
    (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
    (okV : ByteArray × ByteArray → Prop) (v₀ : ByteArray × ByteArray)
    (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
    (Yes : FullSizeMatrix → XF → Prop) (ok : FullSizeMatrix → Prop) (sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)) (s1 : ℕ)
    (zT hT z : ℝ≥0∞)
    (d : PremWDebts c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT z)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst} {k : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (P : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop) (z₁ z₃ : ℝ≥0∞)
    (hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr → P ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (p₁ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast (dataZ Z).ds₁)
    (s₁ : sharesSum (provG Z Zp Np cF B G H).first (descZ Zp Np cF).first.blocksInOrder.dropLast
      (dataZ Z).ds₁ ≤ z₁)
    (p₃ : PartsHeld P Face.own.sees (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder
      (dataZ Z).ds₃)
    (s₃ : sharesSum (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃ ≤
      z₃) :
    PremWDebts c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT (z₁ + z₃) := by
  obtain ⟨D, r, L⟩ := d.laid
  exact { d with
    sessionStops := sessionStops_at_files Z Zp Np cF run₂ run₃ B G H d.scope hr d.live L hR hn Yes
      P z₁ z₃ hP p₁ s₁ p₃ s₃ ok fun _ => True }

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_atFiles
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_atFiles
#print axioms OnBytes.FrontRoad.dropLast_of_cut
#print axioms OnBytes.FrontRoad.sessionStops_at_files
#print axioms OnBytes.FrontRoad.premWDebts_stops
