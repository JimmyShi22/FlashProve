-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OnlineStopsOfK8.lean: where only the kind K8 has a second stop, the parts' premise of the private stops asks of K8 alone.

1.  partsHeld_of_k8: PartsHeld of one chain, from: no part outside K8 has a second stop; and each K8 part's own debt (K8Clause).
2.  online_stops_of_k8: the online prover of the term meets the private stops' line at the number, from SecondStopsAreK8s and K8's
    clause at the first and the last chain.
3.  secondStopsAreK8s_of_kinds: SecondStopsAreK8s from each other kind, one by one; kindQuiet_of_lot: a kind from its lot's list of halves,
    where the returned prover's sides of that kind lie in that list. That they do is a premise here.
4.  Nothing here says that K8's parts meet their debt, or that any kind is quiet.
-/
import Johnson.T3.OnlineStopsOfParts
import E2E.TheHonestProverStatements
import E2E.TheHonestProver

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Prover ProverCoinCounts Sides Local AtHonest OnlineProverWithDescription Coins Ready ready Face Placed Part StopDebt Why Cells)
open ProofFile.Honest.Term (OnlineReturn)
open OnBytes.FrontRoad (PartsHeld)
open OnBytes.Maker (RDT)
open VerifiableInference.Desc (Chain KindName Block)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open _root_.Run (ckP)
open P5J

local instance (priority := high) onlineStopsOfK8Instance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) onlineStopsOfK8Instance2 {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

section General
variable {S Cl V W Y : Type}

/-- **K8's debt**: PartsHeld's clause, at the halves of kind K8 alone. -/
def K8Clause (P : V → Prop) (see : V → Option V) (hs : List (Placed V W Y))
    (bs : List (Block S Cl)) (ds : List RDT) : Prop :=
  ∀ v, P v → ∀ (A : List (Block S Cl)) (b : Block S Cl) (B : List (Block S Cl)), bs = A ++ b :: B →
    ∀ g, (hs.find? fun g => g.place == b.place) = some g → g.place.kind = KindName.K8 →
    ∀ (A' : List (Part V W Y)) (p : Part V W Y) (B' : List (Part V W Y)), g.parts = A' ++ p :: B' →
      (∀ u l o, p.hid u l o = none) ∨
        StopDebt (ckP .two) (· == some Why.hid) (see v) p
          ((((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length).drop
            (A'.map (·.moves.length)).sum).take p.moves.length) p.hidShare.val

/-- **From no second stop outside K8, and K8's debt, to the parts' premise.** -/
theorem partsHeld_of_k8 {P : V → Prop} {see : V → Option V} {hs : List (Placed V W Y)}
    {bs : List (Block S Cl)} {ds : List RDT}
    (quiet : ∀ g ∈ hs, g.place.kind ≠ KindName.K8 → ∀ p ∈ g.parts, ∀ u l o, p.hid u l o = none)
    (k8 : K8Clause P see hs bs ds) : PartsHeld P see hs bs ds := by
  intro v hv A b B e g hg A' p B' e'
  by_cases hk : g.place.kind = KindName.K8
  · exact k8 v hv A b B e g hg hk A' p B' e'
  · exact Or.inl (quiet g (List.mem_of_find?_eq_some hg) hk p (by rw [e']; simp))

end General

section Term
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type}
variable {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place} {Fl : ProofFile.Honest.OnlineProverParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Tr X₀ Xh}
  {A : OnlineProverWithDescription FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Tr X₀ Xh} {G' : Sides A.F A.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh}
  {more : List (String × Bool)}

/-- The halves of the sessions' prover are the maker's. -/
theorem provG_first (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x Fl A G' more) :
    (provG Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H).first = A.H.first := by
  have e := sidesAt_prover hd.isTerm.2 G' ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)
  show ((sidesAt hd.isTerm.2 G').prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)).first = _
  rw [e]
  exact (show (G'.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)).first = (G'.prover A.H).first
    from rfl).trans (congrArg Prover.first hd.ring)

theorem provG_second (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x Fl A G' more) :
    (provG Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H).second = A.H.second := by
  have e := sidesAt_prover hd.isTerm.2 G' ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)
  show ((sidesAt hd.isTerm.2 G').prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)).second = _
  rw [e]
  exact (show (G'.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)).second = (G'.prover A.H).second
    from rfl).trans (congrArg Prover.second hd.ring)

/-- **The private stops' line at the number, from no second stop outside K8 and K8's debt at the two chains.** -/
theorem online_stops_of_k8 (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x Fl A G' more)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {xx : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) A.B (provG Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H) w₀ rc xx k = .ok R)
    (hn : ∀ L ∈ (sidesAt hd.isTerm.2 G').first, L.place.kind ≠ KindName.frame)
    (Pr : Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr → Prop)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a →
      ∀ tr, A.H.trace w.1 (instanceAsPlainRecord a) = some tr → Pr ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩)
    (quiet : ∀ side ∈ A.H.first ++ A.H.second, side.place.kind ≠ KindName.K8 →
      ∀ part ∈ side.parts, ∀ input front own, part.hid input front own = none)
    (k₁ : K8Clause Pr Face.own.sees A.H.first (descZ Zp Np cF).first.blocksInOrder.dropLast (dataZ Z).ds₁)
    (k₃ : K8Clause Pr Face.own.sees A.H.second (descZ Zp Np cF).second.blocksInOrder (dataZ Z).ds₃)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    PrivateStopsAtMost
      ((HonestProvers.ofThreeProvers (proversOf hT hL (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                (dataAtFiles flashProveData Z).P A.H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online (onlinePrivateStopsAt Z Zp Np cF A.B (sidesAt hd.isTerm.2 G') A.H) :=
  online_stops_at_term scope hr live hd hR hn Pr hP
    (by
      rw [provG_first Z Zp Np cF hd]
      exact partsHeld_of_k8 (fun g hg => quiet g (List.mem_append_left _ hg)) k₁)
    (by
      rw [provG_second Z Zp Np cF hd]
      exact partsHeld_of_k8 (fun g hg => quiet g (List.mem_append_right _ hg)) k₃)
    hT hL n

end Term

section Kinds
variable {files : PublicFiles}

/-- **The clause of SecondStopsAreK8s at one kind.** -/
def KindQuiet (returned : OnlineReturn files) (κ : KindName) : Prop :=
  ∀ side ∈ returned.H.first ++ returned.H.second, side.place.kind = κ →
    ∀ part ∈ side.parts, ∀ input front own, part.hid input front own = none

/-- **SecondStopsAreK8s, kind by kind.** -/
theorem secondStopsAreK8s_of_kinds {returned : OnlineReturn files}
    (h : ∀ κ, κ ≠ KindName.K8 → KindQuiet returned κ) : SecondStopsAreK8s returned :=
  fun side hs hk => h _ hk side hs rfl

/-- **A kind from its lot's halves**: where the returned sides of that kind lie in a list that has no second stop. -/
theorem kindQuiet_of_halves {returned : OnlineReturn files} {κ : KindName}
    {hs : List (Placed (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit)}
    (tie : ∀ side ∈ returned.H.first ++ returned.H.second, side.place.kind = κ → side ∈ hs)
    (quiet : ∀ h ∈ hs, ∀ p ∈ h.parts, ∀ u l o, p.hid u l o = none) : KindQuiet returned κ :=
  fun side hm hk part hp input front own => quiet side (tie side hm hk) part hp input front own

end Kinds

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.partsHeld_of_k8
#print axioms VerifiableInference.Compilation.online_stops_of_k8
#print axioms VerifiableInference.Compilation.secondStopsAreK8s_of_kinds
#print axioms VerifiableInference.Compilation.kindQuiet_of_halves
