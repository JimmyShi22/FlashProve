-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/StopsThru.lean: the private stops' premises pass from the base to the term.

1.  At one part read through: hid_thru, the moves' number, stopDebt_thru (by Part.stopAt_thru).
2.  At a list of sides read through: sidesQuiet_thru, kindQuiet_thru, k8Clause_thru: places, parts'
    numbers and shares stay.
3.  online_hid_of_k8_atBase: online_hid_of_k8_base with quiet and K8's debt stated at the base's
    halves, where each kind's stops are stated.
4.  No value of any premise is given here: nothing is said of any part's stops.
-/
import AtFullSide.T3.OnlineK8AtBase
import Johnson.Desc.ProofFile.Honest.ThruRun

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Prover Sides relAt AtHonest OnlineProverWithDescription Cells Coins Ready ready Local Face Placed Part StopDebt
  Why)
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput tableCoins)
open VerifiableInference.Desc (Chain KindName FileDescription Block)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD RDT)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles NamedFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open _root_.Run (ckP)
open P5J

local instance (priority := high) stopsThruPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) stopsThruValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) stopsThruDefault : Inhabited RunValue := ⟨fun _ => 0⟩

section Parts
variable {S Cl V V' W W' Y : Type}

/-- A part's second stop, read through, reads its input through. -/
theorem hid_thru (see : V' → V) (wit : W' → W) (p : Part V W Y) (u : V')
    (l o : List Fmt.Drawn) : (p.thru see wit).hid u l o = p.hid (see u) l o := rfl

/-- Its rounds are as many. -/
theorem moves_length_thru (see : V' → V) (wit : W' → W) (p : Part V W Y) :
    (p.thru see wit).moves.length = p.moves.length :=
  List.length_map ..

/-- **A part's debt on its stops passes through.** -/
theorem stopDebt_thru (C : _root_.Run.PQ.CK) (sp : Option Why → Bool) (see : V' → V) (wit : W' → W)
    (p : Part V W Y) (v' : Option V') (dsp : List RDT) (q : ℝ≥0∞)
    (h : StopDebt C sp (v'.map see) p dsp q) : StopDebt C sp v' (p.thru see wit) dsp q := fun fr => by
  simp only [Part.stopAt_thru see wit p (v'.map see) v' rfl]
  exact h fr

/-- **No second stop at some sides: the same at them read through.** -/
theorem sidesQuiet_thru (see : V' → V) (wit : W' → W) (hs : List (Placed V W Y))
    (kind : KindName → Prop)
    (quiet : ∀ side ∈ hs, kind side.place.kind → ∀ part ∈ side.parts, ∀ input front own,
      part.hid input front own = none) :
    ∀ side ∈ hs.map (Placed.thru see wit), kind side.place.kind → ∀ part ∈ side.parts,
      ∀ input front own, part.hid input front own = none := by
  intro side hside hk part hpart input front own
  obtain ⟨s₀, h₀, rfl⟩ := List.mem_map.1 hside
  obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hpart
  exact quiet s₀ h₀ hk p₀ hp₀ (see input) front own

/-- **K8's debt passes through.** -/
theorem k8Clause_thru {P : V → Prop} {P' : V' → Prop} {s : V → Option V} {s' : V' → Option V'}
    (f : V' → V) (wit : W' → W) (hP : ∀ v, P' v → P (f v)) (hs' : ∀ v, (s' v).map f = s (f v))
    {hs : List (Placed V W Y)} {bs : List (Block S Cl)} {ds : List RDT}
    (clause : K8Clause P s hs bs ds) : K8Clause P' s' (hs.map (Placed.thru f wit)) bs ds := by
  intro v hv A b B e g hg hk A' p B' e'
  rw [List.find?_map] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := Option.map_eq_some_iff.1 hg
  obtain ⟨A₀, rest, hsplit, rfl, hrest⟩ := List.map_eq_append_iff.1 e'
  obtain ⟨p₀, B₀, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hrest
  have hlen : ((A₀.map (Part.thru f wit)).map (·.moves.length)).sum =
      (A₀.map (·.moves.length)).sum := by
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left fun a _ => moves_length_thru f wit a)
  rcases clause (f v) (hP v hv) A b B e g₀ hg₀ hk A₀ p₀ B₀ hsplit with h | h
  · exact Or.inl fun u l o => h (f u) l o
  · refine Or.inr ?_
    rw [hlen, moves_length_thru]
    exact stopDebt_thru _ _ f wit p₀ (s' v) _ _ (by rw [hs' v]; exact h)

end Parts

section AtFiles
variable (files : PublicFiles) {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place}
  {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}

/-- The reader from the term's input to the base's. -/
abbrev termSees (files : PublicFiles) :
    Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Local FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Inst Cells :=
  Local.thru id (tableCoins files)

/-- No second stop at the base's sides: the same at the term's. -/
theorem quiet_at_term (kind : KindName → Prop)
    (quiet : ∀ side ∈ A.H.first ++ A.H.second, kind side.place.kind → ∀ part ∈ side.parts,
      ∀ input front own, part.hid input front own = none) :
    ∀ side ∈ (termProver files A).first ++ (termProver files A).second, kind side.place.kind →
      ∀ part ∈ side.parts, ∀ input front own, part.hid input front own = none := by
  have e : (termProver files A).first ++ (termProver files A).second =
      (A.H.first ++ A.H.second).map (Placed.thru (termSees files) (termSees files)) :=
    (List.map_append ..).symm
  rw [e]
  exact sidesQuiet_thru _ _ _ kind quiet

/-- **A kind that is quiet at the base is quiet at the term.** -/
theorem kindQuiet_thru (κ : KindName)
    (quiet : ∀ side ∈ A.H.first ++ A.H.second, side.place.kind = κ → ∀ part ∈ side.parts,
      ∀ input front own, part.hid input front own = none) :
    KindQuiet (A.thru id (tableCoins files) matrixInput.dummy) κ :=
  quiet_at_term files (· = κ) quiet

/-- **The private stops of the online prover at the named number**, from what the base's halves
owe: no second stop outside K8, and K8's debt, at the first and the last chain. -/
theorem online_hid_of_k8_atBase (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles files).EncodingRandomness} {xx : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Cells Unit Unit}
    (hR : ready (descZ A.Z Np cF) A.B (provG files A.Z Np cF A.B (termRows files hd) (termProver files A)) w₀ rc xx
      k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Pr : Local FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a →
      ∀ tr, (termProver files A).trace w.1 (instanceAsPlainRecord a) = some tr →
        Pr (termSees files ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩))
    (quiet : ∀ side ∈ A.H.first ++ A.H.second, side.place.kind ≠ KindName.K8 →
      ∀ part ∈ side.parts, ∀ input front own, part.hid input front own = none)
    (k₁ : K8Clause Pr Face.own.sees A.H.first (descZ A.Z Np cF).first.blocksInOrder.dropLast (dataZ files).ds₁)
    (k₃ : K8Clause Pr Face.own.sees A.H.second (descZ A.Z Np cF).second.blocksInOrder (dataZ files).ds₃) :
    HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a)
      (onlinePrivateStopsAt files A.Z Np cF A.B (termRows files hd) (termProver files A)) :=
  online_hid_of_k8_base files scope live hr hd hR hn (fun v => Pr (termSees files v)) hP
    (quiet_at_term files (· ≠ KindName.K8) quiet)
    (k8Clause_thru (termSees files) (termSees files) (fun _ h => h) (fun _ => rfl) k₁)
    (k8Clause_thru (termSees files) (termSees files) (fun _ h => h) (fun _ => rfl) k₃)

end AtFiles

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.hid_thru
#print axioms VerifiableInference.Compilation.moves_length_thru
#print axioms VerifiableInference.Compilation.stopDebt_thru
#print axioms VerifiableInference.Compilation.sidesQuiet_thru
#print axioms VerifiableInference.Compilation.k8Clause_thru
#print axioms VerifiableInference.Compilation.quiet_at_term
#print axioms VerifiableInference.Compilation.kindQuiet_thru
#print axioms VerifiableInference.Compilation.online_hid_of_k8_atBase
