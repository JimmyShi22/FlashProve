-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/KindsAtPure.lean: THE SIX FIELDS OF `KindsRun` (LotsAtPure.lean) PAID AT THE
SEATED LOTS' OWN BLOCKS, at both readings of "heard" (the lookup on the calls: `S.lookHeard?`; on
the digits: `heardD`), AND SO THE ROAD "WHO PAYS K3RanAt" AT `onlineDescription`, WITH NO PREMISE OUTSIDE ITS
CONCLUSION. Definitions, and theorems with their proofs.

WHOSE LAWS ARE SPENT: K3: theStated_runs_calls | _digits (Johnson/Top/H/K3StatedRuns.lean) · K4:
k4C_runsFo (CarriesFoK4.lean) · K5: with_join_step | runsK_step (RunsStep.lean; general in the
seat), through SeatN.lean's runN_ok · K6: k6_have (HeadRunsCarry.lean) · K8: carries_shape_look |
_digits (Johnson/Desc/First/TailClaims/EquationsAtS.lean) · K11: run_carries_look | _digits
(RunCarries.lean) · K9: callsK9G (ReadingsAtK9.lean), k9_makerMono (GuardAtDriver.lean) · that
`onlineDescription` is `onlineDescriptionFromPublicPart` at the seated seat: descPure_made
(Johnson/Desc/ProofFile/Law/MakerPublic.lean).

  `k3RunsLook` … `k8RunsDigits`: the fields. `kindsRunLook`, `kindsRunDigits`: all six.
  `RoadAtN hd o Z F`: `ranAtPureZ`'s conclusion at the seated seat.
  **`ranAtDescPureNLook`, `ranAtDescPureNDigits`**: `onlineDescription o pol lay KL = .ok F` gives the public
    part Z that the road makes of the three files, and `RoadAtN … o Z F`.

Limits. Frame's laws: no error; nothing on soundness. "PAID" IS SAID OF `LotsCarry`'s FIELDS. WHAT
STANDS BETWEEN THESE THEOREMS AND A SENTENCE WITH CONTENT AT A REAL SIZE: (1) `onlineDescription … = .ok F`
(a run's word) · (2) INSIDE THE CONCLUSION, link by link: that the hearing blocks behind b step
where their tests on the plan say yes (empty for the lookup on the digits but at the head's link) ·
(3) `F.run … = true` (a run's word) · (4) INSIDE `RanUpTo` | `RanAllUpTo`: that the record behind
b's decision holds something as heard, and a ledger with its sizes. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.LotsAtPure
import Johnson.Desc.First.K9x.ReadingsAtK9
import Johnson.Top.H.K3StatedRuns
import Johnson.Desc.First.Att.Claims.RunsStep
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.First.TailClaims.EquationsAtS
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open ProofFile (Pub Cl Inst pureSeat onlineDescription pureRoad)

variable (hd : S → Option Forest.Heard)

/-- Marking one owed claim as added carries. -/
theorem paidCarriesN (hp : ∀ s G, hd (S.putFork s G) = hd s) (s : S) (F : Fork) (i : Nat)
    (hF : s.fork? = some F) : CF hd s (s.putFork (F.paid i)) :=
  carriesFoOfLater _ _ _ _ (fun g hg => by rw [hp]; exact hg) fun F' hF' => by
    obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    exact ⟨F.paid i, S.fork_putFork s F _ hF, OnBytes.PscRun.paid_later F i⟩

theorem hpLookN (s : S) (G : Fork) : (S.putFork s G).lookHeard? = s.lookHeard? :=
  S.look_putFork s G

theorem hpDigitsN (s : S) (G : Fork) : heardD (S.putFork s G) = heardD s := by
  show (s.putFork G).tl?.bind (·.heard) = s.tl?.bind (·.heard)
  rw [tl_putFork']

/-! ## K3 -/

theorem k3RunsLook (Z : Pub) :
    ∀ G, ∀ b ∈ (K3Lot.lot Z).hearC G, b.RunsStep (CF S.lookHeard?) := by
  intro G b hb
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hb
  exact OnPublicFiles.theStated_runs_calls _ _ _ _ _ _ b hx

theorem k3RunsDigits (Z : Pub) : ∀ G, ∀ b ∈ (K3Lot.lot Z).hearC G, b.RunsStep (CF heardD) := by
  intro G b hb
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hb
  exact OnPublicFiles.theStated_runs_digits _ _ _ _ _ _ b hx

/-! ## K5 -/

theorem k5Runs (hp : ∀ s G, hd (S.putFork s G) = hd s) (Z : Pub) :
    ∀ G, ∀ b ∈ (H2K5.lotN Z).hearC G, b.RunsStep (CF hd) := by
  intro G b hb
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hb
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 hb'
  intro c hc n s cl s' h
  have hc' : c ∈ First.Att.P.runsN A := hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨l, hl, _⟩ := First.Att.P.runN_ok h
  rcases K5Law.with_join_step _ _ (K5Law.runsK_step _ _) r hr n s l s' hl with
    rfl | ⟨F, g, hF, _, rfl⟩
  · exact (preCF hd).refl _
  · exact paidCarriesN hd hp s F _ hF

/-! ## K6 -/

theorem k6Runs (hp : ∀ s G, hd (S.putFork s G) = hd s) (Z : Pub) :
    ∀ G, ∀ b ∈ (P4.k6Lot Z).hearC G, b.RunsStep (CF hd) := by
  intro G b hb
  have hb' : ((P4.headBefore Z G).bind fun ms =>
      Kinds.Head.seatedClaims G.W (G.built.size - 1) ms) = some b := Option.mem_toList.1 hb
  obtain ⟨ms, _, hs⟩ := Option.bind_eq_some_iff.1 hb'
  obtain ⟨b6, h6, rfl⟩ := Option.map_eq_some_iff.1 hs
  intro c hc n s cl s' h
  exact Kinds.Head.Law.k6_have (CF hd) G.W _ (preCF hd).refl
    (fun s F g hF _ => paidCarriesN hd hp s F _ hF) b6 h6 c hc n s (cl, s') h

/-! ## K8 -/

/-- What a yes of K8's one run at the record is. -/
theorem k8RunIs (n : Nat) (s : S) (cl : List Claim) (s' : S)
    (h : First.K8.atRecord (fun p : First.TailClaims.K8Part =>
      (First.TailClaims.equations (p.F.nClaim + n) p.tl p.funs p.F).map fun x =>
        (x.2.2, { p with tl := x.1, F := x.2.1 })) s = .ok (cl, s')) :
    ∃ (F F1 : Fork) (tl tl' : HTailF2) (funs : Array HFun), s.fork? = some F ∧ s.tl? = some tl ∧
      First.TailClaims.equations (F.nClaim + n) tl funs F = .ok (tl', F1, cl) ∧
      s' = (s.putTl tl').putFork F1 := by
  unfold First.K8.atRecord at h
  split at h
  · exact nomatch h
  · rename_i q hq
    obtain ⟨y, hy, e⟩ := mapOk h
    obtain ⟨x, hx, rfl⟩ := mapOk hy
    obtain ⟨w, hw, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨funs, _, rfl⟩ := Option.map_eq_some_iff.1 hq
    obtain ⟨tl, ht, hw⟩ := Option.bind_eq_some_iff.1 hw
    obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨tl', F1, cls⟩ := x
    obtain rfl : cls = cl := congrArg Prod.fst e
    exact ⟨F, F1, tl, tl', funs, hF, ht, hx, (congrArg Prod.snd e).symm⟩

theorem k8RunsLook (Z : Pub) :
    ∀ G, ∀ b ∈ (ProofFile.P1K8.lot Z).hearC G, b.RunsStep (CF S.lookHeard?) := by
  intro G b hb
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hb
  intro c hc n s cl s' h
  obtain rfl := List.mem_singleton.1 hc
  obtain ⟨F, F1, tl, tl', funs, hF, -, hx, he⟩ := k8RunIs n s cl s' h
  exact First.TailClaims.Law.carries_shape_look hF he hx

theorem k8RunsDigits (Z : Pub) :
    ∀ G, ∀ b ∈ (ProofFile.P1K8.lot Z).hearC G, b.RunsStep (CF heardD) := by
  intro G b hb
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hb
  intro c hc n s cl s' h
  obtain rfl := List.mem_singleton.1 hc
  obtain ⟨F, F1, tl, tl', funs, hF, ht, hx, he⟩ := k8RunIs n s cl s' h
  exact First.TailClaims.Law.carries_shape_digits hF ht he hx

/-! ## All six -/

theorem kindsRunLook (Z : Pub) : KindsRun S.lookHeard? Z :=
  ⟨k3RunsLook Z, k4Runs OnBytes.Desc.First.K4.keepsIn_look Z, k5Runs _ hpLookN Z,
    k6Runs _ hpLookN Z, k8RunsLook Z, k11RunsLook Z⟩

theorem kindsRunDigits (Z : Pub) : KindsRun heardD Z :=
  ⟨k3RunsDigits Z, k4Runs OnBytes.Desc.First.K4.keepsIn_digits Z, k5Runs _ hpDigitsN Z,
    k6Runs _ hpDigitsN Z, k8RunsDigits Z, k11RunsDigits Z⟩

theorem lotsCarryLook (o : ProofFile.SecondHashFunctionArgument) (Z : Pub) :
    LotsCarry (CF S.lookHeard?) (QN Z) (pureSeat o Z) :=
  lotsCarryAtPure _ o Z (callsK9G _ setLeavesLook) (kindsRunLook Z)

theorem lotsCarryDigits (o : ProofFile.SecondHashFunctionArgument) (Z : Pub) :
    LotsCarry (CF heardD) (QN Z) (pureSeat o Z) :=
  lotsCarryAtPure _ o Z (callsK9G _ setLeavesDigits) (kindsRunDigits Z)

/-! ## At `onlineDescription` -/

/-- What the road concludes at a description F that is made at the public part Z, AT A READING hd OF
"heard": `ranAtPureZ`'s conclusion at the seated seat. WHOEVER QUOTES IT QUOTES THE READING WITH IT:
at the reading that never hears anything `RanUpTo` and `RanAllUpTo` hold of everything, for nothing.
-/
def RoadAtN (o : ProofFile.SecondHashFunctionArgument) (Z : Pub) (F : FileDescription Inst) : Prop :=
  ∃ B c A B₂ H several c₀, ProofFile.baseOf Z (pureSeat o Z) = .ok B ∧
    F = ProofFile.fileDescBy o pureRoad.links Z A B₂ (fun s => s) (ProofFile.startS Z) c ∧
    First.firstChainWithoutReplyGuard H (ProofFile.subsOf Z) several = some c₀ ∧
    c = c₀.guarded H.same First.hearsReply ∧
    HIs Z (pureSeat o Z) B H ∧
    (∀ L ∈ c₀.links, ∀ M ∈ L.hear, SeatedAs (pureSeat o Z) B M) ∧
    (∀ (x : Inst) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      ∀ n y, foldBlocks 0 (c₀.blocksInOrder.take n) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
          (withEmptySealRound v₁).opened = .ok y →
        foldBlocks 0 (c.blocksInOrder.take n) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
          (withEmptySealRound v₁).opened = .ok y) ∧
    ∀ (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl), c₀.links = Ls₁ ++ L :: Ls₂ →
    ∀ (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
      (∀ x ∈ h₂, x.planOk = true → x.Steps (CF hd)) →
    ∀ (x : Inst) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      ∃ y ∈ (ProofFile.subsOf Z).zipIdx, First.linkAt H y.2 y.1 = some L ∧
        ∃ m c', foldBlocks 0 (c₀.upToLink Ls₁) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened =
            .ok (m, behindOf (c₀.upToLink Ls₁) (withEmptySealRound v₁).rounds, c') ∧
          ∃ t t₁ u₀ z u e cls,
            Traced (CF hd) (QN Z (First.batchPlaceOf y.2 y.1)) L h₁ b 0 m
              (behindOf (c₀.upToLink Ls₁) (withEmptySealRound v₁).rounds) c' t t₁ u₀ z u e cls ∧
            RanUpTo S.fork? hd _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls ∧
            RanAllUpTo S.fork? hd _root_.Fo.Later OnBytes.PscRun.Sized L t₁ e cls

/-- **THE ROAD AT `onlineDescription` OVER THE VARIANT's GROUND, at what the lookup on the calls was heard to
return.** -/
theorem ranAtDescPureNLook (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst)
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧ RoadAtN S.lookHeard? o Z F := by
  obtain ⟨Z, hZ, hF⟩ := ProofFile.Law.descPure_made h
  exact ⟨Z, hZ, ranAtPureZ _ (QN Z) Z (pureSeat o Z) F hF (lotsCarryLook o Z)⟩

/-- The like at what the lookup on the digits was heard to return. -/
theorem ranAtDescPureNDigits (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst)
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧ RoadAtN heardD o Z F := by
  obtain ⟨Z, hZ, hF⟩ := ProofFile.Law.descPure_made h
  exact ⟨Z, hZ, ranAtPureZ _ (QN Z) Z (pureSeat o Z) F hF (lotsCarryDigits o Z)⟩

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.paidCarriesN
#print axioms VerifiableInference.Desc.K9.hpLookN
#print axioms VerifiableInference.Desc.K9.hpDigitsN
#print axioms VerifiableInference.Desc.K9.k3RunsLook
#print axioms VerifiableInference.Desc.K9.k3RunsDigits
#print axioms VerifiableInference.Desc.K9.k5Runs
#print axioms VerifiableInference.Desc.K9.k6Runs
#print axioms VerifiableInference.Desc.K9.k8RunIs
#print axioms VerifiableInference.Desc.K9.k8RunsLook
#print axioms VerifiableInference.Desc.K9.k8RunsDigits
#print axioms VerifiableInference.Desc.K9.kindsRunLook
#print axioms VerifiableInference.Desc.K9.kindsRunDigits
#print axioms VerifiableInference.Desc.K9.lotsCarryLook
#print axioms VerifiableInference.Desc.K9.lotsCarryDigits
#print axioms VerifiableInference.Desc.K9.ranAtDescPureNLook
#print axioms VerifiableInference.Desc.K9.ranAtDescPureNDigits
