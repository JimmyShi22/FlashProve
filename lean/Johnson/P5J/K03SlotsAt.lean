-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03SlotsAt.lean: THE LOOKUPS' LEDGER's DEBT «slots» AT THE 24 LINKS IN FRONT OF THE OUTPUT HEAD's, AT THE CLOSED CONSTANT: A THEOREM UNDER THE HEAD.
The ledger (AttOwedR | LayOwedR and their shorter forms) asks: (𝔇.built[l]?).map (·.ns) = some (P.ofPlace (Params.settingOf X.P.frame) false x).ns: the built segment's number of slots is the place's. The left side is the maker's built list, the right the public plan's number at the lookup's place.
  built_ns_att_plain: where the plain road returns Z, with attention's segments: the built segment 2 g + 1 bears attention's plan's a.ns. built_ns_plain (Johnson/Road/K4/Riders/BuiltNs.lean: the like for segment 2 g and hp.ns) WITH THE OTHER HALF OF THE SAME LEMMA's ANSWER: its proof, line for line, but for the component taken.
  lookAt_ns: at p4, twelve groups, l < 24: lookAt's place's number of slots is the group's plan's (l even) or attention's plan's (l odd): by lookAt's make.
  k03_slots_look: the debt at lookAt's place · k03_slots_lay · k03_slots_att: at layAt's | attAt's place (lookAt's with its shape laid anew: the number of slots is untouched): THE LEDGER's OWN TEXT.
𝔇.built is Zp.made.p.built.links and ProofFile.Pub.p is «made.p» by definition: one list.
Limits. It pays one debt at each of 24 places. Not at the head's link (there the ledger asks no
such debt of the calls). The head is a premise; a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction only because the head stands there: the two laws on the built list hold at every function in the second hash function's place.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03Terms
import Johnson.Road.K4.Riders.BuiltNs
import Johnson.Goal.Meaning.PlanNames
import Johnson.Desc.First.Look.K3CallerLayTests
import Johnson.Desc.First.Look.K3AttInst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open OnBytes.Model.Stages (LinkH SubPlanH)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.First.Look (Place lookAt layAt attAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : Place}

/-- Where the plain road returns the public part Z: the built segment 2 g + 1 bears the number of
slots of group g's attention's plan. -/
theorem built_ns_att_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (h4 : Z.p.X.p4 = true) {g : ℕ} {hp : Layer.HPlan2}
    {a : Attention.Plan} (hgp : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) :
    (Z.p.built.links[2 * g + 1]?).map (·.ns) = some a.ns := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [h4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨_, q1⟩ := p0 g _ _ s0 t0
  obtain ⟨ar, e⟩ := (Meaning.built_at hB).2 (2 * g + 1) _ q1
  rw [e]
  rfl

/-- lookAt's place's number of slots, in front of the head's link. -/
theorem lookAt_ns {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ} (hl : l < 24)
    {x : Place} (hx : lookAt X l false = some x) :
    (l % 2 = 0 → ∃ hp, X.G[l / 2]? = some hp ∧ x.ns = hp.ns) ∧
      (l % 2 = 1 → ∃ a, X.A[l / 2]? = some a ∧ x.ns = a.ns) := by
  have hs : (if X.p4 = true then 2 else 1) = 2 := by rw [h4]; rfl
  unfold lookAt at hx
  dsimp only at hx
  rw [hs, hN] at hx
  split at hx
  · rename_i hc
    have : l = 2 * 12 := by simpa using hc
    omega
  · split at hx
    · rename_i he
      have he' : l % 2 = 0 := by simpa using he
      obtain ⟨hp, hG, hx⟩ := Option.bind_eq_some_iff.1 hx
      simp only [Bool.false_eq_true, if_false] at hx
      obtain rfl := Option.some.inj hx
      exact ⟨fun _ => ⟨hp, hG, rfl⟩, fun h1 => by omega⟩
    · rename_i he
      have he' : l % 2 ≠ 0 := by simpa using he
      obtain ⟨a, hA, hx⟩ := Option.bind_eq_some_iff.1 hx
      simp only [Bool.false_eq_true, if_false] at hx
      obtain rfl := Option.some.inj hx
      exact ⟨fun h0 => absurd h0 he', fun _ => ⟨a, hA, rfl⟩⟩

/-- **slots, at lookAt's place.** -/
theorem k03_slots_look (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 24)
    {x : Place} (hx : lookAt (At.X Zp) l false = some x) :
    ((h.toAtMg.𝔇 h.𝔇).built[l]?).map (·.ns) =
      some (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).ns := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨⟨hp, hG⟩, a, hA, -⟩ := Meaning.scope_plans24 h.scope h.reads h.pubOne (l / 2) (by omega)
  obtain ⟨e0, e1⟩ := lookAt_ns h4 hN hl hx
  show (Zp.p.built.links[l]?).map (·.ns) = some x.ns
  rcases Nat.mod_two_eq_zero_or_one l with he | he
  · obtain ⟨hp', hG', en⟩ := e0 he
    have k := OnBytes.Road.K4.Riders.built_ns_plain h.laid.pub h4 hG' hA
    rw [show 2 * (l / 2) = l by omega] at k
    rw [en]
    exact k
  · obtain ⟨a', hA', en⟩ := e1 he
    have k := built_ns_att_plain h.laid.pub h4 hG hA'
    rw [show 2 * (l / 2) + 1 = l by omega] at k
    rw [en]
    exact k

/-- **slots, at the layers' calls: the ledger's own text.** -/
theorem k03_slots_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 24)
    {x : Place} (hx : layAt (At.X Zp) l = some x) :
    ((h.toAtMg.𝔇 h.𝔇).built[l]?).map (·.ns) =
      some (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).ns := by
  unfold layAt at hx
  split at hx
  · obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, rfl⟩ := Option.map_eq_some_iff.1 hx
    have k := k03_slots_look h hl h1
    exact k
  · cases hx

/-- **slots, at attention's calls: the ledger's own text.** -/
theorem k03_slots_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 24)
    {x : Place} {A : Attention.Shape} {tl : HTailF2} (hx : attAt (At.X Zp) l = some (x, A, tl)) :
    ((h.toAtMg.𝔇 h.𝔇).built[l]?).map (·.ns) =
      some (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).ns := by
  unfold attAt at hx
  split at hx
  · obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨a, -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rfl, -⟩ := Prod.mk.inj hx
    have k := k03_slots_look h hl h1
    exact k
  · cases hx

end P5J

#print axioms P5J.built_ns_att_plain
#print axioms P5J.lookAt_ns
#print axioms P5J.k03_slots_look
#print axioms P5J.k03_slots_lay
#print axioms P5J.k03_slots_att
