-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03SlotsHeadAt.lean: THE BUILT SEGMENT 24 HAS THE OUTPUT HEAD's PLACE's NUMBER OF SLOTS, AT THE CLOSED CONSTANT. The like of Johnson/P5J/K03SlotsAt.lean for the head's link, and for the digits' lookup at the other 24.
  built_ns_head_plain: where the plain road returns Z, with attention's segments: the built segment 2 * NGr bears the head's plan's number X.H.ns. (built_head_ns (Johnson/Desc/ProofFile/Law/HeadNs.lean) says it of THE LAST built segment; here it is said BY ITS NUMBER: the fifth part of the same lemma's answer whose fourth part gives the segments 2 g and 2 g + 1.)
  lookAt_ns_head: at p4 and twelve groups: lookAt's place at link 24, at the calls' and at the digits' lookup alike, has X.H.ns slots: by lookAt's make.
  k03_slots_head_look: under the head: (𝔇.built[24]?).map (·.ns) = some x.ns at lookAt's place (either lookup) · k03_slots_head: the same at the head's own place x (its field headAt: lookAt's place with its shape laid anew).
  lookAt_ns_any · k03_slots_look_any: K03SlotsAt's lookAt_ns | k03_slots_look AT EITHER LOOKUP (there: the calls' alone), l < 24: lookAt lays the same number of slots in both arms.
SO: at all 25 written links, at the calls' and at the digits' lookup: the built segment's number of slots is lookAt's place's.

Limits. One equation of numbers at each link. The head is a premise; a member of it is proved at the second hash function OnBytes.secondHashFunction, at two written sets of public files VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap, in the side library (AtFullSide/Top/: headMember_zFull, headMember_zGap); at other files or hashes none is shown.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03SlotsAt
import Johnson.Desc.First.Look.K3CallerHead

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
open VerifiableInference.Desc.First.Look (Place lookAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}

/-- Where the plain road returns the public part Z: the built segment 2 * NGr bears the head's plan's
number of slots. -/
theorem built_ns_head_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (h4 : Z.p.X.p4 = true) :
    (Z.p.built.links[2 * Z.p.X.NGr]?).map (·.ns) = some Z.p.X.H.ns := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [h4] at h₀
  obtain ⟨_, _, _, _, pH⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨ar, e⟩ := (Meaning.built_at hB).2 (2 * Z.p.X.NGr) _ pH
  rw [e]
  rfl

/-- lookAt's place's number of slots at the head's link, at either lookup. -/
theorem lookAt_ns_head {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {d : Bool}
    {y : Place} (hy : lookAt X 24 d = some y) : y.ns = X.H.ns := by
  have hs : (if X.p4 = true then 2 else 1) = 2 := by rw [h4]; rfl
  unfold lookAt at hy
  dsimp only at hy
  rw [hs, hN] at hy
  simp only [show ((24 : ℕ) == 2 * 12) = true from rfl, if_true] at hy
  split at hy
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hy
    rfl
  · obtain rfl := Option.some.inj hy
    rfl

/-- **The built segment 24's number of slots is lookAt's place's**, at either lookup. -/
theorem k03_slots_head_look (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {d : Bool} {y : Place}
    (hy : lookAt (At.X Zp) 24 d = some y) :
    ((h.toAtMg.𝔇 h.𝔇).built[24]?).map (·.ns) = some y.ns := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  have k := built_ns_head_plain h.laid.pub h4
  have hN' : Zp.p.X.NGr = 12 := hN
  rw [hN'] at k
  show (Zp.p.built.links[24]?).map (·.ns) = some y.ns
  rw [lookAt_ns_head h4 hN hy]
  exact k

/-- **The same at the head's own place.** -/
theorem k03_slots_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ((h.toAtMg.𝔇 h.𝔇).built[24]?).map (·.ns) = some x.ns := by
  have hx := h.headAt
  unfold VerifiableInference.Desc.Kinds.Head.Law.headAt at hx
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  rw [show (if (At.X Zp).p4 = true then 2 else 1) = 2 by rw [h4]; rfl, hN] at hx
  obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', -, rfl⟩ := Option.map_eq_some_iff.1 hx
  have k := k03_slots_head_look h (d := false) (y := x') h1
  exact k

/-- lookAt's place's number of slots in front of the head's link, at either lookup. -/
theorem lookAt_ns_any {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ} (hl : l < 24)
    {d : Bool} {y : Place} (hy : lookAt X l d = some y) :
    (l % 2 = 0 → ∃ hp, X.G[l / 2]? = some hp ∧ y.ns = hp.ns) ∧
      (l % 2 = 1 → ∃ a, X.A[l / 2]? = some a ∧ y.ns = a.ns) := by
  have hs : (if X.p4 = true then 2 else 1) = 2 := by rw [h4]; rfl
  unfold lookAt at hy
  dsimp only at hy
  rw [hs, hN] at hy
  split at hy
  · rename_i hc
    have : l = 2 * 12 := by simpa using hc
    omega
  · split at hy
    · rename_i he
      have he' : l % 2 = 0 := by simpa using he
      obtain ⟨hp, hG, hy⟩ := Option.bind_eq_some_iff.1 hy
      refine ⟨fun _ => ⟨hp, hG, ?_⟩, fun h1 => by omega⟩
      split at hy
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hy
        rfl
      · obtain rfl := Option.some.inj hy
        rfl
    · rename_i he
      have he' : l % 2 ≠ 0 := by simpa using he
      obtain ⟨a, hA, hy⟩ := Option.bind_eq_some_iff.1 hy
      refine ⟨fun h0 => absurd h0 he', fun _ => ⟨a, hA, ?_⟩⟩
      split at hy
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hy
        rfl
      · obtain rfl := Option.some.inj hy
        rfl

/-- **The built segment l's number of slots is lookAt's place's**, l < 24, at either lookup. -/
theorem k03_slots_look_any (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 24)
    {d : Bool} {y : Place} (hy : lookAt (At.X Zp) l d = some y) :
    ((h.toAtMg.𝔇 h.𝔇).built[l]?).map (·.ns) = some y.ns := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨⟨hp, hG⟩, a, hA, -⟩ := Meaning.scope_plans24 h.scope h.reads h.pubOne (l / 2) (by omega)
  obtain ⟨e0, e1⟩ := lookAt_ns_any h4 hN hl hy
  show (Zp.p.built.links[l]?).map (·.ns) = some y.ns
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

end P5J

#print axioms P5J.built_ns_head_plain
#print axioms P5J.lookAt_ns_head
#print axioms P5J.k03_slots_head_look
#print axioms P5J.k03_slots_head
#print axioms P5J.lookAt_ns_any
#print axioms P5J.k03_slots_look_any
