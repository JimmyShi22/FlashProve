-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FitsMsBuilt.lean: TWO CLOSED SENTENCES ON EVERY BUILT SEGMENT's
STRUCTURE OF THE APPROXIMATE RANGE PROOF, AS THEOREMS IN THE GOALS' SCOPE: "THE SHAPES FIT THE
MATRICES" (`Fits`, OnBytes/Tie/Pv/Tail/EndSame.lean) AND "EACH SHAPE HAS A THIRD OF ITS MATRIX's
ROWS OF CELLS, ROUNDED UP, AS ITS ROWS OF SYMBOLS" (`MsPlan`, HmsAtFront.lean); AND SO THE FIELD hmS
(of `EqTake`, ExpsAt.lean, and of `NumbersOk`) AT WHAT IS FIXED AT EVERY STATE REACHED
IN FRONT OF EVERY ONE OF THE 25 BATCHINGS, WITH NO CLOSED PREMISE LEFT. Statements and proofs:
calls.

  `public_of_pub`: the maker's return holds what `Verify.publicOf` returns of the same three files
    (at the second hash function).
  `Fits` at each plan's structure in what publicOf returns LIES: `both_layers`,
    `both_attention`, `both_head` (Johnson/Desc/Sound/K8Tests/PlanFitsOfPublic.lean): called, not
      typed again.
  `fits_built`, `ms_built`: **l < 25; Xl the blank letters' built segment at l ⊢ Fits Xl.tl; MsPlan
    Xl.tl.** `MsPlan`: `public_G_mS`, `public_A_mS`, `public_H_mS`. The carrying:
    `IM.ground_tails`.
  `fits_links`: **the same at the maker's own list: l < 25; Z.p.built.links[l]? = some X ⊢ Fits
    X.tl** (what a closed test on that list would ask).
  `hmS_whole`: **the field hmS at fixed9 (phiAll u ψ) s', s' reached at the batching's front of a
    written stretch: from the scope, "reached", an opening O and the built segment (e3).**
Limits. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.HmsAtFront
import Johnson.Road.K4.Plan.ShapeRowsG
import Johnson.Desc.First.Att.Door.Law.K5ShpOfPlan
import Johnson.Desc.Kinds.Law.HeadPlanMs
import Johnson.Desc.Sound.K8Tests.PlanFitsOfPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (Fits)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.PlanWritten (publicOfO_older)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The maker's return holds what publicOf returns. -/
theorem public_of_pub {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z) :
    Verify.publicOf pol KL (some lay) = .ok Z.p.X :=
  (publicOfO_older pol KL (some lay)).symm.trans (ProofFile.Law.pub_public hZ)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- An entry of the built segments with their routines exchanged has the structure of the entry that
it stems from. -/
theorem zip_tl {bs ls : Array LinkH} {j : ℕ} {Y : LinkH}
    (h : (bs.zipWith (fun b l => { b with run := l.run }) ls)[j]? = some Y) :
    ∃ b, bs[j]? = some b ∧ Y.tl = b.tl := by
  rw [Array.getElem?_zipWith] at h
  cases hb : bs[j]? with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases hx : ls[j]? with
    | none =>
      rw [hx] at h
      cases h
    | some y =>
      rw [hx] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl⟩

/-- The built segment's structure is one of the 25 plans'. -/
theorem built_plan (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {l : ℕ} (hl : l < 25) {Xl : LinkH}
    (e3 : G₀.built[l]? = some Xl) :
    (∃ (g : ℕ) (hp : Layer.HPlan2), Z.p.X.G[g]? = some hp ∧ Xl.tl = hp.tl) ∨
      (∃ (g : ℕ) (a : Attention.Plan), Z.p.X.A[g]? = some a ∧ Xl.tl = a.seam.tl) ∨
      Xl.tl = Z.p.X.H.tl := by
  have eW : G₀.W = Z.p.X := ProofFile.Law.blankBy_W hG
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨y, q, t, _⟩ := (IM.ground_tails hS hR hZ hG).2
    obtain rfl : y = Xl := Option.some.inj (q.symm.trans e3)
    exact Or.inr (Or.inr (by rw [t, eW]))
  · obtain ⟨hp, a, y, y', hGg, hAg, q, t, _, _, _, _, q', t', _⟩ :=
      (IM.ground_tails hS hR hZ hG).1 (l / 2) (by omega)
    rw [eW] at hGg hAg
    rcases Nat.mod_two_eq_zero_or_one l with ev | od
    · have em : 2 * (l / 2) = l := by omega
      rw [em] at q
      obtain rfl : y = Xl := Option.some.inj (q.symm.trans e3)
      exact Or.inl ⟨_, hp, hGg, t⟩
    · have em : 2 * (l / 2) + 1 = l := by omega
      rw [em] at q'
      obtain rfl : y' = Xl := Option.some.inj (q'.symm.trans e3)
      exact Or.inr (Or.inl ⟨_, a, hAg, t'⟩)

/-- **Fits AT EVERY BUILT SEGMENT.** -/
theorem fits_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {l : ℕ} (hl : l < 25) {Xl : LinkH}
    (e3 : G₀.built[l]? = some Xl) : Fits Xl.tl := by
  have hX := public_of_pub hZ
  rcases built_plan hS hR hZ hG hl e3 with ⟨g, hp, h1, e⟩ | ⟨g, a, h1, e⟩ | e
  · rw [e]
    exact (LT28.K8Tests.both_layers hX h1).1
  · rw [e]
    exact (LT28.K8Tests.both_attention hX h1).1
  · rw [e]
    exact (LT28.K8Tests.both_head hX).1

/-- **MsPlan AT EVERY BUILT SEGMENT.** -/
theorem ms_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {l : ℕ} (hl : l < 25) {Xl : LinkH}
    (e3 : G₀.built[l]? = some Xl) : MsPlan Xl.tl := by
  have hX := public_of_pub hZ
  rcases built_plan hS hR hZ hG hl e3 with ⟨g, hp, h1, e⟩ | ⟨g, a, h1, e⟩ | e
  · rw [e]
    exact OnBytes.Road.K4.Plan.public_G_mS hX g hp h1
  · rw [e]
    exact H2K5.Door.public_A_mS hX g a h1
  · rw [e]
    exact VerifiableInference.Desc.Kinds.Head.Law.InScope.public_H_mS hX

/-- **Fits AT THE MAKER's OWN LIST.** -/
theorem fits_links (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {l : ℕ} (hl : l < 25) {X : LinkH}
    (hX : Z.p.built.links[l]? = some X) : Fits X.tl := by
  have hb : ∃ Xl, G₀.built[l]? = some Xl := by
    by_cases h24 : l = 24
    · subst h24
      obtain ⟨y, q, _⟩ := (IM.ground_tails hS hR hZ hG).2
      exact ⟨y, q⟩
    · obtain ⟨_, _, y, y', _, _, q, _, _, _, _, _, q', _⟩ :=
        (IM.ground_tails hS hR hZ hG).1 (l / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one l with ev | od
      · exact ⟨y, by rw [← (by omega : 2 * (l / 2) = l)]; exact q⟩
      · exact ⟨y', by rw [← (by omega : 2 * (l / 2) + 1 = l)]; exact q'⟩
  obtain ⟨Xl, e3⟩ := hb
  obtain ⟨links, eb⟩ := _root_.Meaning.K2.blank_built hG
  obtain ⟨X', x1, x2⟩ := zip_tl (eb ▸ e3)
  obtain rfl : X' = X := Option.some.inj (x1.symm.trans hX)
  rw [← x2]
  exact fits_built hS hR hZ hG hl e3

end

variable {β : Type} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE FIELD hmS, AT ALL 25: FROM THE SCOPE, "REACHED", AN OPENING O AND e3.** -/
theorem hmS_whole (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) (hl : x.1 < 25) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2) (z, s'))
    (u : HTailF2) (ψ : S → β) :
    ∀ tlb, (pi8 (fixed9 (phiAll u ψ) s').1).1 = some tlb → ∀ mu, mu < tlb.NM →
      (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m :=
  hmS_at hS hR O hx e3 h (ms_built hS hR O.pub O.blank hl e3)
    (fits_built hS hR O.pub O.blank hl e3) u ψ

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.public_of_pub
#print axioms VerifiableInference.Desc.LinkJoin.zip_tl
#print axioms VerifiableInference.Desc.LinkJoin.built_plan
#print axioms VerifiableInference.Desc.LinkJoin.fits_built
#print axioms VerifiableInference.Desc.LinkJoin.ms_built
#print axioms VerifiableInference.Desc.LinkJoin.fits_links
#print axioms VerifiableInference.Desc.LinkJoin.hmS_whole
