-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HtinPaid.lean: THE FIELD htin OF THE LINK's TABLE AT THE PROOF FILE's
SEAT, THIRD FORM: `htin_left` (HtinLeft.lean) WITH `FrameFinds` PAID (FrameAtBehind.lean;
NamedOfBuilt.lean). What is left on the states: four facts, each a test of the table's own promise
or a law that lies; on the public part: four closed facts a link. Theorems. No text already in the library turns.

  `named_at_blank`: `named_of_made` at the blank letters' link (the built link but for its routine).
  `LinkPlanFits Z l Xl`: the four closed facts: sortsB says yes at the built link's planned arrays'
    looks · every planned array has an entry in the link's list of names · the link has at most
    three moments · one of its messages has mask rows. `linkPlanB`, `linkPlanFits_of_B`: the four
    as one test with code.
  `htin_paid`: **LinkPlanFits · N.groupAt x.1 = x.1 · hOn : ∀ a, on1 a → ‹reached behind the
    batching's entry› ∧ ledgerB a.1 = true ∧ ‹the open ledger has a coefficient for each slot› ∧
    membersHeld N ‹what is open there› a.1 = true ⊢ htin, to the letter, at own := N.group x.1.**
Limits. LinkPlanFits is shown at no plan here: four Bools a link, for an evaluation. In scope, at
secondHashFunction alone. No member. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.FrameAtBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers membersHeld)
open VerifiableInference.Desc.JoinAtBlocks
open Meaning.K2 (blank_built)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (linksW placesW nAt openAt)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem named_at_blank {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol ly KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : ℕ} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    ∀ (τ born : ℕ) (name : String), Xl.arrayOf[τ]? = some (born, name) →
      NamedHeld Z.first l Xl τ born name := by
  obtain ⟨links, e⟩ := blank_built hG
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  intro τ born name hx
  exact named_of_made hZ l (Z.p.built.links[l]'hl1) τ born name (Array.getElem?_eq_getElem hl1) hx

/-- Four closed facts on the public part, a link. -/
structure LinkPlanFits (Z : ProofFile.Pub) (l : ℕ) (Xl : LinkH) : Prop where
  sorts : sortsB (Xl.Fp.trees.toList.map look) Xl.tl = true
  names : Xl.Fp.trees.size ≤ Xl.arrayOf.size
  three : ∀ L, Z.first.shape.link[l]? = some L → reqMoments L ≤ 3
  mask : ∃ L, Z.first.shape.link[l]? = some L ∧
    (L.messages.any fun x => x.shape.maskRows != 0) = true

/-- The four as one test with code. -/
def linkPlanB (Z : ProofFile.Pub) (l : ℕ) (Xl : LinkH) : Bool :=
  sortsB (Xl.Fp.trees.toList.map look) Xl.tl && decide (Xl.Fp.trees.size ≤ Xl.arrayOf.size) &&
    (Z.first.shape.link[l]?).any fun L =>
      decide (reqMoments L ≤ 3) && L.messages.any fun x => x.shape.maskRows != 0

theorem linkPlanFits_of_B {Z : ProofFile.Pub} {l : ℕ} {Xl : LinkH} (h : linkPlanB Z l Xl = true) :
    LinkPlanFits Z l Xl := by
  unfold linkPlanB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases e : Z.first.shape.link[l]? with
  | none =>
    rw [e] at h3
    exact nomatch h3
  | some L =>
    rw [e] at h3
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h3
    exact ⟨h1, h2, fun L' h' => by rw [← Option.some.inj (e.symm.trans h')]; exact h3.1, L, e,
      h3.2⟩

/-- **htin, TO THE LETTER, AT A LINK OF THE SEAT: THIRD FORM.** -/
theorem htin_paid {α : Type} {Fr : Frame} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Lk : Link S Cl}
    (eL : c.links[x.1]? = some Lk) {Xl : LinkH} (e3 : Bs.G₀.built[x.1]? = some Xl)
    (hP : LinkPlanFits Z x.1 Xl) (N : Numbers) (hg : N.groupAt x.1 = x.1) (z : ProofFile.InstPub)
    (on1 : S × Fr.E.Str → Prop)
    (hOn : ∀ a, on1 a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) (z, a.1) ∧
        First.ledgerB a.1 = true ∧ (∀ G, a.1.fork? = some G → G.LS.size = G.ns) ∧
        membersHeld N (openAt linksW placesW (14 * x.1 + nAt x.1 + 3)) a.1 = true) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) Lk).map (·.move)) a.1 t [] →
      K9.totalIn (N.group x.1) t = true := by
  have hl : x.1 < 25 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.1 hl
  obtain ⟨L, hL, hM⟩ := hP.mask
  refine htin_left hS hR O hx eL e3 hP.sorts N hg z on1 fun a ha => ?_
  obtain ⟨r, lb, ls, mh⟩ := hOn a ha
  refine ⟨r, lb, ls, mh, fun p hp => ?_⟩
  exact frameFinds_behind hS hR O hl e3 (named_at_blank O.pub O.blank e3)
    (by rw [List.length_map, Array.length_toList]; exact hP.names) hL (hP.three L hL) hM
    (y := (z, a.1)) (by rw [← border_eq hx]; exact r) hp

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.named_at_blank
#print axioms VerifiableInference.Desc.LinkJoin.linkPlanFits_of_B
#print axioms VerifiableInference.Desc.LinkJoin.htin_paid
