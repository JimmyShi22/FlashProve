-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/RoomRuns.lean: THE RUNS' SHARE BENEATH THE FIELDS batch AND
behind OF KeepShares (RoomKeepK9.lean's one premise hruns), IN THE GOALS'
SCOPE: PAID AT 24 OF THE 25 LINKS; AT THE HEAD's LINK ONE HALF IS OWED BY NAME.
  `hear_runs_stays`: THE NUMBER's HALF, AT ALL 25 LINKS: every hearing sub-protocol's runs leave the
    index masks' number: the relation `PileStays` at every lot's own sub-protocol
    (`lot_pile`), carried to the seats by
    `first_sits`, `chain_hear_alone`, `joined_runs`, `alone_runs`.
  `reach_yes`: whatever number is reached, every sub-protocol in front of it has accepted somewhere.
  `hruns_reached`: the runs' share at a link in front of whose batching a state is reached: THE
    STATEMENT's HALF at l < 24 by `hear_runs` (Johnson/IMR/LinkRest.lean) at "the
    statement stays", which `Quiet` gives; its premise "the link's first sub-protocol accepts
    somewhere" out of "reached".
  `field_batch_scope`, `field_behind_scope`: **the two fields, to the letter**, from the scope, the
    opening of the proof file's IOP as written in Lean, and hHead.
Limits. hHead IS OWED: at the head's link (l = 24) every hearing sub-protocol's runs leave the
statement: nine seats (K7 · K2 · K3 · K6 · K1 · K8 · K1 · K3 · K11), each with its maker's own lemma
on "quiet": no lemma joins them yet. In the goals' scope alone, at OnBytes.secondHashFunction alone. No
soundness statement.

-/
import Johnson.LPFK9R.RoomKeepK9
import Johnson.LPFK9R.PileByPlace
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl Lot Ground)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Tied
open Meaning.K2
open P1L20 (Hands2 KeepsAt outOfGroupsB nA)

/-- The statement stays. -/
def StS (s s' : S) : Prop := s'.st = s.st

theorem stS_refl (s : S) : StS s s := rfl

theorem stS_trans (a b c : S) (h : StS a b) (k : StS b c) : StS a c := Eq.trans k h

section
variable {T C : Type} {A B : T → T → Prop}

theorem runs_and {b : Block T C} (h1 : RunsKeep A b) (h2 : RunsKeep B b) :
    RunsKeep (fun s t => A s t ∧ B s t) b :=
  ⟨fun c hc n s y e => ⟨h1.1 c hc n s y e, h2.1 c hc n s y e⟩,
    fun c hc s t e => ⟨h1.2 c hc s t e, h2.2 c hc s t e⟩⟩

theorem runs_mono (h : ∀ s t, A s t → B s t) {b : Block T C} (k : RunsKeep A b) : RunsKeep B b :=
  ⟨fun c hc n s y e => h _ _ (k.1 c hc n s y e), fun c hc s t e => h _ _ (k.2 c hc s t e)⟩

end

/-- The two halves give the whole. -/
theorem stIx_runs {b : Block S Cl} (h1 : RunsKeep StS b) (h2 : RunsKeep PileStays b) :
    RunsKeep StIx b := runs_mono (fun _ _ q => ⟨q.1, q.2.2.1⟩) (runs_and h1 h2)

/-- Whatever number is reached, every sub-protocol in front of it has accepted somewhere. -/
theorem reach_yes {Q : Type} {ft : ℕ} {bs : List (Block S Cl)} {start : Q → S} :
    ∀ {k : ℕ} {x : Q × S}, Reach ft bs start k x → ∀ j < k, ∀ b, bs[j]? = some b →
      ∃ s₁ s₂, StepYes ft b s₁ s₂ := by
  intro k x h
  induction h with
  | zero z => intro j hj; omega
  | succ hr hb hy ih =>
    rename_i k z s s' b₀
    intro j hj b e
    by_cases hk : j = k
    · subst hk
      obtain rfl : b₀ = b := Option.some.inj (hb.symm.trans e)
      exact ⟨_, _, hy⟩
    · exact ih j (by omega) b e

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE NUMBER's HALF, AT ALL 25 LINKS**: the runs of a link's hearing sub-protocols leave the
rows on the table, the index masks' number and the stand. (The walk is `hear_runs_pile`'s,
at the relation itself.) -/
theorem hear_runs_stays (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk) : ∀ b ∈ Lk.hear, RunsKeep PileStays b := by
  intro b hb
  have h0 : Z.P.firstTree = 0 := pub_firstTree O.pub
  obtain ⟨j, hj, e'⟩ := List.getElem_of_mem hb
  have e : Lk.hear[j]? = some b := by rw [List.getElem?_eq_getElem hj, e']
  obtain ⟨Lk9, -, -, -, e9, -, -, -, -, -, -, -, -, -, -, -, -, hlen9, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk9 := Option.some.inj (eL.symm.trans e9)
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, -, e1, hn, -⟩ := hall l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e1)
  have hn' : Lk.hear.length = IM.nAt l := hn
  have hn9 : IM.nAt l ≤ 9 := by unfold IM.nAt; split <;> omega
  obtain ⟨k1, hk1⟩ : ∃ k1, (kindsBeforeBatching (IM.subAt l) (l == 0))[j]? = some k1 :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlen9]; exact hj)⟩
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨Lk', b0, e1', e2, Lt, hLt, b', hb', ep, hjn⟩ := IM.first_sits hS hR O l hl k1 hk1
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e1')
    obtain rfl : b = b0 := Option.some.inj (e.symm.trans e2)
    exact joined_runs pile_refl pile_trans hjn
      (lot_pile Z h0 Bs.G₀ hLt hb' (by rw [ep]; exact (hear_noframe hk1).1)
        (by rw [ep]; exact (hear_noframe hk1).2)).2
  · obtain ⟨h9, h10⟩ := IM.hear_plain hk1
    obtain ⟨Lk', b0, e1', e2, sp, -, Lt, hLt, b', hb', -, ep, hla⟩ :=
      IM.chain_hear_alone O.made O.places O.chain l (IM.subAt l) (IM.subs_scope hS hR O l hl) j k1
        hk1 h9 h10 ⟨by omega, by omega⟩
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e1')
    obtain rfl : b = b0 := Option.some.inj (e.symm.trans e2)
    exact alone_runs pile_refl hla
      (lot_pile Z h0 Bs.G₀ hLt hb' (by rw [ep]; exact (hear_noframe hk1).1)
        (by rw [ep]; exact (hear_noframe hk1).2)).2

/-- **THE RUNS' SHARE AT A LINK IN FRONT OF WHOSE BATCHING A STATE IS REACHED.** hHead: the
statement's half at the head's link: OWED. -/
theorem hruns_reached {Q : Type} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S)
    (hHead : ∀ Lk : Link S Cl, c.links[24]? = some Lk → ∀ b ∈ Lk.hear, RunsKeep StS b)
    {l : Nat} (hl : l < 25) {Lk : Link S Cl} (eL : c.links[l]? = some Lk) {k : ℕ} {x : Q × S}
    (hk : 14 * l + 2 < k) (hreach : Reach 0 c.blocksInOrder start k x) :
    ∀ b ∈ Lk.hear, RunsKeep StIx b := by
  intro b hb
  refine stIx_runs ?_ (hear_runs_stays hS hR O hl eL b hb)
  by_cases h24 : l = 24
  · subst h24
    exact hHead Lk eL b hb
  · refine hear_runs stS_refl stS_trans (fun _ _ q => q.1.1) hS hR O (by omega) eL
      (fun b₀ h0 => ?_) b hb
    have e0 := IM.hear_at_flat eL h0
    rw [IM.flatIx_scope hS hR O (by omega) 0] at e0
    obtain ⟨s₁, s₂, hy⟩ := reach_yes hreach (14 * l + 0 + 2) (by omega) b₀ e0
    obtain ⟨rs, gs, d⟩ := stepYes_decide hy
    exact ⟨s₁, rs, gs, s₂, d⟩

/-- **THE FIELD batch OF KeepShares, TO THE LETTER, IN THE GOALS' SCOPE.** -/
theorem field_batch_scope {Q : Type} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S)
    (hHead : ∀ Lk : Link S Cl, c.links[24]? = some Lk → ∀ b ∈ Lk.hear, RunsKeep StS b) :
    ∀ l < 25, ∀ (Lk : Link S Cl) p, c.links[l]? = some Lk → IM.k9At Z l = some p →
      KeepsAt c start (14 * l + nA l + 2)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p
          (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro l hl Lk p e _ z s s' hreach hy ho
  exact batch_keeps c start _ p Lk
    (hruns_reached hS hR O start hHead hl e (by unfold nA; split <;> omega) hreach)
    z s s' hreach hy ho

/-- **THE FIELD behind OF KeepShares, TO THE LETTER, IN THE GOALS' SCOPE.** -/
theorem field_behind_scope {Q : Type} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (start : Q → S)
    (hHead : ∀ Lk : Link S Cl, c.links[24]? = some Lk → ∀ b ∈ Lk.hear, RunsKeep StS b) :
    ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk → ∀ z s t,
      Reach 0 c.blocksInOrder start (14 * l + nA l + 3) (z, s) → Lk.runBehind s = .ok t →
      outOfGroupsB s = true → Hands2 s t := by
  intro l hl Lk e z s t hreach h ho
  exact behind_keeps Lk
    (hruns_reached hS hR O start hHead hl e (by unfold nA; split <;> omega) hreach) s t h ho

end

end LPFK9

#print axioms LPFK9.hear_runs_stays
#print axioms LPFK9.hruns_reached
#print axioms LPFK9.field_batch_scope
#print axioms LPFK9.field_behind_scope
