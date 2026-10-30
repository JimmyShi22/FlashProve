-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/PubPlain.lean: the proof file's public part (`ProofFile.pubPlain`,
Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean) at a parameter file with another acceptance policy. Statements
and proofs.
Premises of the main statements: hX: `publicOfO` returns X at the first parameter file; hX': at the
second it returns `X.withPol C theta cap`; one scale file, one layout file. (`chainsOf_wp` and
`builtOf_wp` have no premise.)
  `chainsOf_wp`, `builtOf_wp`: the plain planner's chains and segments' records read none of the
      three numbers: by unfolding.
  `planned_wp`, `sendsOf_wp`, `madeOf_wp`: the plain planner, the list of sendings and the maker's
      record.
  `pubPlain_wp`: where `pubPlain` returns Z at the first file, it returns `wpZ Z pol' C theta cap`
      at the second.
Limits. hX' is a premise here. Nothing on soundness.

-/
import Johnson.LPFPol.WithPol
import Johnson.LPFPol.HashReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace LPFPol
open OnBytes OnBytes.Model
open OnBytes.Params (exc_bind)
open VerifiableInference.PlanWritten (publicOfO)

theorem chainsOf_wp (X : Verify.Public) (C theta cap : Nat) (lay : Option ByteArray)
    (cfg : ByteArray) :
    ProofFile.Plain.chainsOf (X.withPol C theta cap) lay cfg = ProofFile.Plain.chainsOf X lay cfg := rfl

theorem builtOf_wp (X : Verify.Public) (C theta cap : Nat) (ch : Verify.Chains) :
    ProofFile.Plain.builtOf (X.withPol C theta cap) ch = ProofFile.Plain.builtOf X ch := rfl

section
variable {o : Nat → ByteArray → ByteArray} {pol pol' KL : ByteArray} {X : Verify.Public}
    {C theta cap : Nat}

theorem planned_wp {lay : Option ByteArray} (hX : publicOfO o pol KL lay = .ok X)
    (hX' : publicOfO o pol' KL lay = .ok (X.withPol C theta cap)) {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o pol KL lay = .ok p) :
    ProofFile.Plain.planned o pol' KL lay = .ok (wpP p C theta cap) := by
  unfold ProofFile.Plain.planned at hp ⊢
  obtain ⟨X0, h0, hp⟩ := exc_bind hp
  obtain rfl : X0 = X := Except.ok.inj (h0.symm.trans hX)
  obtain ⟨ch, hch, hp⟩ := exc_bind hp
  obtain ⟨b, hb, hp⟩ := exc_bind hp
  cases hp
  refine (bind_ok hX').trans ?_
  refine (bind_ok (a := ch) hch).trans ?_
  refine (bind_ok (a := b) hb).trans ?_
  rfl

theorem planned_X {lay : Option ByteArray} (hX : publicOfO o pol KL lay = .ok X)
    {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o pol KL lay = .ok p) : p.X = X := by
  unfold ProofFile.Plain.planned at hp
  obtain ⟨X0, h0, hp⟩ := exc_bind hp
  obtain rfl : X0 = X := Except.ok.inj (h0.symm.trans hX)
  obtain ⟨ch, hch, hp⟩ := exc_bind hp
  obtain ⟨b, hb, hp⟩ := exc_bind hp
  cases hp
  rfl

theorem sendsOf_wp {lay : ByteArray} {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o pol KL (some lay) = .ok p)
    (hp' : ProofFile.Plain.planned o pol' KL (some lay) = .ok (wpP p C theta cap)) :
    ProofFile.PlainG.sendsOf o pol' lay KL = ProofFile.PlainG.sendsOf o pol lay KL := by
  unfold ProofFile.PlainG.sendsOf
  rw [bind_ok hp, bind_ok hp']
  rfl

theorem madeOf_wp {lay : ByteArray} (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap)) {m : Johnson.G.OfPlan.Made}
    (hm : ProofFile.PlainG.madeOf o pol lay KL = .ok m) :
    ProofFile.PlainG.madeOf o pol' lay KL = .ok (wpM m C theta cap) := by
  unfold ProofFile.PlainG.madeOf at hm ⊢
  obtain ⟨p, hp, hm⟩ := exc_bind hm
  have hp' := planned_wp hX hX' hp
  obtain ⟨l, hl, hm⟩ := exc_bind hm
  refine (bind_ok hp').trans ?_
  refine (bind_ok (a := l) ((sendsOf_wp hp hp').trans hl)).trans ?_
  split at hm
  · cases hm
    rfl
  · cases hm

theorem madeOf_X {lay : ByteArray} (hX : publicOfO o pol KL (some lay) = .ok X)
    {m : Johnson.G.OfPlan.Made} (hm : ProofFile.PlainG.madeOf o pol lay KL = .ok m) : m.p.X = X := by
  unfold ProofFile.PlainG.madeOf at hm
  obtain ⟨p, hp, hm⟩ := exc_bind hm
  obtain ⟨l, hl, hm⟩ := exc_bind hm
  split at hm
  · cases hm
    exact planned_X hX hp
  · cases hm

theorem atCall_ok {α : Type} {n : String} {x : Except String α} {a : α}
    (h : ProofFile.atCall n x = .ok a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => exact h

theorem atCall_of {α : Type} {n : String} {x : Except String α} {a : α} (h : x = .ok a) :
    ProofFile.atCall n x = .ok a := by
  rw [h]
  rfl

/-- **The public part at the other policy.** -/
theorem pubPlain_wp {lay : ByteArray} (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap)) {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ProofFile.pubPlain o pol' lay KL = .ok (wpZ Z pol' C theta cap) := by
  unfold ProofFile.pubPlain ProofFile.pubBy at hZ ⊢
  obtain ⟨m, hm, hZ⟩ := exc_bind hZ
  have hm' := atCall_of (n := "the plan") (madeOf_wp hX hX' (atCall_ok hm))
  refine (bind_ok hm').trans ?_
  dsimp only at hZ ⊢
  split at hZ
  · obtain ⟨_, e, _⟩ := exc_bind hZ
    cases e
  · rename_i hc
    obtain ⟨u, hu, hZ⟩ := exc_bind hZ
    obtain ⟨D, hD, hZ⟩ := exc_bind hZ
    obtain ⟨told, ht, hZ⟩ := exc_bind hZ
    obtain ⟨depth, hd, hZ⟩ := exc_bind hZ
    obtain ⟨cuts, hcu, hZ⟩ := exc_bind hZ
    obtain ⟨s0, hs, hZ⟩ := exc_bind hZ
    cases hZ
    rw [if_neg (show ¬ ((!(wpM m C theta cap).p.chains.proof.first.codes.lengthsOk) = true) from
        hc)]
    refine (bind_ok (a := u) hu).trans ?_
    refine (bind_ok (a := D) hD).trans ?_
    refine (bind_ok (a := told) ht).trans ?_
    refine (bind_ok (a := depth) hd).trans ?_
    refine (bind_ok (a := cuts) hcu).trans ?_
    refine (bind_ok (a := s0) hs).trans ?_
    rfl

theorem pubPlain_X {lay : ByteArray} (hX : publicOfO o pol KL (some lay) = .ok X) {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) : Z.p.X = X := by
  unfold ProofFile.pubPlain ProofFile.pubBy at hZ
  obtain ⟨m, hm, hZ⟩ := exc_bind hZ
  have e := madeOf_X hX (atCall_ok hm)
  dsimp only at hZ
  split at hZ
  · obtain ⟨_, e, _⟩ := exc_bind hZ
    cases e
  · obtain ⟨u, hu, hZ⟩ := exc_bind hZ
    obtain ⟨D, hD, hZ⟩ := exc_bind hZ
    obtain ⟨told, ht, hZ⟩ := exc_bind hZ
    obtain ⟨depth, hd, hZ⟩ := exc_bind hZ
    obtain ⟨cuts, hcu, hZ⟩ := exc_bind hZ
    obtain ⟨s0, hs, hZ⟩ := exc_bind hZ
    cases hZ
    exact e

end

end LPFPol

#print axioms LPFPol.pubPlain_wp
#print axioms LPFPol.pubPlain_X
