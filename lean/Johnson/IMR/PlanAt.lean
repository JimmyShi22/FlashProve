-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/PlanAt.lean: THE TEST ON THE PLAN AT THE SEAT, ONE LEMMA FOR ALL KINDS: where the
description passes its tests on the plan, THE LOT's BLOCK at every place passes its own.
OBJECT. b'.planOk for the lot's block b' beneath a seated block b of onlineDescription's first chain. USER. The kinds' laws that take «B.planOk = true» (of the row K03_sits: «hOk: no top hands it»): whoever calls a seat.
CALLED, NOT TYPED: VerifiableInference.Desc.Keeps.planOk_blocks (Johnson/Desc/PlanPasses.lean: F.planOk = true gives every block's own test, chain by chain; its runEnd_blocks gives the same behind a yes of the file's decision).

  plan_flat         F.planOk = true → every block of c.blocksInOrder passes its test on the plan.
  plan_hear         … so does every block in front of a link's batching.
  plan_alone        … and the lot's block beneath it, where it stands ALONE.
  plan_carried      … and, where the lot's block is carried over (x.retype), x's own test.
  plan_joined       … and, at a link's first place, the lot's block's and the row's (f.plan = true).
  plan_back         … and every block behind the links.
  k7_sits_step      (in scope) at «H:1» the seated block's STEP's yes is k7Block's step's yes, to the same record, with as many columns taken; no mark behind it (wanted by the row K07_sits).

What is not claimed. That F.planOk holds: it is the caller's (behind a yes of the run: planOk_of_runEnd). Behind the links Chain.blocksInOrder lays { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }: plan_back gives c.back[j]'s own. No soundness.
-/
import Johnson.IMR.FirstSeats
import Johnson.Desc.PlanPasses

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Where the description passes its tests on the plan, every block of the first chain's flat list passes its own.** -/
theorem plan_flat (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  have hd := O.desc
  subst hd
  exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hp).1

/-- A block in front of a link's batching. -/
theorem plan_hear (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) {l i : ℕ}
    {Lk : Link S Cl} {b : Block S Cl} (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) :
    b.planOk = true :=
  plan_flat O hp b (hear_mem_flat h1 h2)

/-- **The lot's block beneath it, where it stands alone.** -/
theorem plan_alone (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) {l i : ℕ}
    {Lk : Link S Cl} {b b' : Block S Cl} {name : String} {a : Place} (h1 : c.links[l]? = some Lk)
    (h2 : Lk.hear[i]? = some b) (hla : LaidAlone ProofFile.sameReply b b' name a) : b'.planOk = true := by
  rw [← alone_planOk hla]
  exact plan_hear O hp h1 h2

/-- Where the lot's block is carried over from a block without claims of its own type. -/
theorem plan_carried (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) {l i : ℕ}
    {Lk : Link S Cl} {b : Block S Cl} {C : Type} {x : Block S C} {name : String} {a : Place}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b)
    (hla : LaidAlone ProofFile.sameReply b x.retype name a) : x.planOk = true :=
  (retype_planOk x (plan_alone O hp h1 h2 hla)).1

/-- **At a link's first place: the lot's block's test and the row's.** -/
theorem plan_joined (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) {l : ℕ}
    {Lk : Link S Cl} {b b' : Block S Cl} {a : Place} (h1 : c.links[l]? = some Lk)
    (h2 : Lk.hear[0]? = some b) (hj : Joined Z l b b' a) :
    b'.planOk = true ∧
      ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
        fs[l]? = some f ∧ f.plan = true := by
  obtain ⟨fs, f, hfs, hf, e⟩ := hj.planOk
  rw [plan_hear O hp h1 h2] at e
  have e' := Bool.and_eq_true_iff.1 e.symm
  exact ⟨e'.1, fs, f, hfs, hf, e'.2⟩

/-- A block behind the links. -/
theorem plan_back (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) {j : ℕ}
    {b : Block S Cl} (h : c.back[j]? = some b) : b.planOk = true := by
  have hm : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl) ∈ c.blocksInOrder := by
    unfold Chain.blocksInOrder
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, List.mem_of_getElem? h, rfl⟩))
  have h1 : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := plan_flat O hp _ hm
  exact (Bool.and_eq_true_iff.1 h1).1

end

/-! ## K7 at the step -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **AT «H:1» THE SEATED BLOCK's STEP's YES IS k7Block's STEP's YES, TO THE SAME RECORD, WITH AS MANY COLUMNS TAKEN; no mark behind it.** (Joined.step at the head's row, whose «opened» hands the record on.) -/
theorem k7_sits_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hj : Joined Z 24 b (k7Block Bs.G₀.W 24).retype k7Place) {ft : ℕ} {s t : S} {n : ℕ}
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hy : b.step ft s rs cols = .ok (t, n)) :
    ((k7Block Bs.G₀.W 24).retype : Block S Cl).step ft s rs cols = .ok (t, n) ∧ t.failed = none := by
  obtain ⟨-, -, -, -, -, hid⟩ := k7_sits hS hR O
  obtain ⟨fs, f, m, hfs, hf, h1, h2, h3, -, -⟩ := hj.step hy
  rw [hid fs f hfs hf] at h3
  obtain rfl : m = t := Except.ok.inj h3
  exact ⟨h1, h2⟩

end

end IM

#print axioms IM.plan_flat
#print axioms IM.plan_hear
#print axioms IM.plan_alone
#print axioms IM.plan_carried
#print axioms IM.plan_joined
#print axioms IM.plan_back
#print axioms IM.k7_sits_step
