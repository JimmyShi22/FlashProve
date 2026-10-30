-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/HeldPublic.lean: THE SMALLNESS TEST: TWO OF THE VERIFIER's OWN TESTS IN FRONT
OF THE BATCHING (`forestHeld`, and `callHeld` at both calls: OnBytes/Model/Tail.lean) READ OF WHAT
THE DIGITS' LOOKUP HAS HEARD FIVE SIZES AND NOTHING ELSE; ALL ELSE THAT THEY READ ARE FIVE PLANNED
FIELDS OF THE DATA. SO AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A
SEGMENT's BATCHING, IN THE GOALS' SCOPE, BOTH SAY YES WHERE ONE PUBLIC TEST WITH CODE SAYS YES AT
THE BUILT SEGMENT's DATA AND THE FIVE SIZES ARE AS THE DATA NAME THEM. A premise at every state is
exchanged for a test on 25 plans and five sizes. Definitions and lemmas; none of the library's
goals.

  `forestHeld_size`, `callHeld_size`   the two tests hang on the heard structure's sizes alone
  `modelHeard tl`   a heard structure of zeros with the five sizes that the data name
  `heldPubB tl`   THE PUBLIC TEST, WITH CODE: the verifier's own two tests at modelHeard tl
  `HeardSizes tl g`   the five sizes: zy · zx · e · the two calls' points
  **`held_of_pub`**   heldPubB tl = true · HeardSizes tl g ⊢ forestHeld and both callHeld say yes
  `heldFields tl`, `planned_heldFields`   the data with all but five fields (f9 · z1 · z2 · lidb ·
                   blocks) at their defaults; a reading of planned fields; the public test reads no
                   other field (`pub_heldFields`, by rfl)
  **`held_at_batch`**   at the state's own data, from the public test at the built segment's
KIN: the library's `forestHeld_iff`, `callHeld_iff` (Johnson/Desc/First/TailClaims/AgainMeans.lean)
spell the two tests out clause by clause; not called.
Limits. EXCHANGED, NOT PAID: `heldPubB` IS SHOWN OF NO PLAN HERE; IN SCOPE, UNDER AN OPENING OF THE
DESCRIPTION AND ITS TEST ON ITS PLAN, THE PUBLIC TEST SAYS YES AT EACH OF THE 25 BUILT SEGMENTS'
DATA (`heldPub_at_built`, Johnson/Desc/K8/Honest/HeldOutright.lean); no verifier asks it as such: it
is the verifier's own text at a made-up heard structure. `HeardSizes` IS A PREMISE HERE; it is
shown, at the 24 segments in front of the head's, in Johnson/Desc/K8/Honest/HeardAtReach.lean, off
the library's own law at these very states (`leftOn_digits_front`,
Johnson/Desc/First/Link/Law/KxAtFront.lean). THE FIVE NUMBERS ARE THOSE THAT THE TWO TESTS' TEXT
COMPARES THE SIZES WITH (by reading; were one of them another, the public test would say no at every
plan). Nothing on `pointsHeld`. IN SCOPE ALONE in the last: the full size's 25 segments; under an
opening of the description; the first chain; the family of states from the description's own first
state. Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.PlannedAtDraw
import Johnson.P1K8R.StaticAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The first test hangs on three sizes alone. -/
theorem forestHeld_size {tl : HTailF2} {g g' : Forest.Heard} (h1 : g.zy.size = g'.zy.size)
    (h2 : g.zx.size = g'.zx.size) (h3 : g.e.size = g'.e.size) :
    tl.forestHeld g = tl.forestHeld g' := by
  simp only [HTailF2.forestHeld, h1, h2, h3]

/-- The second hangs on the size of the call's point alone. -/
theorem callHeld_size {tl : HTailF2} {g g' : Forest.Heard} {nbW q : Nat}
    (h : (g.zk.getD q #[]).size = (g'.zk.getD q #[]).size) :
    tl.callHeld g nbW q = tl.callHeld g' nbW q := by
  simp only [HTailF2.callHeld, h]

/-- A heard structure of zeros with the five sizes that the data name. -/
def modelHeard (tl : HTailF2) : Forest.Heard :=
  { (default : Forest.Heard) with
    zy := Array.replicate (tl.z1.call.n - min tl.z1.call.n tl.lidb + 1) zeroE
    zx := Array.replicate (min tl.z1.call.n tl.lidb) zeroE
    e := Array.replicate 2 zeroE
    zk := #[Array.replicate tl.z1.call.n zeroE, Array.replicate tl.z2.call.n zeroE] }

/-- **The public test**: the verifier's own two tests at that structure. -/
def heldPubB (tl : HTailF2) : Bool :=
  tl.forestHeld (modelHeard tl) && [0, 1].all (tl.callHeld (modelHeard tl) tl.zzBlocks)

/-- The five sizes. -/
def HeardSizes (tl : HTailF2) (g : Forest.Heard) : Prop :=
  g.zy.size = tl.z1.call.n - min tl.z1.call.n tl.lidb + 1 ∧
    g.zx.size = min tl.z1.call.n tl.lidb ∧ g.e.size = 2 ∧
    (g.zk.getD 0 #[]).size = tl.z1.call.n ∧ (g.zk.getD 1 #[]).size = tl.z2.call.n

/-- The made-up structure has them. -/
theorem model_sizes (tl : HTailF2) : HeardSizes tl (modelHeard tl) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [modelHeard]

/-- **From the public test and the five sizes.** -/
theorem held_of_pub {tl : HTailF2} {g : Forest.Heard} (hP : heldPubB tl = true)
    (Z : HeardSizes tl g) :
    tl.forestHeld g = true ∧ [0, 1].all (tl.callHeld g tl.zzBlocks) = true := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := Z
  obtain ⟨b1, b2, b3, b4, b5⟩ := model_sizes tl
  unfold heldPubB at hP
  rw [Bool.and_eq_true] at hP
  obtain ⟨p1, p2⟩ := hP
  refine ⟨?_, ?_⟩
  · rw [forestHeld_size (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm)]
    exact p1
  · have c0 : tl.callHeld g tl.zzBlocks 0 = tl.callHeld (modelHeard tl) tl.zzBlocks 0 :=
      callHeld_size (a4.trans b4.symm)
    have c1 : tl.callHeld g tl.zzBlocks 1 = tl.callHeld (modelHeard tl) tl.zzBlocks 1 :=
      callHeld_size (a5.trans b5.symm)
    simp only [List.all_cons, List.all_nil, Bool.and_true] at p2 ⊢
    rw [c0, c1]
    exact p2

/-- The data with all but five fields at their defaults. -/
def heldFields (tl : HTailF2) : HTailF2 :=
  { f9 := tl.f9, z1 := tl.z1, z2 := tl.z2, lidb := tl.lidb, blocks := tl.blocks }

/-- A reading of planned fields. -/
theorem planned_heldFields : LinkJoin.Planned heldFields :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- The public test reads no other field. -/
theorem pub_heldFields (tl : HTailF2) : heldPubB tl = heldPubB (heldFields tl) := rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING.** -/
theorem held_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) (hP : heldPubB Xl.tl = true) {g : Forest.Heard}
    (hZ : HeardSizes tl g) :
    tl.forestHeld g = true ∧ [0, 1].all (tl.callHeld g tl.zzBlocks) = true := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have v : heldFields tl = heldFields Xl.tl := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_heldFields hS hR O hx e3 (z, s) h') tl ht
  have hP' : heldPubB tl = true := by
    rw [pub_heldFields tl, v, ← pub_heldFields Xl.tl]
    exact hP
  exact held_of_pub hP' hZ

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.forestHeld_size
#print axioms VerifiableInference.Desc.First.K8.Honest.callHeld_size
#print axioms VerifiableInference.Desc.First.K8.Honest.model_sizes
#print axioms VerifiableInference.Desc.First.K8.Honest.held_of_pub
#print axioms VerifiableInference.Desc.First.K8.Honest.planned_heldFields
#print axioms VerifiableInference.Desc.First.K8.Honest.pub_heldFields
#print axioms VerifiableInference.Desc.First.K8.Honest.held_at_batch
