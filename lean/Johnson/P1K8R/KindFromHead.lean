-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/KindFromHead.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
KIND'S FIELD OF THE TABLE, FROM THE HEAD ALONE. NO SOUNDNESS.

`k08_kind_head_of_ownSizes` (KindOfOwnSizes.lean) has one premise beside the head: a yes of the
closed test `ProofFile.smallSizesOwnB` at the blank ground. Under the head that is a
theorem: `P5J.ownSizes_at_head` (Johnson/P5J/K8OwnSizesAtHead.lean). Here it is called.
  `k08_cond_head`: **under the head, at any filling 𝔏 whose three lists are the flat lists':
    `h.K8Cond 𝔏`** (the frozen named condition: Johnson/Goal/Skeleton/Kinds/K8Bridge.lean).
  `k08_kind_head`: **and so `h.Kind 𝔏 K8`.**
  `k08_cond_free`, `k08_kind_free`: the two at the closed value `h.free`: the head is the one
    binder.
Limits. "FROM THE HEAD" IS "FROM THE HEAD (WITH THE FOURTEEN ENTRY TESTS)": most calls beneath spend
the head's field on the entry tests' accept; the block beneath `digits` also spends the head's
handed-in field `k3`, which no entry test asks. "From the head" is not "from what the verifier
asks". THAT THE HEAD CAN BE MET IS OTHER FILES' TO SHOW: a member of it is proved at `storedPublicFiles` and
`zGap` alone (at secondHashFunction; side library AtFullSide/Top/): AT OTHER FILES THE THEOREMS MAY BE IDLE.
What the condition's field `alike` is worth is
said in Johnson/P1K8R/EarlyReadFromHead.lean. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.
WHAT THE HEAD ITSELF RESTS ON: a head exists under four conditions on the public files: in scope,
the files read, `protocolDataWellFormed` accepts, and `rowsRead Z` (`P5J.head_exists_of_rows`,
Johnson/P5J/HeadExistsAtName.lean): the head's fields `k3` and `plan.radii` have that fourth as
their one payer. Over thirteen entry tests it was a named condition that the verifier did not run;
row 14 of the fourteen asks it, and `P5J.owed_of_live` (Johnson/Goal/Skeleton/OwedOfLive.lean) has
it from `protocolDataWellFormed`. K8 IS THE DRAW ALONE: this is the kind's share of the table: that the committed
values are small against a cheating prover needs K3 (the digits' lookups), K9 (the forms of the run
"small") and the sendings' pins as well. NO STATE that meets the promise, is reached and bears no
mark at one of the 25 places is shown in Lean: at an honest run's states parts of this were
evaluated, not proved.

-/
import Johnson.P1K8R.KindOfOwnSizes
import Johnson.P5J.K8OwnSizesAtHead

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FROZEN NAMED CONDITION AT ANY FILLING, FROM THE HEAD.** -/
theorem k08_cond_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) : h.K8Cond 𝔏 :=
  k08_cond_head_of_ownSizes h 𝔏 q₁ q₂ q₃ (P5J.ownSizes_at_head h)

/-- **THE KIND's FIELD OF THE TABLE AT ANY FILLING, FROM THE HEAD.** -/
theorem k08_kind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    h.Kind 𝔏 KindName.K8 :=
  k08_kind_head_of_ownSizes h 𝔏 q₁ q₂ q₃ (P5J.ownSizes_at_head h)

/-- The condition at the closed value. -/
theorem k08_cond_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : h.K8Cond h.free :=
  k08_cond_of_ownSizes h (P5J.ownSizes_at_head h)

/-- The kind's field at the closed value. -/
theorem k08_kind_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : h.Kind h.free KindName.K8 :=
  k08_kind_of_ownSizes h (P5J.ownSizes_at_head h)

end P1K8T

#print axioms P1K8T.k08_cond_head
#print axioms P1K8T.k08_kind_head
#print axioms P1K8T.k08_cond_free
#print axioms P1K8T.k08_kind_free
