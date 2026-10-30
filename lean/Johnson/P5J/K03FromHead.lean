-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P5J/K03FromHead.lean: the kind "lookup" (K3): THE KIND's LAW AT THE CLOSED CONSTANT, FROM
THE HEAD. The tenth and last count: no binder is left.
  `k03_cond_head` : `h.K3Cond 𝔏`: the kind's named condition
    (Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), from the head `AtMgA` at secondHashFunction,
    the filling 𝔏 and its three equations q₁ q₂ q₃. By one call of `k03_cond_due9`
    (Johnson/P5J/K03Due9.lean, which does not turn).
  `k03_kind_head` : `h.Kind 𝔏 .K3`: by `k03_kind_all`.
  `k03_kind_free` : `h.Kind h.free .K3`: at the head's own filling (Johnson/P5J/FreeAll.lean): NO
    PREMISE BUT THE HEAD.

PAID HERE BEYOND `k03_cond_due9`, ALL WHERE THE DIGITS' PIECE ACCEPTS: "join" at attention's 12
(Johnson/P5J/K03JoinItAttAt.lean, over `hJoinIt_dig`) · at the output head's link:
"own" and "join" behind the accept, and "join", "norm", "policy", "logits" go forward
(Johnson/P5J/K03HeadOwnAt.lean, over four ends and six of two other groups) · what the ledger behind
still owes the ledger in front owed (Johnson/P5J/K03HobAt.lean). The condition's two letters s₀ and
z₀ stand under "there are": any value serves; they are filled with the blank state and an empty
public instance.

WHAT IT IS NOT. THE HEAD IS A HYPOTHESIS: among its fields stand the entry tests' rows and further
named tests and equations on the public files; "from the head" has MOVED every closed test of this
kind into it. A MEMBER OF THE HEAD IS PROVED at `storedPublicFiles` and `zGap` alone (at secondHashFunction, with `fixedConfigurationDigest`
in the digest's place; side library AtFullSide/Top/); so by this project's rule of counting what
rests on the head counts as proved at `storedPublicFiles` and `zGap` alone. The condition is the frozen one AS
FENCED (Johnson/Desc/Sound/MgAt/K3Owed.lean, its
turned version): over the unturned ledger this file does not compile; the fence turns the condition
in the middle, not the sentence `h.Kind 𝔏 .K3` at the end. "No binder is left" means: none beside h.
Of the head's fields this kind spends, among others, k3 (a test on the lists of rounds at every
written link: Johnson/P5J/K03SeatsAt.lean). NO STATE IS SHOWN at which the promise, "reached", "no
mark" and an accept of a piece of this kind hold together: the law may hold idly. THE LAW ENDS IN A
DEBT: the relation behind a lookup is what later blocks owe; the lookup's own text tests no equation
(OnBytes/Model/Look.lean: "No equation is tested here"); no sum of the errors over the rounds is a
theorem here. At secondHashFunction and the full size alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Due9
import Johnson.P5J.K03JoinItAttAt
import Johnson.P5J.K03HeadOwnAt
import Johnson.P5J.K03HobAt
import Johnson.P5J.FreeAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift joinAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- **THE KIND's NAMED CONDITION, FROM THE HEAD, THE FILLING AND ITS THREE EQUATIONS.** -/
theorem k03_cond_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    h.K3Cond 𝔏 := by
  refine k03_cond_due9 h 𝔏 q₁ q₂ q₃ VerifiableInference.Desc.First.S.blank
    ⟨ByteArray.empty, default⟩ (k03_ownIt_head h 𝔏 q₁ q₂ q₃) ?_ (k03_hOb_head h 𝔏 q₁ q₂ q₃)
    (k03_fwd_join_head h 𝔏 q₁ q₂ q₃) (k03_fwd_own_head h 𝔏 q₁ q₂ q₃)
  intro l hl sub hsub hs q hq b' hb
  cases sub with
  | layers => exact absurd rfl hs
  | attention =>
    obtain ⟨he, h24⟩ := (k03_sorts_full l hl).1 hsub
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    exact k03_joinIt_att h 𝔏 q₁ q₂ q₃ g (by omega) q hq b' hb
  | head =>
    obtain rfl : l = 24 := (k03_sorts_full l hl).2 hsub
    exact k03_joinIt_head h 𝔏 q₁ q₂ q₃ q hq b' hb

/-- **THE KIND's LAW, FROM THE HEAD, THE FILLING AND ITS THREE EQUATIONS.** -/
theorem k03_kind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    h.Kind 𝔏 KindName.K3 :=
  k03_kind_all h 𝔏 q₁ q₂ q₃ (k03_cond_head h 𝔏 q₁ q₂ q₃)

/-- **THE KIND's LAW AT THE HEAD's OWN FILLING: NO PREMISE BUT THE HEAD.** -/
theorem k03_kind_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.Kind h.free KindName.K3 :=
  k03_kind_head h h.free h.free_q₁ h.free_q₂ h.free_q₃

end P5J

#print axioms P5J.k03_cond_head
#print axioms P5J.k03_kind_head
#print axioms P5J.k03_kind_free
#print axioms P5J.k03_kind_all
