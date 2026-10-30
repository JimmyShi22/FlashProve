-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Behind.lean: CONDITIONAL. Definitions of hypotheses, and
statements with their proofs.

What is here. A THREAD's DEBT `Behind` (Honest/Thread/Pays.lean) AT THE MEMBER OF THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4), BROUGHT DOWN TO SIX NAMED HYPOTHESES ON THE THREAD's
PARAMETERS.

  `K4Promise T b p Fence`   where the thread's form and promise hold at a state s in front of the
      member, s' is such that `KeptAtS` (Johnson/Road/K4/KeptAtS.lean) holds of s and s' (what a yes
      of the kind's sub-protocol leaves: THE YES ITSELF IS NOT AMONG THE HYPOTHESES: so it is asked
      at every such pair, accepted or not), and Fence holds of s: the form and the promise of the
      next border hold at s', at the same handed data. Fence: what is asked of the state in front
      beside the promise: a parameter.
  `BehindAt T At b`   the sentence of `Behind` with At in the stead of «Thr T b»: which stands in
      front are meant, as in `ShareAt` (Law/Table.lean).
  `seat_behind`   behind the member's step the handed data are those in front. General in the
      thread.
  `k4_behind`   **BehindAt**, under SIX: K4Sits · K4NoMark · K4Promise · At gives the thread's
      sentence and Fence · K4's clause `K4KeepsM` (Law/KeepsStep.lean: with «no mark behind» inside)
      gives the thread's parameter keeps at b · the thread's parameter rides passes from b to b + 1
      across `K4KeepsM`.
  `k4_behind_thr`, `k4_behind_said`   so `Behind T b`, and `BehindS T Said b`.
  `k4_form_keeps`   the form behind and keeps alone, without the hypothesis on rides.

Not shown here. THAT THE PROMISE HOLDS BEHIND THE STEP ANYWHERE: `K4Promise` is a hypothesis here.
That the hypotheses can hold together: this file gives no example. Who is meant to prove each.
K4Sits, K4NoMark: Law/SitsAt.lean has both at a member that is the lot's own sub-protocol, seated
alone. K4Promise: Law/PromiseConds.lean, Law/PromiseAll.lean and Law/PromiseAt.lean have it at the
library's own parameters, at the full size, under the library's hypothesis on the public files and
eleven public hypotheses, with six facts on the state in front as Fence. Law/FenceOfFold.lean has
five of these six from a structure of facts at reached states, and Law/BehindHead.lean has these
five wherever the first chain's thread, at the library's own parameters, stands in front of the
member (`k4Fence_at`): so there `k4_behind_thr` serves (`k4_behind_head`). The sixth, that what the
lookup has heard has the plan's shape, is a hypothesis in all of these; Law/HeadTops.lean
(`k4_behind_top`) has it out of the promise in front (`k4_heard_head`, Law/ReadyHead.lean). The two
on keeps and rides: whoever lays these two parameters. No other file under Honest/K4/ names
`k4_behind_said` or `k4_form_keeps`. Every file under Law/ that this head names is no part of the
library yet. Following import lines, and stopping unopened at every module under Johnson/Goal/,
Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its
imports reach 2 modules under Johnson/Bridge/ and none of the others; what lies behind these is not
counted. Nothing on soundness, on completeness or on any other property.

Kin. THE SECOND CLAUSE OF `seat_behind` STANDS, UNDER LESS, IN ANOTHER KIND's FILE:
`ProofFile.Honest.seat_moved` (Honest/K7/Behind.lean, of other writers): from `T.Fit b m` and `T.Moved`
alone, at any two states; here it is drawn from «Thr T b» and `T.Stepped`, which give these two. The
first clause is the first of `play_mid` (Honest/Law/Along.lean). It is typed here so that no file of
another kind's writers is imported. `BehindAt` names no kind: it is `Behind` at a free At; `BehindS`
(Honest/Thread/PaysS.lean) is its case At := «ThrS T Said b».

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (KeptAtS kept_atS)
open VerifiableInference.Desc (Block OpenedColumn Claim First.S)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **The thread's form and promise pass K4's accepting decision.** A hypothesis's form. Nothing is
claimed by the definition. -/
def K4Promise (T : Thread Bk First.S Claim V W X Pb) (b : Nat) (p : Par) (Fence : First.S → Prop) :
    Prop :=
  ∀ (z : T.P) s s', T.form b (z, s) = true → T.formP b (z, s) → KeptAtS p s s' → Fence s →
    T.form (b + 1) (z, s') = true ∧ T.formP (b + 1) (z, s')

section
variable {S Cl : Type} (T : Thread Bk S Cl V W X Pb)

/-- **The sentence of `Behind`**, at the stands in front that At names. A definition: nothing is
claimed by it. -/
def BehindAt (At : Coins Bk → S → Mid W X → Env → Prop) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 ∧ T.rides (b + 1) y.2.st.input s' ∧ T.keeps b s s'

/-- Behind the member's step the input is the input in front, and what was handed to the chain is
what was handed in front. -/
theorem seat_behind {b : Nat} {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} (hA : Thr T b k s m E)
    (hS : T.Stepped blk k s m E ds y cols s') :
    y.2.st.input = m.st.input ∧ T.seat k y.2 s' = ((T.seat k m s).1, s') := by
  unfold Thr at hA
  obtain ⟨-, hF0, -, -, -, -, -⟩ := hA
  unfold Thread.Stepped Thread.Moved at hS
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  have hfr : T.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  refine ⟨ei, ?_⟩
  unfold Thread.seat
  rw [ei, eh, List.take_append_of_le_length hfr]

end

section
variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {p : Par} {Fence : First.S → Prop}

/-- **`Behind` AT K4's MEMBER.** CONDITIONAL: on the seat (`K4Sits`, `K4NoMark`), the promise's
passing, and the three hypotheses on At, keeps and rides. -/
theorem k4_behind {At : Coins Bk → First.S → Mid W X → Env → Prop} (hSit : K4Sits T b p)
    (hM : K4NoMark T b) (hP : K4Promise T b p Fence)
    (hA : ∀ k s m E, At k s m E → Thr T b k s m E ∧ Fence s)
    (hK : ∀ s s', K4KeepsM s s' → T.keeps b s s')
    (hR : ∀ w s s', T.rides b w s → K4KeepsM s s' → T.rides (b + 1) w s') : BehindAt T At b := by
  intro blk hblk k s m E ds y cols s' hAt hd hS
  obtain ⟨hT, hFe⟩ := hA k s m E hAt
  obtain ⟨ei, es⟩ := seat_behind T hT hS
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  have Kp : K4KeepsM s s' := ⟨k4_keeps hdec, hM blk hblk s _ _ s' _ hS.2⟩
  unfold Thr at hT
  obtain ⟨-, -, hFm, -, -, hRd, -⟩ := hT
  refine ⟨?_, ?_, hK s s' Kp⟩
  · unfold Thread.Form
    rw [es]
    exact hP _ s s' hFm.1 hFm.2 (kept_atS hdec) hFe
  · rw [ei]
    exact hR _ s s' hRd Kp

/-- **`Behind T b`.** CONDITIONAL, as `k4_behind`; Fence is asked wherever the thread's sentence
holds in front. -/
theorem k4_behind_thr (hSit : K4Sits T b p) (hM : K4NoMark T b) (hP : K4Promise T b p Fence)
    (hF : ∀ k s m E, Thr T b k s m E → Fence s) (hK : ∀ s s', K4KeepsM s s' → T.keeps b s s')
    (hR : ∀ w s s', T.rides b w s → K4KeepsM s s' → T.rides (b + 1) w s') : Behind T b :=
  k4_behind hSit hM hP (fun k s m E h => ⟨h, hF k s m E h⟩) hK hR

/-- **`BehindS T Said b`.** CONDITIONAL, as `k4_behind`; Fence is asked at the pair alone. -/
theorem k4_behind_said (Said : Nat → Coins Bk → Mid W X → Prop) (hSit : K4Sits T b p)
    (hM : K4NoMark T b) (hP : K4Promise T b p Fence)
    (hA : ∀ k s m E, ThrS T Said b k s m E → Thr T b k s m E ∧ Fence s)
    (hK : ∀ s s', K4KeepsM s s' → T.keeps b s s')
    (hR : ∀ w s s', T.rides b w s → K4KeepsM s s' → T.rides (b + 1) w s') : BehindS T Said b :=
  k4_behind hSit hM hP hA hK hR

/-- **The form behind, and keeps**: the two that a thread's own statement on `BehindS` from its
clauses of rides asks of a member's writers (`behindS_of_keepsS`, Honest/Thread/SharesS.lean: its
hypothesis hFK; `behindS_of_keeps_and`, Honest/Thread/RidersAnd.lean, asks the same). CONDITIONAL:
as `k4_behind`, without the hypothesis on rides. -/
theorem k4_form_keeps {At : Coins Bk → First.S → Mid W X → Env → Prop} (hSit : K4Sits T b p)
    (hM : K4NoMark T b) (hP : K4Promise T b p Fence)
    (hA : ∀ k s m E, At k s m E → Thr T b k s m E ∧ Fence s)
    (hK : ∀ s s', K4KeepsM s s' → T.keeps b s s') :
    ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s' := by
  intro blk hblk k s m E ds y cols s' hAt hd hS
  obtain ⟨hT, hFe⟩ := hA k s m E hAt
  obtain ⟨-, es⟩ := seat_behind T hT hS
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  unfold Thr at hT
  obtain ⟨-, -, hFm, -, -, -, -⟩ := hT
  refine ⟨?_, hK s s' ⟨k4_keeps hdec, hM blk hblk s _ _ s' _ hS.2⟩⟩
  unfold Thread.Form
  rw [es]
  exact hP _ s s' hFm.1 hFm.2 (kept_atS hdec) hFe

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4Promise
#print axioms ProofFile.Honest.K4.BehindAt
#print axioms ProofFile.Honest.K4.seat_behind
#print axioms ProofFile.Honest.K4.k4_behind
#print axioms ProofFile.Honest.K4.k4_behind_thr
#print axioms ProofFile.Honest.K4.k4_behind_said
#print axioms ProofFile.Honest.K4.k4_form_keeps
