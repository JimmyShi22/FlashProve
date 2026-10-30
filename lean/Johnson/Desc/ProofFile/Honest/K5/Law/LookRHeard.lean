-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LookRHeard.lean: CONDITIONAL: WHATEVER THE SEATED HEARING OF A
LOOKUP RETURNS, AT PARAMETERS WITH A SHAPE OF FOUR CALLS, HAS KEY POINTS OF THE LIBRARY's FORM
(`K3Pts`, Johnson/Desc/First/Att/K05LookAll.lean); so, under the library's hypothesis on the public
input (`P5J.AtMgA`), at the shape of an attention group's stored plan it meets the sentence `lookR`
(Johnson/Desc/K5/Honest/Law/LookR.lean).

Why. A rider on the open segment's field g, laid by the lookup's member, is typed general in a
sentence R on that field, under the premise that R holds of whatever the seated hearing returns at
parameters with the plan's shape, at every fork and on all rounds. Here R is `lookR`. This is that
premise.

  `k3Pts_of_hearVia`   CONDITIONAL: the parameters' shape is s; s has four calls; the hearing
                       returns Hd: `K3Pts` s Hd.zx Hd.zy Hd.zk (readV (Hd.zx ++ Hd.zy))
  `lookR_of_hearVia`   CONDITIONAL: under h, g below 12, the group's plan a: **at every p with
                       p.shape = some a.fs, every fork and all rounds: `lookR` a (some Hd)**

The road. The hearing's zx, zy, zk are the cut of a point that is made of the rounds' samples
(`keyPtsAt_of_hearVia`, Honest/K3/HeardLaw.lean); that point has dT + rK coordinates whatever the
samples are (`keyPt_size`, Honest/K5/Law/KeyOfK3.lean); the cut of such a point has the form
(`k3Pts_cut`, Honest/K5/Law/KeyOfK3At.lean); the plan's shape has four calls (`fo_at_head`,
Johnson/Desc/K5/Honest/Law/FoAtHead.lean). The library's nearest text: `block_point_calls`
(Johnson/Desc/First/Look/K3PointAtSeats.lean): the same cut from a yes of the lookup's sub-protocol;
here it is had from the seated hearing's return.

Limits. `K3Pts` at readV (zx ++ zy) IS A SENTENCE ON THE THREE FIELDS ALONE: two lengths, and that
each call's key point is a cut of zy, then zx. IT TIES THEM TO NO ROUND AND TO NOTHING THAT WAS
HEARD: so it can hold of every return. That the key points are those of the challenges that a run
has heard is another sentence (`keyText_K3`'s second clause, Honest/K5/Law/KeyTextK3.lean), and is
not here. h is a hypothesis of every statement that names it; it is spent for the four calls alone.
At the library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyOfK3At
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw
import Johnson.Desc.K5.Honest.Law.FoAtHead
import Johnson.Desc.K5.Honest.Law.LookR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Att.P (K3Pts)
open VerifiableInference.Desc.K3.Law (hearVia)
open ProofFile.Honest.K3 (keyPtsAt keyPtsAt_of_hearVia)
open H2K5.Honest (lookR)
open P5J (AtMgA TS)

/-- **WHAT THE SEATED HEARING RETURNS HAS KEY POINTS OF THE LIBRARY's FORM.** CONDITIONAL: hp: the
parameters' shape is s; nc: s has four calls; hv: the hearing returns. -/
theorem k3Pts_of_hearVia {s : Forest.Shape} (nc : s.NC = 4)
    {p : VerifiableInference.Desc.First.Look.P} (hp : p.shape = some s) {F G₁ : Fork}
    {rs : List Fmt.RoundView} {Hd : Forest.Heard} (hv : hearVia p F rs = some (Hd, G₁)) :
    K3Pts s Hd.zx Hd.zy Hd.zk (OnBytes.Slice.readV (Hd.zx ++ Hd.zy)) := by
  obtain ⟨ex, ey, ez⟩ := keyPtsAt_of_hearVia p s hp F G₁ rs Hd [] [] hv
  rw [ex, ey, ez]
  unfold keyPtsAt
  exact k3Pts_cut s (show _ = s.dT + s.rK from keyPt_size _ _ _ _ s.v) nc

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **`lookR` OF WHATEVER THE SEATED HEARING RETURNS AT THE PLAN's SHAPE.** CONDITIONAL: under the
hypothesis h; g is below 12; the group's plan. -/
theorem lookR_of_hearVia {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    ∀ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs →
      ∀ F rs Hd G₁, hearVia p F rs = some (Hd, G₁) → lookR a (some Hd) := by
  intro p hp F rs Hd G₁ hv
  obtain ⟨-, a', -, Pl, -⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  obtain ⟨x₁, hx⟩ := Pl.look
  exact ⟨Hd, rfl, k3Pts_of_hearVia (H2K5.Honest.fo_at_head h hg ha hx).2 hp hv⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k3Pts_of_hearVia
#print axioms ProofFile.Honest.K5.lookR_of_hearVia
