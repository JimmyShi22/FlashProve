-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Pays.lean: who can pay the one premise on values of the output head's four
runs of claims (Ends, Core.lean beside it) IN FRONT OF a return of a run.

What it is not. It shows the premise at no state that the chain reaches. It shows of no member and
of no run that it carries what the lookup on the calls was heard to return: these laws are the
library's and the other sub-protocols' authors' (each ends in CarriesFo S.fork? S.lookHeard?,
Johnson/Desc/First/LedgerAtFo.lean); here they are made spendable for the premise by one lemma
(endsHeard_carried), and one is spent (the draw); THE JOIN from the output head's own member to the
batching is not made. Nothing on chance: that the test holds of whatever the lookup lays is not
shown. Nothing on any property of the protocol. It stands on what Core.lean stands on.

  `ends_congr`   the premise reads what the lookup on the calls was heard to return, and no more
  `ends_putFork`, `ends_set`   so a laying of the ledger, and the batching's lens's laying of its
                part, leave it as it was: by the library's S.look_putFork and K9.set_heard
  `EndsHeard p s`   the lookup on the calls IS heard at s, and the one test on values accepts
                what it returned: the form that is carried
  `endsHeard_ends`, `endsHeard_iff`   it gives the premise; where the lookup is heard the two
                are one
  `endsHeard_of_given`   **where `given` returns (Johnson/Desc/Kinds/HeadFrame.lean), EndsHeard
                holds**: the output head's own step calls `given` first
  `endsHeard_carried`   **it is carried along the library's relation**
  `endsHeard_draw`   so it is carried across the batching's draw, whatever element is drawn

-/
import Johnson.Desc.K6.Shape.Core
import Johnson.Desc.First.K9x.CallsAtK9
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S)

section Pays
variable (p : Par)

/-- The premise reads what the lookup on the calls was heard to return, and no more. -/
theorem ends_congr {s s' : S} (e : s'.lookHeard? = s.lookHeard?) : Ends p s' ↔ Ends p s :=
  ⟨fun a => ⟨fun g hg => a.ends g (e.trans hg)⟩, fun a => ⟨fun g hg => a.ends g (e.symm.trans hg)⟩⟩

/-- A laying of the ledger leaves it as it was. -/
theorem ends_putFork (s : S) (F : Fork) : Ends p (s.putFork F) ↔ Ends p s :=
  ends_congr p (S.look_putFork s F)

/-- The batching's lens's laying of its part leaves it as it was. -/
theorem ends_set (s : S) (q : K9.Part) : Ends p (K9.atS.set s q) ↔ Ends p s :=
  ends_congr p (K9.set_heard s q).1

/-- **The form that is carried**: the lookup on the calls is heard, and the one test on values
accepts what it returned. -/
def EndsHeard (s : S) : Prop := ∃ g, s.lookHeard? = some g ∧ endsB p g = true

/-- It gives the premise. -/
theorem endsHeard_ends {s : S} (a : EndsHeard p s) : Ends p s := by
  obtain ⟨g, hg, e⟩ := a
  refine ⟨fun g' hg' => ?_⟩
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  exact e

/-- Where the lookup is heard the two are one. -/
theorem endsHeard_iff {s : S} {g : OnBytes.Model.Forest.Heard} (hg : s.lookHeard? = some g) :
    EndsHeard p s ↔ Ends p s :=
  ⟨endsHeard_ends p, fun a => ⟨g, hg, a.ends g hg⟩⟩

/-- **Where `given` returns, EndsHeard holds.** No view is wanted: so it speaks at the state in
front of the output head's own step, where that step's hearing is not yet laid. -/
theorem endsHeard_of_given (h : OnBytes.Model.Head.Shape) (iU3 : Nat) {s : S} {g : Given}
    (hg : given p (seatAt h iU3) s = .ok g) : EndsHeard p s := by
  obtain ⟨z, y, hz, hy, -, -⟩ := Law.Came.given_ok p (seatAt h iU3) s g hg
  have hz' : s.lookHeard?.map (fun g => (g.zx, fun c => g.zk.getD c #[])) = some z := hz
  obtain ⟨gl, hgl, rfl⟩ := Option.map_eq_some_iff.mp hz'
  refine ⟨gl, hgl, ?_⟩
  have h1 : (given p (seatAt h iU3) s).toOption.isSome = true := by
    rw [hg]
    rfl
  rw [given_isSome p (seatAt h iU3) s _ y hz hy] at h1
  have h5 := (@test_split p.sizes p.floor gl.zx fun c => gl.zk.getD c #[]).symm.trans h1
  rw [Bool.and_eq_true] at h5
  exact h5.2

/-- **It is carried along the library's relation**: what was heard stands. -/
theorem endsHeard_carried {s s' : S} (c : CarriesFo S.fork? S.lookHeard? s s') (a : EndsHeard p s) :
    EndsHeard p s' := by
  obtain ⟨g, hg, e⟩ := a
  exact ⟨g, c.1 g hg, e⟩

/-- So it is carried across the batching's draw, whatever element is drawn: by the library's
K9.drawStepsAtS (Johnson/Desc/First/K9x/CallsAtK9.lean). -/
theorem endsHeard_draw (w : K9.Where) {t t₁ : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (K9.drawAlone (Cl := Claim) K9.atS w).decide t rs gs = .ok t₁) (a : EndsHeard p t) :
    EndsHeard p t₁ :=
  endsHeard_carried p (K9.drawStepsAtS w t rs gs t₁ hd) a

end Pays

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.ends_congr
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.ends_putFork
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.ends_set
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.endsHeard_ends
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.endsHeard_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.endsHeard_of_given
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.endsHeard_carried
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.endsHeard_draw
