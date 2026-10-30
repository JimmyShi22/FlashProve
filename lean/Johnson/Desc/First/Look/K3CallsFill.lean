-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsFill.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS: TWO
OF THE NAMED PREMISES OF THE ROW (AttAtTable's and LayAtTable's cf, pinIn) PAID AT THE TABLE's OWN
FILLING OF ITS LETTERS ON THE READING OF THE ORACLES (pinJT, noCollJT,
Johnson/Desc/Sound/MeaningSig.lean), under named conditions on the plan. Statements and proofs.
Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table's letters pin, noColl (meaningSig's pinJT, noCollJT) against
  the library's CfAt, PinSig at the link's own list.
USER: K3CallsAt.lean, K3CallsAtR.lean, Johnson/Desc/Sound/MgAt/K3HeadR.lean (calls_cf, calls_pinIn).
LETTERS: the link's list as ONE sending S0 := (sigListCalls D rad x.link, seatT); smp: the row's
  reader of samples, of the verifier's state alone; smpT: the table's; cs := D.codes.

Why. The table speaks of a tenant of a tree: "every member of ms that sits there ...". The lookup's
law speaks of the members of the link's own list. As values these are members of two lists. A pin is
a fact on a seat (Johnson/Desc/Sound/PinMove.lean: pin_move, cf_move): what is said of a member is
said of every member that is alike (one shape with its radius, one seat), where the state holds one
sample for the two.

THE CONDITIONS (the structure `ListSits`; all on the plan and on the letter smpT):
  `some`: each member of the link's list has an alike member in the table's list ms.
  `bySeat`: SmpBySeat: at alike members the verifier's state holds one sample.
  `sent`: every seat of the link's list is a tenant that segment m sends at moment 0 (ONE WAY: the
    table's numbers hold more there: the carried target).
  `fits`: the seats fit (SeatFits: a test on the plan).
  `smpIs`: smp s i = smpT (z, s) S0 i at EVERY value z of the public part (after the like at the
    digits): the row is asked at every z with one smp.

Limits. NONE OF THE FIVE IS SHOWN AT ANY PLAN OR FILLING. THE LINK's LIST HOLDS THE KEPT MESSAGES,
THEN THE LINK's OWN OF MOMENT 0 (sigListCalls, Johnson/Desc/First/Look/K3CallerAtt.lean:124): so
`sent` asks that the table's numbers count the kept copies' tenants among those that segment m
sends at moment 0: by a run off the small real plan they do.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.First.Look.K3CallerAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Numbers)

section
variable {P Cells Tok Xi : Type} (G : Desc.FileDescription Xi) (x : Desc.First.Look.Place)
  (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smpT : P × Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf D.codes s.l).om i).Smp)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (ms : List Mem) (N : Numbers) (m : ℕ)

/-- The link's list as one sending. -/
def callsSending : Sending := ⟨sigListCalls D rad x.link, seatT⟩

/-- **What is asked of the plan and of the two readers of samples.** smpIs: THE TIE OF THE TWO
LETTERS: the row stands at every value of the public part with ONE reader smp of the verifier's
state: so the table's reader must not read the public part at this list. -/
structure ListSits : Prop where
  some : ∀ i, ∃ y ∈ ms, Alike y ⟨callsSending x D rad seatT, i⟩
  bySeat : SmpBySeat D.codes smpT
  sent : ∀ i, seatT i ∈ N.sent m 0
  fits : SeatFits G D.codes (sigListCalls D rad x.link) seatT
  smpIs : ∀ (z : P) (s : Desc.First.S) i, smp s i = smpT (z, s) (callsSending x D rad seatT) i

variable {x D rad seatT smpT smp ms N m}

theorem ListSits.smpEq (T : ListSits G x D rad seatT smpT smp ms N m) (z : P) :
    smp = fun s => smpT (z, s) (callsSending x D rad seatT) :=
  funext fun s => funext fun i => T.smpIs z s i

/-- **cf.** -/
theorem calls_cf (T : ListSits G x D rad seatT smpT smp ms N m) (pi : P) (i) (s : Desc.First.S)
    (y : Strs) (h : noCollJT D.codes G smpT ms (seatT i).1 (seatT i).2 (pi, s) y) :
    CfAt G D.codes (sigListCalls D rad x.link) seatT smp i s y := by
  obtain ⟨z, hz, hA⟩ := T.some i
  have hs : SitsAt z (seatT i).1 (seatT i).2 := hA.2
  rw [T.smpEq G pi]
  exact (cf_move D.codes G smpT z ⟨callsSending x D rad seatT, i⟩ hA (pi, s)
    (T.bySeat (pi, s) _ _ hA) y).1 (h z hz hs)

/-- **pinIn.** -/
theorem calls_pinIn (T : ListSits G x D rad seatT smpT smp ms N m) (pi : P) (s : Desc.First.S)
    (y : Strs) (w : Desc.Wit Cells Tok MsgT)
    (h : ∀ t ∈ N.sent m 0, pinJT D.codes G arr smpT ms t.1 t.2 (pi, s) y w) :
    PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) s y w := by
  rw [T.smpEq G pi]
  refine ⟨T.fits, fun i _ => ?_⟩
  obtain ⟨z, hz, hA⟩ := T.some i
  have hs : SitsAt z (seatT i).1 (seatT i).2 := hA.2
  exact (pin_move D.codes G arr smpT z ⟨callsSending x D rad seatT, i⟩ hA (pi, s)
    (T.bySeat (pi, s) _ _ hA) y w).1 ((h (seatT i) (T.sent i)).2 z hz hs)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_cf
#print axioms VerifiableInference.OnPublicFiles.calls_pinIn
