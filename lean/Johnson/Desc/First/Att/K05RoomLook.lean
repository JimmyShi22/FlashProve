-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RoomLook.lean: the ledger's room (`Room`,
Johnson/Desc/First/Att/K05Room.lean) behind the lookup's hearing, from the library's record of what
a run of the lookup's routine leaves in the ledger (`PadLeft`,
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean).

Statements and proofs.
Main names:
  `room_of_padLeft`: `PadLeft` h F F' g and room for Forest.elems h + k in F give room k in F', at
    the same ns, the next free number moved on by Forest.elems h. By the fields next, fit, beyond
    and rest.
  `room_two`: so behind the lookup's hearing and the hearing of the kind K5 (`room_behind`).
Used: `PadLeft`, `Filled`, `Room`, `room_behind`, `Free`; no routine in a context.
Limits: that the text of the lookup's kind leaves `PadLeft` is not shown in this file or in what it
imports (the library has `PadLeft` for a run of the routine `Forest.pad`). Nothing is claimed
on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoHeard
import Johnson.Desc.First.Att.K05Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part.MaskedSum (Free)

/-- **The lookup's hearing hands the ledger's room on.** -/
theorem room_of_padLeft {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard} {ns nx k : Nat}
    (L : Fo.PadLeft h F F' g) (R : Room F ns nx (Forest.elems h + k)) : Room F' ns (nx + Forest.elems h) k := by
  obtain ⟨rfl, rfl, hz, hf⟩ := R
  obtain ⟨f1, f2, f3⟩ := L.fit
  have hns : F'.ns = F.ns := L.rest.2.1
  refine ⟨hns, L.next, ⟨f1, f2, f3⟩, f3, by rw [hns]; have := hf.2.1; omega, fun j h1 h2 => ?_⟩
  have hF : F.gotF.getD j true = false := hf.2.2 j (by omega) (by omega)
  have hj : j < F.ns := by have := hf.2.1; omega
  have hb := L.beyond j h1
  unfold OnBytes.PscRun.Filled at hb
  have a1 : F.gotF.getD j false = F.gotF.getD j true := by
    simp [Array.getD_eq_getD_getElem?, show j < F.gotF.size by rw [hz.got]; exact hj]
  have a2 : F'.gotF.getD j false = F'.gotF.getD j true := by
    simp [Array.getD_eq_getD_getElem?, show j < F'.gotF.size by rw [f3, hns]; exact hj]
  rw [a1, a2, hF] at hb
  cases hv : F'.gotF.getD j true with
  | false => rfl
  | true => exact absurd (hb.1 hv) (by simp)

/-- Behind the lookup's hearing and the hearing of the kind K5. -/
theorem room_two {h : Forest.Shape} {F F' G : Fork} {g : Forest.Heard} {ns nx k lead lead' : Nat}
    {x : Params.AttentionRounds} {rs rs' : List Fmt.RoundView} {hd : Heard} (L : Fo.PadLeft h F F' g)
    (hh : hear x (F', rs, lead) = some (hd, G, rs', lead'))
    (R : Room F ns nx (Forest.elems h + (slotsOf (script x) + k))) :
    Room G ns (nx + Forest.elems h + slotsOf (script x)) k :=
  room_behind hh (room_of_padLeft L R)

end VerifiableInference.Desc.First.Att.P
