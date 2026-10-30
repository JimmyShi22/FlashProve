-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/BatSize.lean: what is public of the round before a proximity test's first fold
(`Cb.Pv.Bat.Size`, Cb/Pv/Bat.lean), over a group of Johnson/Pack/Group.lean; its three conditions
from a test on numbers.

The kind BAT (Johnson/Top/H/Bat.lean) asks of a caller the record `Cb.Pv.Bat.Size` and the
conditions `BatOKAt`: the coefficients evade zero, the lists of the group's code are bounded, the
joint radius implies each member's own. Johnson/Pack/Group.lean has the group `grpOf` over the
family `sigOf cs l`, with the second and the third condition from numbers. Here they are laid into
the kind's record. Definitions, statements and proofs; nothing on a group or a block is proved
anew.

Main names:
  `MemberFits cs A e d s e'`: the test on one member with the shape s and the radius e',
    decidable: its length 2 ^ a is at most 2 ^ A; its codes' numbers are in order (`CodeOK`); d ≤
    2 ^ (A - a) times its own distance (`dOf`); e ≤ 2 ^ (A - a) e' + (2 ^ (A - a) - 1).
  `batSize …`: the record: the family `sigOf cs l`, the group `grpOf cs l mem A e`, the kept
    members by a test, the open rows (names B, states Sb, forms sl), the powers of one element as
    coefficients at a numbering f of the rows below `rows`, and the bound `listMax (2 ^ A) d e` on
    the lists.
  `batSize_ok`: `BatOKAt` of it, if f is injective, the group has a member, every member meets
    `MemberFits`, and e is below the Johnson radius of 2 ^ A and d.
  `batCaller`, `batCaller_ok`: a caller of the kind at that size, at any joint on the kept
    messages; `BatOK` of the list that holds it alone.

Which fields are numbers: A, e, d, rows, the two tests. Which are made from numbers: the family,
the group, the coefficients (`Cb.Pv.Bat.powersZ`), the bound. Which are parameters here: the open
rows' names, states and forms; the numbering f.

Limits: those of Johnson/Pack/Group.lean. That the forms and the numbering are the programs' is
not said. No list is written here.
-/
import Johnson.Pack.Group
import Johnson.Top.H.Bat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR OnBytes.Slice VerifiableInference.OnPublicFiles

/-- The test on one member. -/
structure MemberFits (cs : OnBytes.Codes) (A e d : ℕ) (s : OnBytes.OracleShape) (e' : ℕ) :
    Prop where
  le : aOf cs s ≤ A
  ok : CodeOK cs s
  dist : d ≤ 2 ^ (A - aOf cs s) * dOf cs s
  near : e ≤ 2 ^ (A - aOf cs s) * e' + (2 ^ (A - aOf cs s) - 1)

instance (cs : OnBytes.Codes) (A e d : ℕ) (s : OnBytes.OracleShape) (e' : ℕ) :
    Decidable (MemberFits cs A e d s e') :=
  decidable_of_iff (aOf cs s ≤ A ∧ CodeOK cs s ∧ d ≤ 2 ^ (A - aOf cs s) * dOf cs s ∧
      e ≤ 2 ^ (A - aOf cs s) * e' + (2 ^ (A - aOf cs s) - 1))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.le, h.ok, h.dist, h.near⟩⟩

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (A e : ℕ)
  (keep : Fin l.length → Prop) [DecidablePred keep] (B : Type) [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (grpOf cs l mem A e).C.J) (d rows : ℕ)
  (f : (grpOf cs l mem A e).Row B → Fin rows)

/-- What is public of the round. -/
noncomputable def batSize : Cb.Pv.Bat.Size GE where
  S := sigOf cs l
  G := grpOf cs l mem A e
  keep := keep
  B := B
  Sb := Sb
  sl := sl
  Z := Cb.Pv.Bat.powersZ rows f
  L := listMax (2 ^ A) d e

/-- Its conditions, from the test on numbers. `_hne` is not used by the proof: without a member
nothing binds d, and the conditions would hold of a group whose code has no row. -/
theorem batSize_ok (hf : Function.Injective f) (_hne : ∃ i, mem i)
    (hM : ∀ i, mem i → MemberFits cs A e d (l.get i).1 (l.get i).2)
    (hJ : InJohnson (2 ^ A) d e) : BatOKAt (batSize cs l mem A e keep B Sb sl d rows f) where
  z := Cb.Pv.Bat.powersZ_ok rows f hf
  list := grp_list cs l mem A e (fun i hi => (hM i hi).le) (fun i hi => (hM i hi).ok) d
    (fun i hi => (hM i hi).dist) hJ
  fits := grp_fits cs l mem A e (fun i hi => (hM i hi).le) fun i hi => (hM i hi).near

/-- A caller of the kind BAT at that size. -/
noncomputable def batCaller {Kc St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀
      ((((batSize cs l mem A e keep B Sb sl d rows f).S.sub
        (batSize cs l mem A e keep B Sb sl d rows f).kp)).Msg × Wp)) : BatCaller GE :=
  ⟨batSize cs l mem A e keep B Sb sl d rows f, Kc, St₀, Wp, E₀, A₀⟩

/-- The kind's condition at the list that holds this caller alone. -/
theorem batCaller_ok (h : BatOKAt (batSize cs l mem A e keep B Sb sl d rows f))
    {Kc St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀
      ((((batSize cs l mem A e keep B Sb sl d rows f).S.sub
        (batSize cs l mem A e keep B Sb sl d rows f).kp)).Msg × Wp)) :
    BatOK [batCaller cs l mem A e keep B Sb sl d rows f A₀] := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact h

end

end Johnson.Pack

#print axioms Johnson.Pack.batSize_ok
#print axioms Johnson.Pack.batCaller_ok
