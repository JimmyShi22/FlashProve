-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/RunsMember.lean: The kind "lookup" (K3): A STEP ON THE ROAD TO A MEMBER OF THE
PREMISE ON A RUN (PlainOk, RunOk; Johnson/Top/H/Keep/RunsLetters.lean): IT DOES NOT SETTLE WHETHER
THAT PREMISE RANGES OVER NOTHING: IT CARRIES THE QUESTION from K3's promise on the fixed part
(K3Ok: a sentence with rounds and end values in it) TO SIX PLAIN FACTS ON ONE RECORD e: what the
lookup heard is still read there; the lens reads a part; its ledger is later than the one that the
yes left, and has its sizes; the batching's draw has run; one coefficient a slot. Definitions,
statements and proofs.

OBJECT: K3.block's decide and the run "objects" (Johnson/Desc/First/Look/K3Lookup.lean; objectsRun,
  Johnson/Top/H/K3RunsLaw.lean) at seatCalls with the plain maker of claims; the lens atS.
Used by Johnson/Desc/First/Link/Law/KxAtFront.lean and Johnson/Desc/First/Link/Law/KxOfTable.lean.
LETTERS: phi := fun s => s.lookHeard?, hd := id, Ok := K3Ok id lm F.next, F the ledger in front of
  the yes; Fu free.
Compiled with the whole library.

Main names:
  ok_of_shapeOf: a shape that is made of the calls meets the library's bounds.
  k3Ok_of_left: what a yes leaves (K3Left, Johnson/Top/H/K3LeftStatement.lean) gives K3's promise on
    the fixed part, at every snapshot whose ledger is later and has its sizes.
  Ranges phi Ok r: there are q, front, e, a, c, e1 that meet PlainOk's five premises at the run r.
  objects_ranges: from what a yes left, and a record e with the six facts: Ranges at "objects".
  objects_ranges_of_yes: the same from the yes itself.

Limits. THE SIX FACTS ON e ARE SHOWN NOWHERE HERE, AT NO RECORD, MADE UP OR REAL. In the chain the
lookup's block stands IN FRONT OF the batching's draw: so e is not the record behind the yes but a
later one; that the blocks between keep what was heard and leave a later ledger is each kind's. The
rounds' words are below the prime; the ledger in front of the yes has its sizes: premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsLetters
import Johnson.Top.H.K3CEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (Pub9 pubOf Fx9 good9 goesOn_refl)

/-- A shape that is made of the calls meets the library's bounds. -/
theorem ok_of_shapeOf {calls : Array Call} {pub : Array Nat} {lid : ℕ} {h : Shape}
    (a : ShapeOf calls pub lid h) : FoNums.ok h = true := by
  obtain ⟨h0, hs, ha, rfl⟩ := a
  exact Cb.Fo.shape_ok hs ha

/-- **What a yes leaves gives K3's promise on the fixed part.** -/
theorem k3Ok_of_left {h : Shape} {lm : ℕ} {F F' : Fork} {g : Heard} {rs : Rounds GE}
    (L : K3Left Reading.gl h lm F F' g rs) (hok : FoNums.ok h = true) (u : Pub9)
    (hL : _root_.Fo.Later F' u.F) (hS : Sized u.F) :
    K3Ok id lm F.next ((some g : Option Heard), some u) := by
  intro g0 u0 hg hu
  obtain rfl : g = g0 := Option.some.inj hg
  obtain rfl : u = u0 := Option.some.inj hu
  refine ⟨hS, by rw [L.shape]; exact hok, rs, rfl, F', u, rfl, ?_, hL⟩
  rw [L.shape]
  exact L.heardIs

/-- PlainOk's five premises are met together somewhere. -/
def Ranges {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (r : ℕ → S → Except String (List Desc.Claim × S)) : Prop :=
  ∃ q front e a c e₁, Fx9 φ Ok q e ∧ good9 e ∧ atS.get? e = some a ∧ a.F.LS.size = a.F.ns ∧
    r front e = .ok (c, e₁)

/-- **From what a yes left, at a later record.** -/
theorem objects_ranges {h : Shape} {lm : ℕ} {F F' : Fork} {g : Heard} {rs : Rounds GE}
    (L : K3Left Reading.gl h lm F F' g rs) (hok : FoNums.ok h = true) (e : S) {a : Desc.K9.Part}
    (hg : e.lookHeard? = some g) (ha : atS.get? e = some a) (hLt : _root_.Fo.Later F' a.F)
    (hSz : Sized a.F) (hh : a.L.handed = true) (hLS : a.F.LS.size = a.F.ns) :
    Ranges (fun s : S => s.lookHeard?) (K3Ok id lm F.next) (objectsRun (seatCalls plain)) := by
  refine ⟨(some g, some (pubOf a)), 0, e, a, g.rows.toList.map plain,
    e.putFork (a.F.paid g.owedObjects),
    ⟨k3Ok_of_left L hok (pubOf a) hLt hSz, hg, pubOf a, a, rfl, ha, goesOn_refl a⟩,
    ⟨a, ha, hh, hLS⟩, ha, hLS, ?_⟩
  show objectsRun (seatCalls plain) 0 e = _
  unfold objectsRun
  have f1 : (seatCalls plain).fork e = some a.F := fork_of_atS ha
  have f2 : (seatCalls plain).heard e = some g := hg
  rw [f1, f2]
  rfl

/-- The same from the yes itself. g, F': what the yes left, as the record behind it reads them. -/
theorem objects_ranges_of_yes (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Desc.Claim)) (h : Shape)
    (hp : p.shape = some h) (lm : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (seatCalls plain) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) (e : S) {a : Desc.K9.Part}
    (hg : e.lookHeard? = s'.lookHeard?) (ha : atS.get? e = some a)
    (hLt : ∀ F', s'.fork? = some F' → _root_.Fo.Later F' a.F) (hSz : Sized a.F)
    (hh : a.L.handed = true) (hLS : a.F.LS.size = a.F.ns) :
    Ranges (fun s : S => s.lookHeard?) (K3Ok id lm F.next) (objectsRun (seatCalls plain)) := by
  obtain ⟨F0, F', g, e0, e1, e2, hK⟩ :=
    k3LeavesAtCalls Desc.Claim plain piece laid before p guests h hp GE Reading.gl lm s s' rs cols
      hw hd
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans e0)
  exact objects_ranges (hK hS) (ok_of_shapeOf (shape_some p h hp)) e (hg.trans e2) ha (hLt F' e1)
    hSz hh hLS

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3Ok_of_left
#print axioms VerifiableInference.OnPublicFiles.objects_ranges
#print axioms VerifiableInference.OnPublicFiles.objects_ranges_of_yes
