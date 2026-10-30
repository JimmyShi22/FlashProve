-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ShJointAtAll.lean: hJ : Sh.Joint A O
(Johnson/Desc/K14/Law/SharedConstJoint.lean) AT THE TWO TABLES' CLOSED LETTERS: A := the shared
table's parameters at the seat (planAt Zp Np (seatF …)), O := its open letters at the seat
(Sh.openAt) with the first table's five laid at the closed constant: N₁ := At.N Zp cF ·
links := At.links · Mg₁ := P5J.mgAtAll h · smp₁ := e ▸ At.smp Zp · ms₁ := At.ms Zp Z.lay. One
definition, four theorems.

  heq_cast         a value against itself carried along an equation of its type's index.
  matN_is          the shared table's matrix by numbers is the first table's (cellAtNo).
  hn_of_lin        the first table's shape has the configuration's number of rows: from hlin and
                   the head's own test on the shape (h.plan.shape; full_nums).
  Sh.joint_atAll   **Sh.Joint there.** Of Sh.joint_mgAll_within's eleven
                   (ShJointWithin.lean): hMg · hG · harr · hms · hPw · hw: rfl · hcs :=
                   e · hsmp := heq_cast · hmat: rfl with matN_is · hn := hn_of_lin. LEFT: e (At.cs
                   Zp = A.Q.codes: NOT rfl: held in scope elsewhere, not shown, at the price of the
                   door's two pins) · hlin ((K13.whereOf Zp).lin = A.Q.par.S: NOT rfl: in scope at
                   the same price) · hW (at what O.R holds of, not failed, pileWithinC accepts).
What is not claimed. That AtMgA can be met at the release's own files. e · hlin · hW. Nothing on
soundness.

-/
import Johnson.Desc.AtSeats.ShJointWithin
import Johnson.Desc.K14.Law.SharedConstFirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles (kcReq)
open VerifiableInference.Desc (Chain First.S)
open VerifiableInference.Desc.Sound (CellsQ mgBase Sending)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.K13.Law (matBy cellAtNo)
open P5J (AtMgA mgAtAll colsAt)

/-- A value against itself carried along an equation of its type's index. -/
theorem heq_cast {ι : Type} {T : ι → Type} {a b : ι} (e : a = b) (f : T a) : HEq f (e ▸ f) := by
  subst e
  rfl

namespace Sh

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The shared table's matrix by numbers is the first table's. -/
theorem matN_is (c : CellsQ numsFull.rows (colsAt numsFull)) :
    matN (frS.toDecR frZ 402653181) numsFull c = cellAtNo c := rfl

/-- The first table's shape has the configuration's number of rows. -/
theorem hn_of_lin (h : AtMgA o Z D r Zp Np cF x)
    (hlin : (VerifiableInference.Desc.K13.whereOf Zp).lin = (planAt Zp Np (seatF o Zp Np (secondAt
        Zp Np) cF)).Q.par.S) :
    h.𝔇.P13.lin.matrixRows = numsFull.rows := by
  have h1 := congrArg MatrixNums.rows (full_nums _ h.plan.shape)
  show (VerifiableInference.Desc.K13.whereOf Zp).lin.matrixRows = numsFull.rows
  rw [hlin]
  exact h1.symm

/-- **Sh.Joint at the shared and the first table's closed letters.** -/
theorem joint_atAll (h : AtMgA o Z D r Zp Np cF x) (e : P5J.At.cs Zp = (planAt Zp Np (seatF o Zp
    Np (secondAt Zp Np) cF)).Q.codes)
    (hlin : (VerifiableInference.Desc.K13.whereOf Zp).lin = (planAt Zp Np (seatF o Zp Np (secondAt
        Zp Np) cF)).Q.par.S)
    (hW : ∀ p, (openAll h e).R p → ((openAll h e).get p).2.failed = none →
      VerifiableInference.Desc.K13.pileWithinC ((openAll h e).get p).2 = true) :
    Joint (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h e) :=
  joint_mgAll_within _ (openAll h e) h.𝔇 mgBase rfl e rfl rfl (heq_cast (T := fun c => ProofFile.InstPub
      × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf c s.l).om i).Smp) e (P5J.At.smp Zp)) rfl rfl
    rfl (hn_of_lin h hlin) (fun c => by
      rw [show (openAll h e).matC c = cellAtNo c from matN_is c]
      rfl) hW

end Sh

end Desc.K14.Law
