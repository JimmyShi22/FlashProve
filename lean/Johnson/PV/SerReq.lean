-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/SerReq.lean: **sX: A SERIALISER OF THE REQUESTS, WITH CODE AND ITS TWO LAWS**, general in
  the model's sizes P: `sXAt P : Ser (ReqAt P)`. In the library `sX : Ser (ReqAt sizesSmall)` | `Ser
  Flat.Req` is a letter in every file that names it: no value stood anywhere.
WHAT FOR: the total code behind the escape (ArmBack.backL2 … : StrCode) asks a serialiser of a typed
  instance: Ser.prod (Ser.option sX) (Ser.prod serRec serRec). With sX a value, PV.MSmall.bkS sX
  serL | PV.MFull.bkF are values.
THE MAKE: a request is a record of four (Inst/Model/Program.lean:469): T tokens below V · the token
  y · the two numbers r, e below T + 1: written in that order, each in the library's fixed width
  (Ser.fin); the subtype's test (WellFormedAt) is asked at reading.
  vec n A       n elements in a row: a function on Fin n (over the library's putAll | getN and their
    two laws)
  sub p A       the elements that pass a decidable test
  instEquiv P   the record as a tuple
  serInst P · **sXAt P** · sXS := sXAt sizesSmall · sXF := sXAt Inst.Model.ppref
A Ser's two laws are fields of the record: a value cannot be written without them: they are proved
  here. IT IS NOT THE FORMAT's REQUEST FILE: no byte of it is hashed in an honest run: it is read
  behind the escape alone.


-/
import Iop.Ser
import Johnson.Flat.ClaimsTrue
import Johnson.Flat.ClaimsSizes

set_option autoImplicit false

namespace PV.SerReq
open _root_.Iop OnBytes.Flat Inst.Model

variable {α : Type}

/-- n elements in a row. -/
def vec (n : ℕ) (A : Ser α) : Ser (Fin n → α) where
  put f := Ser.putAll A (List.ofFn f)
  get s := (Ser.getN A n s).bind fun x =>
    if h : x.1.length = n then some (fun i => x.1[i.val]'(by rw [h]; exact i.isLt), x.2) else none
  get_put f rest := by
    have hl : (List.ofFn f).length = n := List.length_ofFn
    have e := Ser.getN_putAll A (List.ofFn f) rest
    rw [hl] at e
    rw [e, Option.bind_some, dif_pos hl]
    congr 2
    funext i
    exact List.getElem_ofFn _
  put_get s f rest h := by
    obtain ⟨⟨l, r⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e1, e2⟩ := Ser.putAll_of_getN A n s l r hl
    subst e2
    rw [dif_pos rfl] at h
    cases h
    rw [e1]
    congr 2
    exact List.ofFn_getElem.symm

/-- The elements that pass a decidable test. -/
def sub (p : α → Prop) [DecidablePred p] (A : Ser α) : Ser {a : α // p a} where
  put x := A.put x.1
  get s := (A.get s).bind fun y => if h : p y.1 then some (⟨y.1, h⟩, y.2) else none
  get_put x rest := by
    rw [A.get_put, Option.bind_some, dif_pos x.2]
  put_get s x rest h := by
    obtain ⟨⟨a, r⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    by_cases hp : p a
    · rw [dif_pos hp] at h
      cases h
      exact A.put_get s a r ha
    · rw [dif_neg hp] at h
      cases h

/-- A request as a tuple. -/
def instEquiv (P : Params) :
    Instance P ≃ (Fin P.T → Fin P.V) × Fin P.V × Fin (P.T + 1) × Fin (P.T + 1) where
  toFun x := (x.prompt, x.y, x.rF, x.eF)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A serialiser of the instances. -/
def serInst (P : Params) : Ser (Instance P) :=
  Ser.ofEquiv (instEquiv P)
    (Ser.prod (vec P.T (Ser.fin P.V)) (Ser.prod (Ser.fin P.V) (Ser.prod (Ser.fin (P.T + 1)) (Ser.fin
        (P.T + 1)))))

/-- **THE VALUE.** -/
def sXAt (P : Params) : Ser (ReqAt P) := sub (fun x : Instance' P => WellFormedAt x) (serInst P)

/-- At the small size. -/
def sXS : Ser (ReqAt sizesSmall) := sXAt sizesSmall

/-- At the full size. -/
def sXF : Ser (ReqAt ppref) := sXAt ppref

end PV.SerReq

#print axioms PV.SerReq.sXAt
