-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorMkAtS.lean: K9's "THE ONE EQUATION" AT THE FIRST CHAIN's STATE:
WHAT IT DOES TO THE MAKES OF THE STATEMENT's ROWS (formsOf, Johnson/Desc/First/Shape/Forms.lean), AS
A FUNCTION OF THE CHAIN's SHAPE AND THE MAKES IN FRONT. Over DoorMkRow.lean. A general law, from a
yes alone; nothing is evaluated.

  `termsMk_blank`, `eqMk_blank`: the makes read numbers of the frame of the calls alone: at the
    frame made anew of its shape they are the same.
  **`eqFormsU a Fm`**: THE UPDATE: off the shape's link (the layout; the frame; the table of arrays;
    the number of listed arrays), its ledger (the arrays' shapes; the number of slots) and its core
    (the numbers of bits of the messages' main tables): the row's make (eqMk), laid behind the open
    rows of the link's group. `eqForms`: the same as a total function: where the update refuses: Fm.
  **`one_forms`**: a yes of the bare sub-protocol from s to t gives
    eqFormsU (chainSh s) (formsOf s.st) = some (formsOf t.st). `one_forms'`: so
    formsOf t.st = eqForms (chainSh s) (formsOf s.st).

Limits. From a yes alone; the bare sub-protocol. WITHOUT A YES IN HAND "some" IS NO SIGN OF ONE:
eqFormsU's own text calls neither of the door's tests eqB and doorB (DoorCut.lean): it refuses only
where the link or the ledger is missing or eqMk refuses; at a group outside the makes' list it
answers the makes unchanged; an array, an entry or a message that is not there reads as empty or 0.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.DoorMkRow
import Johnson.Desc.First.Batch.Shape.BatchDraw
import Johnson.Desc.First.Shape.SwitchRowsMk
import Johnson.Desc.Ground.Shape.More

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

theorem termsMk_blank (layout : ReqLayout) (f : ReqFrame) (rb pb : Nat → Nat) :
    ∀ (ts : List TermSh) (acc : List MainMk),
      termsMk layout (frameSh f).blank rb pb ts acc = termsMk layout f rb pb ts acc
  | [], _ => rfl
  | t :: ts, acc => by
    unfold termsMk
    have e : ∀ born m, messageNow (frameSh f).blank born m = messageNow f born m :=
      fun _ _ => rfl
    simp only [e, termsMk_blank layout f rb pb ts]

theorem eqMk_blank (layout : ReqLayout) (f : ReqFrame) (rb pb : Nat → Nat) (ts : List TermSh)
    (n : Nat) : eqMk layout (frameSh f).blank rb pb ts n = eqMk layout f rb pb ts n := by
  unfold eqMk
  rw [termsMk_blank]
  rfl

/-- **THE UPDATE OF THE MAKES.** -/
def eqFormsU (a : ChainSh) (Fm : FormsSh) : Option FormsSh :=
  match a.link, a.led with
  | some L, some F =>
    (eqMk L.check.rows.layout L.check.frame.blank (rowBitsS a.core.st · .main)
      (fun o => Ground.Sh.tableBitsS a.core.st o .main - rowBitsS a.core.st o .main)
      (termsShS L.arrayOf L.list.nt.size F.trees) F.ns).map fun mk =>
        { Fm with groups := Ground.Sh.modAt Fm.groups L.check.frame.group (· ++ [mk]) }
  | _, _ => none

/-- The same, total. -/
def eqForms (a : ChainSh) (Fm : FormsSh) : FormsSh := (eqFormsU a Fm).getD Fm

variable {Cl : Type}

theorem one_forms (p : Where) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t) :
    eqFormsU (chainSh s) (formsOf s.st) = some (formsOf t.st) := by
  obtain ⟨P, o, hP, ho, rfl⟩ := (one_iff p s t rs gs).1 h
  obtain ⟨l1, l2, -, -, -, l6⟩ := part_sh hP
  obtain ⟨mk, hm, hf⟩ := door_forms _ _ _ _ _ _ ho
  rw [l6] at hm hf
  unfold eqFormsU
  rw [l1, l2]
  show (eqMk P.L.check.rows.layout (frameSh P.L.check.frame).blank
    (rowBitsS (Ground.Sh.stSh s.st) · .main)
    (fun o => Ground.Sh.tableBitsS (Ground.Sh.stSh s.st) o .main -
      rowBitsS (Ground.Sh.stSh s.st) o .main)
    (termsShS P.L.arrayOf P.L.list.nt.size (P.F.trees.toList.map treeSh)) P.F.ns).map _ = _
  have e1 : (rowBitsS (Ground.Sh.stSh s.st) · .main) = (s.st.rowBits · .main) := by
    funext o
    exact (rowBits_sh s.st o .main).symm
  have e2 : (fun o => Ground.Sh.tableBitsS (Ground.Sh.stSh s.st) o .main -
      rowBitsS (Ground.Sh.stSh s.st) o .main) = (s.st.placeBits · .main) := by
    funext o
    rw [Ground.Sh.tableBitsS_eq, ← rowBits_sh]
    show s.st.rowBits o .main + s.st.placeBits o .main - s.st.rowBits o .main = _
    exact Nat.add_sub_cancel_left _ _
  rw [e1, e2, eqMk_blank, hm]
  show some _ = some (formsOf o.d.st)
  rw [hf]
  rfl

theorem one_forms' (p : Where) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t) :
    formsOf t.st = eqForms (chainSh s) (formsOf s.st) := by
  unfold eqForms
  rw [one_forms p s t rs gs h]
  rfl

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.eqMk_blank
#print axioms VerifiableInference.Desc.K9.Shape.one_forms
#print axioms VerifiableInference.Desc.K9.Shape.one_forms'
#print axioms VerifiableInference.Desc.K9.Shape.termsMk_blank
#print axioms VerifiableInference.Desc.K9.Shape.eqFormsU
#print axioms VerifiableInference.Desc.K9.Shape.eqForms
