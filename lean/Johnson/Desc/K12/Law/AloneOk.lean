-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/AloneOk.lean: a test on the record of the proximity test (the kind K12): no
member of the group under test shares the first mask's tree.

Definitions with code; no theorem. It can be compiled and run.
Why. Where the first fold sends its own mask, the law reads the mask's table off the chain's first
message. DeepK (Johnson/Desc/K12/Law/K12Lemma.lean) asks that a member which shares the mask's tree
sees the same table whatever that message is: at that letter this can hold only where no member
shares the tree. Johnson/Desc/K12/Law/TabsView.lean takes the yes of this test as a premise.
Main names:
  `aloneOk D`: each member's tree stands at another place of the book than the mask's.
  `aloneAt p t`: the same at the plain data that gpOf makes of the record t behind the batching;
    none where there are no plain data.
  `shared D`: the control's data: the first member's tree is laid at the mask's place.
  `aloneLines`: two lines of text: the test, with the places; the control, which is due false where
    the group has a member.
Limits: aloneOk has been evaluated nowhere yet. Evaluated is not proved. That the test's own mask's
tree is entered behind all the members' is not proved from the text that enters it. Where the mask
is not the test's own the law does not ask this test: the line says so. No soundness is claimed, and
nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.FirstOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- No member of the group under test shares the mask's tree. -/
def aloneOk (D : Plain) : Bool := D.mems.all fun m => m.t != D.fresh.t

/-- The plain data of the record behind the batching, as lastL takes them. -/
def plainAt (p : P12) (t : T12) : Option Plain :=
  match p.nums.stages, t.pass with
  | a :: _, .claim _ L => gpOf p t a L
  | _, _ => none

def aloneAt (p : P12) (t : T12) : Option Bool := (plainAt p t).map aloneOk

/-- The control's data: the first member's tree is laid at the mask's place. -/
def shared (D : Plain) : Plain :=
  { D with mems := match D.mems with
      | m :: r => { m with t := D.fresh.t } :: r
      | [] => [] }

def aloneLines (tagS : String) (p : P12) (t : T12) : List String :=
  let asked : String :=
    if p.nums.ownMask then "ownMask true: asked" else "ownMask false: not asked"
  match plainAt p t with
  | some D =>
    [tagS ++ ".ALONE\taloneOk " ++ toString (aloneOk D) ++ "\t" ++ asked ++
        "\tthe record names a mask: " ++ toString t.mask.isSome ++
        "\tthe members' trees' places " ++ toString (D.mems.map (·.t)) ++ " · the mask's " ++
        toString D.fresh.t,
     tagS ++ ".ALONE.control\tthe first member's tree laid at the mask's place\t" ++
        toString (aloneOk (shared D)) ++ "\tmembers " ++ toString D.mems.length]
  | none => [tagS ++ ".ALONE\tno plain data\t" ++ asked]

end H2K.First
