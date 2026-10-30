-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/ReqIns.lean: the bytes of the item `request` in a proof file's first chain query
at the description's own type of instances: from the verifier program's yes to the equation on these
bytes.



Johnson/Maker/Page/ReqPub.lean writes the bytes as a function of a typed instance that holds the
public input, and leaves one premise: the instance of a call holds that call's files.
Johnson/Flat/ItemOf.lean shows, at the instance that is built from the request's and the reply's
files (`insOf`, Johnson/Flat/InsOf.lean): where the program says yes, the two files rebuilt from the
instance are the call's, and the program forms the item. This file joins the two. Definitions and
proofs.
A proof's first statement also takes the request file's bytes, and the page's letter `reqX` gives
two strings (`HoldsPub.req2`, Johnson/Maker/Page/ReqBoth.lean). The equations here are on the first
alone. The pair's equation follows from two clauses of `req_port` (the instance holds the call's
files; the program forms the item) by `req2_early`: it is not stated here.

Main names:
  `holdsIns hV pol lay KL`: `HoldsPub` at `Instance' P`, with `withoutReply hV` as the early part.
  `reqX_itemOf`: its bytes are those of `itemOf` (Johnson/Flat/ItemOf.lean): one term.
  `insOf_options`: the built instance does not hang on the letter o, the options.
  `req_port`: where the program says yes, at the sizes that the parameter file states: the built
    instance i is there, it holds the call's files, the program forms the item, and `reqX
    (withoutReply hV i) = item`.
  `req_port_at`: the same where the record stands at three public files that are fixed beforehand,
    and the call's are these (three pins): so the function into bytes does not hang on the call.
  `req_of_ins`: the same at an instance xi that is NAMED as what `insOf` returns at the call's
    statement: for a caller whose instance is a letter.
What is asked, by name: hp: the program's yes (`K.PortYesAt`). hP: the sizes.

Limits: hP is a premise. `sizesAt` (Johnson/Flat/Instance.lean) refuses every parameter file that
the program's scan refuses, and every one whose acceptance policy (the lines C, theta, cap, sh, sT)
is not the strictest one, exact match: of a call under another policy nothing is said here, though
the program can say yes to one and its item binds these lines too. That the makers' fixed instance
is the built one is the caller's choice. The premise on the page's two strings itself is not stated
here.
One direction only. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Maker.Page.ReqPub
import Johnson.Flat.ItemOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Flat Inst.Model OnBytes.Model OnBytes.Model.Verify
open OnBytes.TieK (ProofPub)

variable {P : Params} (hV : 0 < P.V)

/-- The description's instances hold the public input, at three fixed public files. -/
def holdsIns (pol lay KL : ByteArray) : HoldsPub (Instance' P) (withoutReply hV) :=
  holdsBytes pol lay KL requestBytesOf replyBytesOf (requestBytesOf_withoutReply hV)

/-- One term with Johnson/Flat/ItemOf.lean's. -/
theorem reqX_itemOf (pol lay KL : ByteArray) (x : Instance' P) :
    (holdsIns hV pol lay KL).reqX x = (itemOf pol KL x).getD ByteArray.empty := rfl

/-- The built instance does not hang on the options. -/
theorem insOf_options (F : K.Files) (o o' : Options) :
    insOf P (K.stmOf F o) = insOf P (K.stmOf F o') := rfl

/-- **From the program's yes to the equation.** -/
theorem req_port {F : K.Files} {id : String} {table further : OnBytes.Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) (hP : sizesAt F.pol = .ok P) :
    ∃ (i : Instance' P) (item : ByteArray), insOf P (K.stmOf F o) = some i ∧
      (holdsIns hV F.pol F.lay F.KL).pub i = ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      (holdsIns hV F.pol F.lay F.KL).reqX (withoutReply hV i) = item := by
  obtain ⟨_, i, item, _, _, _, hi, hr, hy, _, hit, _, _⟩ := insOf_port_bytes hp o hP
  have hx : (holdsIns hV F.pol F.lay F.KL).pub i = ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ :=
    holdsBytes_at F.pol F.lay F.KL requestBytesOf replyBytesOf (requestBytesOf_withoutReply hV) i
      ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ rfl rfl rfl hr hy
  exact ⟨i, item, hi, hx, hit, reqX_early _ i _ item hx hit⟩

/-- **The same with the three public files fixed beforehand**: the record, and so the function into
bytes, stands at pol, lay, KL; the call's three public files are these. -/
theorem req_port_at (pol lay KL : ByteArray) {F : K.Files} {id : String}
    {table further : OnBytes.Params.TableName} (hp : K.PortYesAt F id table further) (o : Options)
    (hP : sizesAt F.pol = .ok P) (h1 : F.pol = pol) (h2 : F.lay = lay) (h3 : F.KL = KL) :
    ∃ (i : Instance' P) (item : ByteArray), insOf P (K.stmOf F o) = some i ∧
      (holdsIns hV pol lay KL).pub i = ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      (holdsIns hV pol lay KL).reqX (withoutReply hV i) = item := by
  subst h1 h2 h3
  exact req_port hV hp o hP

/-- **At the instance that is built from the call, named**: xi is no free letter: it is what `insOf`
returns at the call's statement. -/
theorem req_of_ins (pol lay KL : ByteArray) {F : K.Files} {id : String}
    {table further : OnBytes.Params.TableName} (hp : K.PortYesAt F id table further) (o : Options)
    (hP : sizesAt F.pol = .ok P) (h1 : F.pol = pol) (h2 : F.lay = lay) (h3 : F.KL = KL)
    (xi : Instance' P) (hxi : insOf P (K.stmOf F o) = some xi) :
    ∃ item : ByteArray,
      (holdsIns hV pol lay KL).pub xi = ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      (holdsIns hV pol lay KL).reqX (withoutReply hV xi) = item := by
  obtain ⟨i, item, hi, hx, hit, he⟩ := req_port_at hV pol lay KL hp o hP h1 h2 h3
  obtain rfl : i = xi := Option.some.inj (hi.symm.trans hxi)
  exact ⟨item, hx, hit, he⟩

end Johnson.Session
