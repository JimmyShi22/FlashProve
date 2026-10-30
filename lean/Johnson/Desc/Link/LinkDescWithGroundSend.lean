-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkDescWithGroundSend.lean: A MIDDLE TERM OF THE LAWS' PROOFS, SEATED, RUN AND WALKED NOWHERE:
the entry file's link in its elder text: the same eight blocks as
Johnson/Desc/Link/LinkDesc.lean's but for block 2,
"send o_0, o_1", which here decides by the plain ground's sendP (Johnson/Desc/Ground/Calls.lean),
over `verify-on-bytes`'s pure functions Send.form | Send.pad by name.
WHY IT STAYS. The library's record of facts on a link's five rounds (LinkRanR), on which its proved
soundness stands, speaks of Send.form's rows. K15's law («hands on») and hsem are proved of THIS
text; the tie
(Johnson/Desc/K15/SendOwnLaw.lean | SendOwnPaid.lean) says: where the description that is seated
says yes, this one says yes, at the same record; so they hold of the seated one
(Johnson/Desc/K15/HsemAtV.lean).
It stands in no top statement, and no definition that is seated names it.
  send · blocks · blocksOr · chainOf · descOf · linkDesc      the texts, taken out of K15/K15.lean
  and Link/LinkDesc.lean to the letter
Definitions with code (they have ridden; nobody need run them). No theorem.
-/
import Johnson.Desc.Link.LinkDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14 (Round Says)
open VerifiableInference.Desc (Block Chain Place KindName OneChainFileDescription roundlessBlock)
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)
open VerifiableInference.Desc.Ground (Clauses)

/-- o_0 and o_1 go out in one prover's message by a sending: THE TEXT THAT THE LAWS' PROOFS PASS
THROUGH: the plain ground's sendP. (The seated text's: the kind K1's own block:
Johnson/Desc/Link/LinkDesc.lean: sendK1.) -/
def send (p : Par15) (d : St) : List Fmt.RoundView → Option St
  | [r₁, r₂] => do
    let (ids, _, _, _, d) ← sendP groundG p.gp true d (linkMessage p.S p.samples) r₁ r₂
    behind p d ids
  | _ => none

/-- **The five blocks in front of the test**; nothing where the rounds cannot be said. G is the
chain's group 0; the one
tree is the chain's message 0. -/
def blocks (P : P15) : Option (List (Block St Unit)) := do
  let es ← entries P
  let p := P.par
  let plain (n : String) (i : Nat) (kind : KindName) (first k : Nat)
      (oracles : List (List VerifiableInference.Desc.Oracle)) (before : List (Nat × Nat))
          (l : St → Clauses)
      (f : St → List Fmt.RoundView → Option St) : Block St Unit :=
    { name := n, place := ⟨1, none, i, kind⟩, planOk := true
      rounds := ((es.drop first).take k).map fun e => { entry := e }
      oracles := oracles, before := before, decide := fun d rs _ => why (l d) (f d rs)
      claims := [], after := [] }
  pure
    [plain "LINK point" 1 .K15 0 1 [[]] [] (fun _ => []) (point p),
     plain "send o_0, o_1" 2 .K1 1 2
       [Desc.K14.oraclesOf P.codes (sent P) ([[0], [0]] ++ if P.S.masksAhead then [[]] else []), []]
           []
       (fun _ => []) (send p),
     plain "(rec_gamma), twice" 3 .K15 0 0 [] [] (fun d => laysRecL p d.loc) (laysRec p),
     { name := "LINK", place := ⟨1, none, 4, .K15⟩, planOk := true
       rounds := ((es.drop 3).take 1).map fun e => { entry := e, stored := readsAtLink P.S }
       oracles := [[]], before := [(1, 0)], decide := fun d rs gs => why [] (link p d rs gs)
       claims := [], after := [] },
     plain "LINK phi" 5 .K15 4 1 [[]] [(1, 0)] (fun _ => []) (phi p)]

/-- The five blocks; where the rounds cannot be said, one block that fails its test on the plan. -/
def blocksOr (P : P15) : List (Block St Unit) :=
  (blocks P).getD
      [{ roundlessBlock "the kind's rounds cannot be said" 1 none 1 .ok with planOk := false }]

/-- **The chain.** The end is handed the very list that is laid in front of it. -/
def chainOf (P : P15) : Chain St Unit :=
  let inFront := blocksOr P ++ [testBlock P]
  { first := frontBlock P, front := [], links := []
    back := inFront, last := chainEnd 1 7 false (inFront.flatMap (·.rounds)) fun d => untestedL d.st }

/-- The description at any parameters and any plan's declared rounds. ok: the file's own public test
(`OneChainFileDescription.fileOk`): WITHOUT A DEFAULT:
whoever makes a description says what it is. -/
def descOf (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) : OneChainFileDescription (TableKey × TableKey) :=
  { S := St, Cl := Unit, plan := plan, tableDepth := P.S.table.tree.a, tables := 2, fileOk := ok
    okStart := fun x => okKey 0 x.1 && okKey 1 x.2
    start := first P.codes, chain := chainOf P, fin := fun _ _ => true }

/-- **The link's description.** Its own public test: `tiesOk`, and the public test on the prices of
the entry file's finished plan
(`entryOk`, Johnson/Desc/MadeOk.lean: every round holds at the target 128, work counted; the side
conditions; at most 32 bits of work a round). -/
def linkDesc (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound) : OneChainFileDescription
    (TableKey × TableKey) :=
  descOf (p15Of c) plan (VerifiableInference.Desc.entryOk c.made && tiesOk c plan)

end Desc.K15
