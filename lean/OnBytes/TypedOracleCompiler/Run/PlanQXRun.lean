-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQXRun.lean: the description of a chain that opens stored tables, its interface
with the type of leaves' bodies as a parameter, and how typed oracle queries are spelled as the
format's hash calls, over the sibling.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After the library's Run/PlanQXRun.lean (XD, XD.atR, ds, xs, a, C, K, ok, L, PDX, firstX, leafX,
famX) and OnBytes/Tie/FamPd.lean (firstXPd, famXPd: a value pd in the place of the format's digest
of the parameter bytes).

AS TEXT. `XD` (said whole, so that `D.ds` is the sibling's list of rounds' data, with a list of
trees a round), `XD.atR`, `XD.ds`, `XD.xs`, `XD.a`, `XD.C`, `XD.K`, `XD.ok`, `firstXPd`, `famXPd`.
TURNED.
 `XD.L Bd D dec`    the type Bd of bodies is a parameter (`LkX Bd ..`).
 `PDX B D dec`      a message is spelled from a LIST of roots; a body's spelling is the datum
                    `B.own`, where the library spells a typed symbol by `leafSL`.
 `leafX B D dec`    which bodies are stored symbols is read by `B.getE`, where the library matches
                    on the body's constructor.
 `firstX`, `famX`   abbreviations: `firstXPd` and `famXPd` at the format's own digest.
NEW.
 `BodyD Bd`         what is asked of the type of bodies, as data: `embE : SgX → Bd` with its reading
                    back `getE` and both laws; `own`, the spelling of a body of the chain's own
                    trees.

WHAT IS NOT SAID. The verifier `VX`, `vx_eq`, `headEntry`, `readHead`, `runEntry` of the library's
file: they want the wire with its embeddings of bodies. An embedding of the chain's own typed
symbols into Bd is no datum here: the page does not need it; the wire will. `XD.K` is the library's
function of the description, whose own rounds' data have one tree a round: that it is the right
number of blocks for a round with several roots is not examined. No instance of `BodyD`. Nothing on
soundness; no probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import Run.PlanQXRun
import OnBytes.TypedOracleCompiler.Run.PlanQX
import OnBytes.TypedOracleCompiler.Run.PlanQSpell
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
import OnBytes.TypedOracleCompiler.Run.CodingFn

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

/-- The description. The library's, said whole: its rounds' data are the sibling's. -/
structure XD where
  /-- the description of the proof's rounds; its field "statement" is not read -/
  base   : _root_.Fmt.Spec
  /-- the statement, as a function of the two roots -/
  stm    : ByteArray → ByteArray → ByteArray
  /-- the stored tables that each round opens -/
  stored : List (List _root_.Fmt.Stored)

namespace XD

/-- The description that the reader takes, at the two roots. -/
def atR (D : XD) (r0 r1 : ByteArray) : _root_.Fmt.SpecX :=
  ⟨{ D.base with statement := D.stm r0 r1 }, D.stored⟩
/-- The rounds' data: the sibling's, with a list of trees a round. -/
abbrev ds (D : XD) : List RD := rds D.base
/-- The openings of stored tables. -/
def xs (D : XD) : List XO :=
  D.stored.zipIdx.flatMap fun t => t.1.map fun s => ⟨t.2, s.item == 1, s.lo, s.count⟩
/-- The stored trees' depth. -/
def a (D : XD) : Nat := (D.stored.flatten.head?.map (·.sh.a)).getD 0
/-- The field's data. -/
abbrev C (D : XD) : CK := ckP D.base.plan.field
/-- The number of blocks of a challenge: the library's function of the description. -/
abbrev K (D : XD) : Nat := kOf D.base

/-- The limits. -/
def ok (D : XD) : Bool :=
  PQ.ok D.base && okX D.ds D.a D.xs &&
    D.stored.flatten.all fun s => s.sh.a == D.a && s.salt == D.base.plan.salt && decide (s.item ≤ 1)

/-- The interface. TWO: the type Bd of leaves' bodies is a parameter. -/
abbrev L (Bd : Type) (D : XD) (dec : View → Bool) : BatchProtocolWithLeafBody Unit Unit :=
  LkX (I := Unit) (RI := Unit) Bd D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some
  ())

end XD

/-- TWO: what is asked of the type of bodies, as data: how a stored table's symbol lies among
the bodies, with a reading back and both laws; and how a body that is no stored symbol is spelled
(the tree's place, the index, the bytes before the salt), or none. -/
structure BodyD (Bd : Type) where
  /-- a stored table's symbol (position, column), as a body -/
  embE  : SgX → Bd
  /-- which bodies are stored symbols -/
  getE  : Bd → Option SgX
  /-- a stored symbol is read back -/
  get_e : ∀ y, getE (embE y) = some y
  /-- only stored symbols are read -/
  e_get : ∀ b y, getE b = some y → b = embE y
  /-- the spelling of a body of the chain's own trees -/
  own   : Bd → Option (Nat × Nat × ByteArray)

variable {Bd : Type} (B : BodyD Bd)

/-- The spellings of the rounds behind the first query. TWO: a list of roots a query; a body's
spelling is `B.own`. -/
def PDX (D : XD) (dec : View → Bool) : PageD (D.L Bd dec) .link where
  label := D.base.label
  kind := fun i => if i = 0 then 7 else ((D.base.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((D.base.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => ByteArray.empty
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL D.C rt D.ds q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL D.C D.ds q
  leaf := B.own
  cfg := D.base.cfg

/-- The first query: the two digests in its head are the roots. With pd in the place of the
format's digest of the parameter bytes. -/
def firstXPd (D : XD) (dec : View → Bool) (pd : ByteArray) (K : Nat)
    (q : FbIn 256 (D.L Bd dec) .link) (j : Fin (K + 1)) : Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, D.base.label, _root_.Fmt.zero32,
            firstBytes pd (D.stm (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (PDX B D dec) K q j

/-- A leaf: of a stored tree, or of the chain's own. TWO: which it is, `B.getE` says. -/
def leafX (D : XD) (dec : View → Bool) (q : LeafIn (D.L Bd dec)) : Option _root_.Fmt.OQ :=
  match B.getE q.body with
  | some s =>
      if bitsToBytes (q.salt.take 256) == D.base.cfg then
        some ⟨0, 174, _root_.Fmt.leafPlace 0 s.2.length ((q.salt.length - 256) / 64), 2 ^ D.a + s.1,
          D.base.cfg, _root_.Fmt.leafBytes s.2 (bitsToBytes (q.salt.drop 256))⟩
      else none
  | none => leafCall (PDX B D dec) q

/-- The typed oracle functions that a function on the format's strings induces, with pd in the
place of the format's digest of the parameter bytes. -/
def famXPd (D : XD) (dec : View → Bool) (pd : ByteArray) (O : ByteArray → ByteArray) (K : Nat) :
    Fam (typedOracleFamily 256 K (D.L Bd dec))
  | .leaf, q => ansOf O (leafX B D dec q)
  | .node, q => ansOf O (nodeCallC D.base.cfg q)
  | .fb .link, q =>
      (fun k => ansOf O (firstXPd B D dec pd K q k.castSucc),
        ansOf O (firstXPd B D dec pd K q (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- The library's `firstX`: at the format's own digest of the parameter bytes. -/
abbrev firstX (D : XD) (dec : View → Bool) (K : Nat) (q : FbIn 256 (D.L Bd dec) .link)
    (j : Fin (K + 1)) : Option _root_.Fmt.OQ :=
  firstXPd B D dec (_root_.Fmt.paramsDigest D.base.params) K q j

/-- The library's `famX`: at the format's own digest of the parameter bytes. -/
abbrev famX (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (K : Nat) :
    Fam (typedOracleFamily 256 K (D.L Bd dec)) :=
  famXPd B D dec (_root_.Fmt.paramsDigest D.base.params) O K

end TypedOracleCompiler.Run.PQ
