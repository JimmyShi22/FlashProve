-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ShutRest.lean: BENEATH THE NAMED LIST OF WHAT IS LEFT AT A LINK's
SHUTTING's PIECE (`ShutList`, ShutList.lean): THE SAME LIST LESS THE SIX
FIELDS THAT HAVE A PAYER: oraS (`oraS_of`, OraPaid.lean), hS and hNH (`hS_paid`,
`hNH_paid`, ShutListPaid.lean), lowS, treesS and msgsS (premises of the theorem: paid at the closed
constant). A structure and one theorem.

What is said.
  `ShutRest 𝔇 ps Zc layF Dw`: four fields of `ShutList`'s, to the letter: mh, hcr, hW, hbase: NONE
    SPEAKS OF A STATE OR OF THE PUBLIC PART z. `shutList_of_rest`: **`ShutList` from it**, where k
    is four behind the number of link m's batching in the full written list, AND: the fence's test
    on the plan says yes; a yes of b₅ is the shutting's; the piece holds b₅; its first tree is the
    plan's number of trees at the place; the two readers answer alike; Zc is made by the road's own
    maker of the public data; the switch that spends «carry 24» does not stand at the head; the
    riders lie low; the plan's two counts stand still over the place; THE FACTS ALONG THE FOLD HOLD
    AT THE LIST's OWN «REACHED» (FF), with first tree 0.

Limits. BOOK-KEEPING. `ShutRest` AND THE THEOREM's PREMISE FF ARE THE DEBT. FF is a structure of
another file (Johnson/Desc/First/FoldFacts.lean), kind-free, whose fields are shown in
Johnson/P5J/FoldJ3Whole.lean (P5J.foldFacts_at_head') at the letters fun a => a.1 · At.foldD Zp cF L
· At.reqW · At.links · At.ps, under h : P5J.AtMg at secondHashFunction, hR, hl, hs and hB; NO MEMBER is shown
there; that FF's own letters (Rz · fun a => (z, a.1) · fd · reqW · links
· pl) are these is not shown here. The count of fields is no measure. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OraPaid
import Johnson.Desc.First.Link.Law.ShutListPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers fenceFit FoldFacts FoldData)
open VerifiableInference.Desc.First.K2Caller (carryAtZ)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (links : List ModelPart) (pl : List Place) (z : P)
  (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT
local notation "Mg" => mgAll 𝔇 mgBase

/-- **THE SHUTTING's LIST, LESS WHAT HAS A PAYER.** -/
structure ShutRest (ps : Piece C F S Claim WT) (Zc : ProofFile.Pub) (layF : ByteArray) (Dw : WholeD) :
    Prop where
  /-- four fields of the list, to the letter -/
  mh : MeantHead 𝔇
  hcr : 𝔇.cr1 = carryAtZ Zc layF
  hW : ProofFile.wholeAt Zc = some Dw
  hbase : ps.base ≤ Dw.t₁

/-- **THE LIST FROM THE REST.** -/
theorem shutList_of_rest (m : ℕ) (hm : m < 25) (hlinks : links = linksFull) (hpl : pl = plF)
    (hkx : k = batchIx m + 4) (hfen : fenceFit 𝔇.N links pl = true) (hkl : k ≤ pl.length)
    (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim WT) (hps : ps.b = below b₅) (hbq : ps.base = 𝔇.N.treesAt pl[k]?)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s)) (Zc : ProofFile.Pub)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Zc)
    (h24 : (ProofFile.pAtK2 Zc 24).stands ≠ .head) (T : lowAtB 𝔇.N ps.base k = true)
    (treesS : 𝔇.N.treesAt pl[k + 1]? = 𝔇.N.treesAt pl[k]?)
    (msgsS : 𝔇.N.msgsAt pl[k + 1]? = 𝔇.N.msgsAt pl[k]?)
    (layF : ByteArray) (Dw : WholeD) (fd : FoldData) (reqW : P → Array UInt32)
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) fd reqW links pl) (hft : fd.ft = 0)
    (H : ShutRest 𝔇 ps Zc layF Dw) :
    ShutList 𝔇 links pl z Rz k ps Zc layF Dw :=
  ⟨treesS, msgsS,
    oraS_of 𝔇 links pl z Rz k hfen hkl pw piece b₅ hb₅ ps hps (Nat.le_of_eq hbq.symm) hd hs,
    H.mh, H.hcr, H.hW, H.hbase, T,
    hS_paid 𝔇.N Mg links pl z Rz k FF hft hZ ps.base hbq FF.rowsSent,
    hNH_paid 𝔇.N Mg links pl z Rz k m hm hlinks hpl hkx Zc h24⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shutList_of_rest
