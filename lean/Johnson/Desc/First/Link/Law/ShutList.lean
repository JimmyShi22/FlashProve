-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ShutList.lean: WHAT IS LEFT OF THE SHUTTING's TIE (`ShutOwesR`,
LinkTiedPubR.lean) AT THE COMPOSED MEANING OVER THE CLOSED BASE (`mgAll 𝔇 mgBase`), AS ONE NAMED
LIST: `ShutList`. Laid in: the hand-on of the promise over the shutting (`hands_mgR`,
RidesAtMgR.lean), the fifth tie (`t5s_list`, FifthTieShut.lean), the ride of «it
decodes» (`dec_at`, TieMarkDec.lean), the closed facts on the written list (K09More.lean; `linkFit`,
`pubFit9`). Two structures and one theorem.

What is said.
  `MeantHead 𝔇`: two sentences on the composed meaning's data alone, which the fifth tie takes at
    every piece of a link. `ShutList 𝔇 links pl z Rz k ps Zc layF Dw`: at the public part z, at the
    shutting's piece ps at border k: ten named fields. `shutOwesR_of_list`: **`ShutOwesR 𝔇.N (mgAll
    𝔇 mgBase) links pl Rz z k pw piece b₅ ps` from it**, where k is four behind the number of link
    m's batching, the written list is the full one, the three Bools on the list say yes, AND THE
    FACTS ON THE SEAT HOLD (premises of the theorem: a yes of b₅ is the shutting's; the piece holds
    b₅; its extractor lays nothing; «reached» is handed on over the piece; the committed table's
    decoder answers alike at any two states).

Limits. BOOK-KEEPING: THE LIST IS THE DEBT. NO FIELD IS A TIE ANY MORE. `MeantHead`'s two fields are
existentials over functions: they want witnesses, not a run. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RidesAtMgR
import Johnson.Desc.First.Link.Law.LinkTiedPubR
import Johnson.Desc.First.Link.Law.TieMarkDec
import Johnson.Desc.First.Link.Law.K09More
import Johnson.Desc.First.Link.Law.FifthTieShut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers)
open _root_.Run.PQ (CK)
open Johnson.Desc.First.Walk.Tied (MeantAt)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)
open VerifiableInference.Desc.First.K2Caller (carryAtZ)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (links : List ModelPart) (pl : List Place) (z : P)
  (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT
local notation "Mg" => mgAll 𝔇 mgBase
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz

/-- **TWO SENTENCES ON THE COMPOSED MEANING's DATA ALONE**, which the fifth tie takes at every piece
of a link: it is the meant one; its head's part is the head kind's, whose request's reader reads
the public part alone and whose token's reader the heard reply alone. -/
structure MeantHead : Prop where
  meant : ∃ seats r, MeantAt 𝔇 seats r
  headIs : ∃ (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (Nh : Numbers)
    (sz : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (plh : ℕ → ℕ × Bool × ℕ × ℕ) (tab : ℕ → ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols)
    (tokH : P × S → Fin Inst.Model.ppref.V),
    𝔇.headPart = headPartK6 cs arr msR Nh sz seat X plh tab put H tokH ∧
      (∀ p s t, H.req (p, s) = H.req (p, t)) ∧
      ∀ p s t, t.out.reply = s.out.reply → tokH (p, s) = tokH (p, t)

/-- **WHAT IS LEFT OF THE SHUTTING's TIE, AT THE PUBLIC PART z.** Zc layF Dw: the public data, the
layout's bytes and the whole data at which the carried item's sentence is read. -/
structure ShutList (ps : Piece C F S Claim WT) (Zc : ProofFile.Pub) (layF : ByteArray) (Dw : WholeD) :
    Prop where
  /-- the plan's numbers of trees and of messages stand still over the place -/
  treesS : 𝔇.N.treesAt pl[k + 1]? = 𝔇.N.treesAt pl[k]?
  msgsS : 𝔇.N.msgsAt pl[k + 1]? = 𝔇.N.msgsAt pl[k]?
  /-- what the four riders on the oracles take, inside onTR -/
  oraS : ∀ a τ b, onK k a → ps.ior.red.out a τ = some b →
    OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k ps.base a.1 b.1
  /-- WHAT THE FIFTH TIE TAKES: the two sentences on the meaning's data; its carried item's sentence
  is the one at Zc; the whole data is Zc's, and the piece's first tree lies below its own -/
  mh : MeantHead 𝔇
  hcr : 𝔇.cr1 = carryAtZ Zc layF
  hW : ProofFile.wholeAt Zc = some Dw
  hbase : ps.base ≤ Dw.t₁
  /-- a test with code: the riders lie low -/
  lowS : lowAtB 𝔇.N ps.base k = true
  /-- on states, inside onTR: four facts on the book and the live frame; where a carried item rides
  whose switch stands at the head, the state does not stand at the head's link -/
  hS : ∀ a, onK k a → ShutFacts Zc ps.base a.1
  hNH : ∀ m', openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) k (.carry m') →
    ¬ insQ links pl k (.carry m') → (ProofFile.pAtK2 Zc m').stands = .head →
    ∀ a, onK k a → ∀ x, a.1.here ≠ .head x

/-- **THE SHUTTING's TIE FROM THE LIST.** -/
theorem shutOwesR_of_list (m : ℕ) (hm : m < 25) (hlinks : links = linksFull) (hpl : pl = plF)
    (hkx : k = batchIx m + 4) (hk : k = batchAt links pl m + 4)
    (hlf : linkFit links pl = true) (hp9 : pubFit9 true moreAll links pl = true)
    (hmf : moreFit links pl = true) (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim WT) (hps : ps.b = below b₅) (hext : ∀ a τ w, ps.ext a τ w = w)
    (hand : HandsOn Rz k ps) (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (Zc : ProofFile.Pub) (layF : ByteArray) (Dw : WholeD)
    (H : ShutList 𝔇 links pl z Rz k ps Zc layF Dw) :
    ShutOwesR 𝔇.N Mg links pl Rz z k pw piece b₅ ps := by
  have hm' : m < links.length := by rw [hlinks]; exact hm
  obtain ⟨⟨p, p', hp, hp', hl, hpc⟩, hins, hctx⟩ := more_shut links pl hmf m hm'
  obtain ⟨seats, r, hM⟩ := H.mh.meant
  obtain ⟨cs, arr, msR, Nh, sz, seat, plh, tab, put, Hh, tokH, h𝔇, hreq, htok⟩ := H.mh.headIs
  rw [← hk] at hp hp' hins hctx
  exact ⟨hb₅, hps, hext, hins, hctx,
    hands_mgR 𝔇 𝔇.N links pl z Rz k m p p' hlf hp9 hp hp' hl hpc H.treesS H.msgsS pw piece b₅ hb₅
      ps hps hand H.oraS,
    t5s_list 𝔇 mgBase links pl z Rz k m hm hlinks hpl hkx pw piece b₅ hb₅ ps hps hext hM h𝔇 hreq
      htok Zc layF H.hcr Dw H.hW H.hbase H.lowS H.hS H.hNH,
    dec_at Mg 𝔇.decT (mgAll_decodes 𝔇 mgBase) z hd ps⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shutOwesR_of_list
