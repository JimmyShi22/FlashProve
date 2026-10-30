-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Border62At.lean: BORDER 62, K6's SIDE: ONE BILL:
all five ties of the output head's block, cut by the rules of K6Tied · K6Second ·
K6AtSig · K6Third · K6Fifth.lean, are joined: what is left of `Tied61` at the object is ONE
structure of named premises, `K6Due`; and the facts that read the table alone are paid at the two
closed lists of segments by the kernel's evaluation. A joining of rules over letters. NO RESULT ON
THE PROTOCOL.

What is said.
  `K6Due`: fourteen fields: ON THE PLAN AND ITS NUMBERS: plan fenced fence logs numbers · ON THE
    FILLINGS: blind reads pubSays order · THE PUBLIC ITEMS BEHIND: pubBehind pubSentences · THE
    BITS: bits · THE ITEMS, ONE SENTENCE AN ITEM: items (`K6Items`: the third and fourth tie) ·
    riders (`K6Riders`: the fifth).
  **`tied61_of_due`**: the object (`Object61`), the meaning's six letters on the oracles filled
    (`SigFields`), the tests on the table and `K6Due` give `Tied61`.
  `tied61_small`, `tied61_full`: at blocks 61 and 341 of the two closed lists: of the tests on the
    table ONE is left: hfit: `pubFit` at the meaning's own filling of the door (it reads that
    filling).
  `Border62Small`, `Border62Full`: the border's statement at the two lists.

Limits. `K6Due`'s fence, pubBehind, pubSentences, items and riders still speak in the table's terms;
THAT THE FOURTEEN CAN BE MET TOGETHER IS SHOWN BY NOTHING: at the filling of the forms that lies the
items the row opens are false of every witness right behind the block (by reading):
then `items.opened` is owed for nothing and the block behind cannot be tied. `items` and `riders`
are typed at `meaningSig … Mg`, which IS Mg under `SigFields` (`SigFields.eq`). Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.K6Fifth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item start flatPlacesOf)

theorem head_small : linksSmall[4]? = some .head := by decide

set_option maxRecDepth 1000000 in
theorem head_full : linksFull[24]? = some .head := by decide

theorem mark_small : Item.unmarked ∈ start linksSmall := by decide

set_option maxRecDepth 1000000 in
theorem mark_full : Item.unmarked ∈ start linksFull := by decide +kernel

set_option maxRecDepth 1000000 in
theorem len_small : 61 ≤ (flatPlacesOf linksSmall true).length := by decide +kernel

set_option maxRecDepth 1000000 in
theorem len_full : 341 ≤ (flatPlacesOf linksFull true).length := by decide +kernel

end VerifiableInference.Desc.Sound

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning pubFit pubOfItems sampledIn start
  readsOpen)
open VerifiableInference.Desc.Sound (Piece Frame Sending Mem MsgT onQ openQ pubQ insL Fenced
  ErrBears kitK kitFs SigFields rowsApart ridersK6 linksSmall linksFull head_small head_full
  mark_small mark_full len_small len_full place62_small place342_full reads_small apart_small
  riders61_small reads_full apart_full riders341_full)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms msT : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (tokOf : P × S → Tok) (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
  (H : First.Blocks S Claim) (links : List ModelPart) (k m : ℕ)

set_option quotPrecheck false in
/-- The driver's list of places. -/
local notation "PS" => First.flatPlacesOf links true

/-- **THE BILL: ALL THAT IS LEFT OF K6's SIDE OF THE BORDER, BESIDE THE OBJECT AND THE TABLE's
TESTS.** -/
structure K6Due (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop where
  /-- two tests on the plan -/
  plan : planB Wp = true
  /-- the trees of what the head reads were sent in front of the piece -/
  fenced : Fenced q.base ms
  /-- so were the trees of every pin that is open in front of it -/
  fence : ∀ x ∈ sampledIn N (openQ links PS k), x.1 < q.base
  logs : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64
  /-- the plan's numbers: the block sends no tree and no message -/
  numbers : N.treesAt PS[k + 1]? = N.treesAt PS[k]? ∧ N.msgsAt PS[k + 1]? = N.msgsAt PS[k]?
  /-- the samples' reader and the decoder do not read where the chain stands -/
  blind : Blind cs smp decT
  /-- K6's reader reads pinned places alone -/
  reads : ReadsPinned cs ms rd6
  /-- three public items give three of K6's tests -/
  pubSays : PubSays Wp Mg m
  /-- "in order" does not read where the chain stands -/
  order : ∀ (z : P) (s : S) h, Mg.inOrder (z, { s with here := h }) = Mg.inOrder (z, s)
  /-- every public item that is open behind holds there, as a Bool -/
  pubBehind : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    ∀ x ∈ pubQ Mg.more links PS (k + 1) ++ pubOfItems (openQ links PS (k + 1)), Mg.pub x b.1 = true
  /-- and as a sentence -/
  pubSentences : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    ∀ x ∈ pubQ Mg.more links PS (k + 1), Mg.pubP x b.1
  /-- the piece's errors bear the law's prices -/
  bits : ErrBears (_root_.Run.ckP fld)
    (fun j => kitK (toRDs q.ds) j *
      (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err
  /-- the third and the fourth tie, one sentence an item -/
  items : K6Items cs G arr smp decT ms msT rd6 Wp fld Fr N Mg links PS k m q
  /-- the fifth tie, one sentence a rider -/
  riders : K6Riders cs G arr smp decT msT fld Fr N Mg links PS k m q

/-- **`Tied61` FROM THE OBJECT, THE TABLE's TESTS AND THE BILL.** hfit hs hp' hr hap hu hk hRid: ON
THE TABLE. -/
theorem tied61_of_due (bef : List (ℕ × ℕ)) (n : String) (bS B : Block S Claim)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))
    (hO : Object61 Wp fld Fr H links k m bef n bS B q)
    (hfit : pubFit Mg.more links PS = true) (hs : links[m]? = some .head)
    (hp' : PS[k + 1]? = some { chain := 1, link := some m, piece := 5, kind := .K1 })
    (hr : readsOpen links PS (start links) = true) (hap : rowsApart links PS = true)
    (hu : Item.unmarked ∈ start links) (hk : k ≤ (PS).length)
    (hRid : ∀ i ∈ openQ links PS k, i ∈ insL links PS k ∨ i ∈ ridersK6 m)
    (hSig : SigFields cs G arr smp msT decT Mg)
    (D : K6Due cs G arr smp decT ms msT rd6 Wp fld Fr N Mg links k m q) :
    Tied61 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg links k q := by
  have Hs := seated_of_object Wp fld Fr H links k m bef n bS B q hO
  have t3 := k6_t3_of_items D.items _ hO.2.1.place rfl hs rfl
  have t4 := k6_t4_of_items Hs D.blind D.items _ hO.2.1.place rfl hs rfl
  have t5 := k6_t5_of_riders Hs D.blind D.riders hr hap hu hk hRid
  rw [hSig.eq] at t3 t4 t5
  exact tied61_at_sig cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg H links k m bef n bS B q
    hO hfit hs hp' hSig
    ⟨D.plan, D.fenced, D.fence, D.logs, D.blind, D.reads, D.pubSays, D.order, D.pubBehind,
      D.pubSentences, D.numbers, D.bits, t3, t4, t5⟩

end

variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms msT : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (tokOf : P × S → Tok) (N : Numbers) (H : First.Blocks S Claim)

/-- **THE BORDER AT THE SMALL CHAIN**: blocks 61 and 62; the head's segment has the number 4. -/
def Border62Small (Mg : Meaning P (Wit Cells Tok MsgT)) (bef : List (ℕ × ℕ)) (n : String)
    (bS B₆ b1 B₁ : Block S Claim) (sealed : (P × S) × Fr.E.Str → Prop)
    (q₆ q₁ : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  Border62 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg H linksSmall 61 4 bef n bS B₆ b1 B₁
    sealed q₆ q₁

/-- **THE BORDER AT THE FULL CHAIN**: blocks 341 and 342; the head's segment has the number 24. -/
def Border62Full (Mg : Meaning P (Wit Cells Tok MsgT)) (bef : List (ℕ × ℕ)) (n : String)
    (bS B₆ b1 B₁ : Block S Claim) (sealed : (P × S) × Fr.E.Str → Prop)
    (q₆ q₁ : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop :=
  Border62 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg H linksFull 341 24 bef n bS B₆ b1 B₁
    sealed q₆ q₁

/-- **K6's SIDE AT BLOCK 61 OF THE SMALL CHAIN.** -/
theorem tied61_small (Mg : Meaning P (Wit Cells Tok MsgT)) (bef : List (ℕ × ℕ)) (n : String)
    (bS B : Block S Claim) (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))
    (hO : Object61 Wp fld Fr H linksSmall 61 4 bef n bS B q)
    (hfit : pubFit Mg.more linksSmall (First.flatPlacesOf linksSmall true) = true)
    (hSig : SigFields cs G arr smp msT decT Mg)
    (D : K6Due cs G arr smp decT ms msT rd6 Wp fld Fr N Mg linksSmall 61 4 q) :
    Tied61 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg linksSmall 61 q :=
  tied61_of_due cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg H linksSmall 61 4 bef n bS B q
    hO hfit head_small place62_small reads_small apart_small mark_small len_small riders61_small
    hSig D

/-- **K6's SIDE AT BLOCK 341 OF THE FULL CHAIN.** -/
theorem tied61_full (Mg : Meaning P (Wit Cells Tok MsgT)) (bef : List (ℕ × ℕ)) (n : String)
    (bS B : Block S Claim) (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))
    (hO : Object61 Wp fld Fr H linksFull 341 24 bef n bS B q)
    (hfit : pubFit Mg.more linksFull (First.flatPlacesOf linksFull true) = true)
    (hSig : SigFields cs G arr smp msT decT Mg)
    (D : K6Due cs G arr smp decT ms msT rd6 Wp fld Fr N Mg linksFull 341 24 q) :
    Tied61 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg linksFull 341 q :=
  tied61_of_due cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg H linksFull 341 24 bef n bS B q
    hO hfit head_full place342_full reads_full apart_full mark_full len_full riders341_full hSig D

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Sound.len_full
#print axioms VerifiableInference.Desc.Sound.mark_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.tied61_of_due
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.tied61_small
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.tied61_full
