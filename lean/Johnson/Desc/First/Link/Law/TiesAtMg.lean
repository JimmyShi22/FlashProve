-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/TiesAtMg.lean: THE FIVE DEBTS A PIECE (`TieRestR`, LinkTiedR.lean) OF A
LINK's THREE PIECES, ASSEMBLED AT THE COMPOSED MEANING (`mgAll 𝔇 Mg₀`) AND AT THE RELATIONS OF THE
LAW WITH THE TWO SENTENCES ON WORTHS (`relFW`, WorthTiedR.lean; `relTotB`, `relTotB'`, `relTot`,
`relRow`, LinkTied.lean), at the reader of the witness `rdC`, the context `ctxPins`, own := the
plan's group of the segment, the public sentence `rwAt 𝔇 m`. The assembly of TieThreeFour.lean and
TieMarkDec.lean. Theorems, each ending in a whole `TieRestR`.

What is said.
  `tq_of`: **the piece of the frame's sub-protocol behind the batching: `TieRestR` whole, the fifth
    tie a premise.** `tb_of`: **the batching's piece: the fourth and the fifth tie premises.**
    `te_of`: **the one equation's piece: the third and the fifth tie premises.**

Limits. BOOK-KEEPING. PREMISES THAT STAY, beside the ties named above (other files have the
fifth tie and the one equation's third, over files that this file does not stand on): what the
table's rows at the three places open, close and read (closed facts, not evaluated here); 𝔇.lk m is
the link; `InsideAt` at the part of each state at which a sentence is turned, asked
only inside `onTR`; `PinAsks`; the two sub-protocols' share `TwoBlocks`; «the committed table's
decoder answers alike at any two states». Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WorthTiedR
import Johnson.Desc.First.Link.Law.TieThreeFour
import Johnson.Desc.First.Link.Law.TieMarkDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf start)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz
/-- **THE PIECE BEHIND THE BATCHING: WHOLE, THE FIFTH TIE A PREMISE.** -/
theorem tq_of {C : CK} (α : Type) (L : Link S Claim) (pp : Where) (hL : 𝔇.lk m = some L)
    (T : TwoBlocks L pp) (hins : (rowQ links pl k).ins = [.totalB m])
    (houts : (rowQ links pl k).outs = [.total m]) (hctx : (rowQ links pl k).ctx = pinsOf m)
    (hinA : ∀ a, onK k a → ∀ s' x, L.runBehind a.1 = .ok s' → atS.get? s' = some x →
      InsideAt 𝔇.cs 𝔇.ms own x)
    (hinB : ∀ b, onK (k + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a)
    (pq : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpq : pq.b = below L.behindB)
    (hext : ∀ a τ w, pq.ext a τ w = w)
    (hpin : ∀ a τ b, onK k a → pq.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pq.base a.1 b.1)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (t5 : ∀ a τ b w i, onK k a → pq.ior.red.out a τ = some b →
      onQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b →
      relQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
      meansQ 𝔇.N Mg (fun s : S => (z, s)) i a (pq.ext a τ w)) :
    TieRestR 𝔇.N Mg links pl (fun s : S => (z, s)) Rz k pq (relTotB' α L own rdW (rwAt 𝔇 m))
      (relTot own rdW (rwAt 𝔇 m)) :=
  ⟨t3_behind 𝔇 Mg₀ links pl z Rz k m houts hinB pq,
    t4_behind 𝔇 Mg₀ links pl z Rz k m α L hL hins hctx hinA pq hext hpin, t5,
    mark_behind z L pp T pq hpq, dec_at Mg 𝔇.decT (mgAll_decodes 𝔇 Mg₀) z hd pq⟩

/-- **THE BATCHING's PIECE: THE FOURTH AND THE FIFTH TIE PREMISES.** -/
theorem tb_of {C : CK} (α : Type) (L : Link S Claim) (pp : Where) (hL : 𝔇.lk m = some L)
    (T : TwoBlocks L pp) (houts : (rowQ links pl k).outs = [.totalB m])
    (hctx : (rowQ links pl k).ctx = pinsOf m)
    (hin : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a →
      InsideAt 𝔇.cs 𝔇.ms own a)
    (pb : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpb : pb.b = below L.batchB)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (R0 : S × F.E.Str → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (t4 : ∀ a τ b w, onK k a → pb.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      R0 a (pb.ext a τ w) →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (insQ links pl k) a (pb.ext a τ w))
    (t5 : ∀ a τ b w i, onK k a → pb.ior.red.out a τ = some b →
      onQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b →
      relQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
      meansQ 𝔇.N Mg (fun s : S => (z, s)) i a (pb.ext a τ w)) :
    TieRestR 𝔇.N Mg links pl (fun s : S => (z, s)) Rz k pb R0
      (relTotB α L own rdW (rwAt 𝔇 m) (ctxPins 𝔇.N Mg z m)) :=
  ⟨t3_batch 𝔇 Mg₀ links pl z Rz k m α L hL houts hctx hin pb, t4, t5,
    mark_batch z L pp T pb hpb, dec_at Mg 𝔇.decT (mgAll_decodes 𝔇 Mg₀) z hd pb⟩

/-- **THE ONE EQUATION's PIECE: THE THIRD AND THE FIFTH TIE PREMISES.** -/
theorem te_of {C : CK} (N : ℕ) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (hins : (rowQ links pl k).ins = [.total m]) (hctx : (rowQ links pl k).ctx = [])
    (hin : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpe : pe.b = below b₃)
    (hext : ∀ a τ w, pe.ext a τ w = w)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (t3 : ∀ a τ b w, onK k a → pe.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relRow own N rdW b w)
    (t5 : ∀ a τ b w i, onK k a → pe.ior.red.out a τ = some b →
      onQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b →
      relQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
      meansQ 𝔇.N Mg (fun s : S => (z, s)) i a (pe.ext a τ w)) :
    TieRestR 𝔇.N Mg links pl (fun s : S => (z, s)) Rz k pe (relTot own rdW (rwAt 𝔇 m))
      (relRow own N rdW) :=
  ⟨t3, t4_eq 𝔇 Mg₀ links pl z Rz k m hins hctx hin pe hext, t5, mark_eq z pw b₃ hb₃ pe hpe,
    dec_at Mg 𝔇.decT (mgAll_decodes 𝔇 Mg₀) z hd pe⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tq_of
#print axioms VerifiableInference.Desc.LinkJoin.tb_of
#print axioms VerifiableInference.Desc.LinkJoin.te_of
