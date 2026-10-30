-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieShut.lean: THE FIFTH TIE AT THE PIECE "THE SEGMENT IS SHUT", IN
THE
VERY FORM OF THE FIELD t5 OF `ShutOwesR` (LinkTiedPubR.lean), at Nm := 𝔇.N and Mg := mgAll 𝔇 Mg₀:
one
theorem ending in the field's type to the letter, with every payer that lies laid in. The sister of
FifthTieList.lean. A joining.

What is laid in. `t5_quiet` (FifthTie.lean) at b₅ with `quiet9_shut`; the premise on every rider,
whole (`hO_quiet`, FifthTieLow.lean); `HeadOpen` (`headOpen_quiet9`, FifthTieHead.lean);
`CarryOpen`,
which is NOT idle here ("carry" rides at the shuttings: `carry_rides_at_shut`, FifthTieList.lean):
`carryOpen_shutZ` (FifthTieCarry.lean) with the fence at the state that the way in returns
(`fence_of_in_doorData`, Johnson/Top/H0/Walk/FrameCarryFenceEnds.lean).

What is said.
  `ShutFacts Z base s`: four facts on the state in front: the book is in order (at each switch's
    number of the first tree); every place of the book names a tree that it holds; the carried rows
    of the live copy's frame name messages that have a place; the book holds at most base trees.
  `notHead_putLink`, `notHead_shut`: the shutting's step leaves "the state does not stand at the
    head's link".
  `t5s_list`: **THE FIELD.**

WHAT IS LEFT, BY NAME: the list is the written full one and k the number of segment m's shutting in
it (k = batchIx m + 4; m < 25); `ShutOwesR`'s own hb₅, hps, hext; `MeantAt 𝔇 seats r`; three
premises
on the letters of 𝔇.headPart; 𝔇.cr1 = carryAtZ Z layF; the proof file's rounds have data and
ps.base ≤ D.t₁; ONE CLOSED TEST: `lowAtB 𝔇.N ps.base k`; ON STATES, INSIDE THE TABLE's CONDITION:
`ShutFacts` (three of its four are fields of FoldFacts: bookInOrder, bookFits, rowsSent; the fourth
is
the promise's bookAt against the piece's first tree) and: where a "carry m'" rides whose switch
stands at the head, the state in front does not stand at the head's link (the promise's shapeAt).
Limits. None of these is shown here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTieList
import Johnson.Desc.First.Link.Law.FifthTieCarry
import Johnson.Top.H0.Walk.FrameCarryFenceEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2 (par9)
open VerifiableInference.Desc.First.K2Caller (carryAtZ doorZ)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)
open Johnson.Desc.First.Walk.Tied
open _root_.Run.PQ (CK)

/-- Four facts on the state in front of the shutting. -/
structure ShutFacts (Z : ProofFile.Pub) (base : ℕ) (s : S) : Prop where
  ord : ∀ m', VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m')).firstTree s =
    true
  fit : VerifiableInference.Desc.K12.Door.atFirstFits s = true
  rows : ∀ o ∈ singleRowsOracles s.live.frame.rows, o < s.book.place.size
  size : s.book.trees.size ≤ base

theorem notHead_putLink {s : S} (L : LinkCtx) (h : ∀ a, s.here ≠ .head a) :
    ∀ a, (s.putLink L).here ≠ .head a := by
  intro a
  unfold S.putLink
  cases hh : s.here with
  | head x => exact absurd hh (h x)
  | lay x => simp
  | att x => simp
  | between => simp [hh]
  | fin x => simp [hh]
  | mem x => simp [hh]

theorem notHead_shut {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    {s t : S} (h : BlockYes b₅ s t) (hs : ∀ a, s.here ≠ .head a) : ∀ a, t.here ≠ .head a := by
  obtain ⟨ft, rs, cols, k, h⟩ := h
  obtain ⟨L, _, rfl⟩ := shut_inv pw piece ft s rs cols t k (hb₅ _ _ _ _ _ h)
  exact notHead_putLink _ hs

theorem shut_mem {m : ℕ} (hm : m < 25) : batchIx m + 4 ∈ quietAt :=
  List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, by simp⟩

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Sound.Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

/-- **THE FIELD t5 OF `ShutOwesR`.** -/
theorem t5s_list {C : CK} (hm : m < 25) (hlinks : links = linksFull) (hpl : pl = plF)
    (hk : k = batchIx m + 4) (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hps : ps.b = below b₅) (hext : ∀ a τ w, ps.ext a τ w = w)
    {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (hM : MeantAt 𝔇 seats r)
    {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {msR : List Mem} {Nh : Numbers}
    {sz : ℕ → Cb.Pv.Tail.Size} {seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {plh : ℕ → ℕ × Bool × ℕ × ℕ} {tab : ℕ → ℕ}
    {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
    {H : P5J.HidAt X P (Wit (CellsQ rows cols) Tok MsgT) rows cols}
    {tokH : P × S → Fin Inst.Model.ppref.V}
    (h𝔇 : 𝔇.headPart = headPartK6 cs arr msR Nh sz seat X plh tab put H tokH)
    (hreq : ∀ p s t, H.req (p, s) = H.req (p, t))
    (htok : ∀ p s t, t.out.reply = s.out.reply → tokH (p, s) = tokH (p, t))
    (Z : ProofFile.Pub) (layF : ByteArray) (hcr : 𝔇.cr1 = carryAtZ Z layF)
    (D : WholeD) (hW : ProofFile.wholeAt Z = some D) (hb : ps.base ≤ D.t₁)
    (hlow : lowAtB 𝔇.N ps.base k = true)
    (hS : ∀ a, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz k a →
      ShutFacts Z ps.base a.1)
    (hNH : ∀ m', openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) k (.carry m') →
      ¬ insQ links pl k (.carry m') → (ProofFile.pAtK2 Z m').stands = .head →
      ∀ a, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz k a →
        ∀ x, a.1.here ≠ .head x) :
    ∀ a τ b w i, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz k a →
      ps.ior.red.out a τ = some b →
      onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) (k + 1) b →
      relQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) (k + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) k i →
      ¬ insQ links pl k i →
      meansQ 𝔇.N (mgAll 𝔇 Mg₀) (fun s : S => (z, s)) i a (ps.ext a τ w) := by
  subst hlinks hpl hk
  let In : P × S → Strs → Prop := fun x _ => ShutFacts Z ps.base x.2 ∧
    ∀ m', openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ First.start linksFull)
        (batchIx m + 4) (.carry m') → ¬ insQ linksFull plF (batchIx m + 4) (.carry m') →
      (ProofFile.pAtK2 Z m').stands = .head → ∀ x', x.2.here ≠ .head x'
  exact t5_quiet 𝔇 Mg₀ 𝔇.N linksFull plF z Rz (batchIx m + 4) b₅ ps hps hext
    (quiet9_shut pw piece b₅ hb₅) In
    (fun a ha => ⟨hS a ha, fun m' h1 h2 h3 => hNH m' h1 h2 h3 a ha⟩) hM
    (carryOpen_shutZ 𝔇 Z layF hcr _ pw piece b₅ hb₅ ps.base In
      (fun m' hr hs _ s t _ hy hI =>
        ⟨hI.2 m' hr.1 hr.2 hs, notHead_shut pw piece b₅ hb₅ hy (hI.2 m' hr.1 hr.2 hs)⟩)
      (fun m' hr => fence_of_in_doorData Z D hW m' ps.base hb In
        (fun _ _ _ hI => ⟨hI.1.ord m', hI.1.fit, hI.1.rows, hI.1.size⟩)
        (fun hs _ _ _ hI => hI.2 m' hr.1 hr.2 hs)))
    (headOpen_quiet9 𝔇 h𝔇 hreq htok _ _ (quiet9_shut pw piece b₅ hb₅) _ _)
    (hO_quiet (shut_mem hm) hlow)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.notHead_shut
#print axioms VerifiableInference.Desc.LinkJoin.t5s_list
