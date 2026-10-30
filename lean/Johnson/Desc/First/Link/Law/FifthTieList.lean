-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieList.lean: THE FIFTH TIE AT THE THREE PIECES OF A LINK's END
(the
batching; the frame's sub-protocol behind it; the one equation) IN THE VERY FORM OF THE THREE FIELDS
t5b, t5q, t5e OF THE LINK's ONE LIST OF DEBTS (`LinkList`, LinkList.lean): three theorems, each
ending in the field's type to the letter, with every payer that lies laid in. A joining.

What is laid in. `t5_quiet` (FifthTie.lean) at the link's two own sub-protocols, `t5_eq`
(FifthTieEq.lean) at the one equation; `quiet9_batch`, `quiet9_behind`; the premise on every rider,
whole (`hO_quiet`, `hO_eq`, FifthTieLow.lean: the kernel's facts on the written table and one closed
test on the plan's numbers); `HeadOpen` (`headOpen_quiet9`, `headOpen_eq`, FifthTieHead.lean);
`CarryOpen`: IDLE at the two quiet pieces: by the kernel no "carry" rides there (`noCarry_full`).

What is said.
  `noCarryB`, `noCarry_full`, `carryOpen_idle`: at the 25 batchings and the 25 places behind them no
    rider is "carry m". `carry_rides_at_shut`: the test is FALSE at the shuttings (a test that
fails).
  `t5b_list`, `t5q_list`, `t5e_list`: **THE THREE FIELDS.**

WHAT IS LEFT, BY NAME, in each: the list is the written full one and k the number of segment m's
batching in it (three equations; m < 25); the piece holds its sub-protocol and its extractor lays
nothing (the list's own hpb | hpq | he, eb | eq | ee); at the two quiet pieces the runs' share hb₁
and
hst (the fields hb₁ and stand of `LinkShare`); `MeantAt 𝔇 seats r`; three premises on the letters of
𝔇.headPart; ONE CLOSED TEST a piece: `lowAtB 𝔇.N q.base k`; and, at the one equation alone, ON
STATES, INSIDE THE TABLE's CONDITION: `OwnNotIndex` (its payer: `ownNotIndex_reached`,
FifthTieLow.lean: from FoldFacts.frameIs, the promise's item indexIs and one closed test).
Limits. None of these is shown here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTieLow
import Johnson.Desc.First.Link.Law.FifthTieHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)
open VerifiableInference.Desc.JoinAtBlocks
open Johnson.Desc.First.Walk.Tied
open _root_.Run (ckP)

/-- A test with code on the written table: no rider at place k is "carry". -/
def noCarryAt (k : ℕ) : Bool :=
  (ridersAt k).all fun i => match i with
    | .carry _ => false
    | _ => true

/-- At the 25 batchings and the 25 places behind them. -/
def noCarryB : Bool := (List.range 25).all fun l => noCarryAt (batchIx l) && noCarryAt (batchIx l +
    1)

set_option maxRecDepth 1000000 in
theorem noCarry_full : noCarryB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A test that fails: at the first segment's shutting "carry" rides. -/
theorem carry_rides_at_shut : noCarryAt (batchIx 0 + 4) = false := by decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **`CarryOpen` is idle where no "carry" rides.** -/
theorem carryOpen_idle {k : ℕ} (hk : k ≤ plF.length) (h : noCarryAt k = true)
    (R : P × S → Strs → P × S → Strs → Prop) :
    CarryOpen 𝔇 (fun i => openAfter (insQ linksFull plF) (outsQ linksFull plF)
      (· ∈ First.start linksFull) k i ∧ ¬ insQ linksFull plF k i) R := by
  intro m hm
  have h1 := List.all_eq_true.1 h _ (rider_mem hk hm.1 hm.2)
  cases h1

end

theorem batch_mem {m : ℕ} (hm : m < 25) : batchIx m ∈ quietAt :=
  List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, by simp⟩

theorem behind_mem {m : ℕ} (hm : m < 25) : batchIx m + 1 ∈ quietAt :=
  List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, by simp⟩

theorem eq_mem {m : ℕ} (hm : m < 25) : batchIx m + 1 + 1 ∈ eqAt :=
  List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩

theorem noCarry_at {m : ℕ} (hm : m < 25) :
    noCarryAt (batchIx m) = true ∧ noCarryAt (batchIx m + 1) = true := by
  have h := List.all_eq_true.1 noCarry_full m (List.mem_range.2 hm)
  rwa [Bool.and_eq_true] at h

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Sound.Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

/-- **THE FIELD t5b.** -/
theorem t5b_list (hm : m < 25) (hlinks : links = linksFull) (hpl : pl = plF) (hk : k = batchIx m)
    (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hst : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hpb : pb.b = below L.batchB) (eb : ∀ a τ w, pb.ext a τ w = w)
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
    (hlow : lowAtB 𝔇.N pb.base k = true) :
    ∀ a τ b w i, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz (k) a →
      pb.ior.red.out a τ = some b →
      onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) ((k) + 1) b →
      relQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) ((k) + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) (k) i →
      ¬ insQ links pl (k) i →
      meansQ 𝔇.N (mgAll 𝔇 Mg₀) (fun s : S => (z, s)) i a (pb.ext a τ w) := by
  subst hlinks hpl hk
  exact t5_quiet 𝔇 Mg₀ 𝔇.N linksFull plF z Rz (batchIx m) L.batchB pb hpb eb
    (quiet9_batch L pp hb₁ hst) (fun _ _ => True) (fun _ _ => trivial) hM
    (carryOpen_idle 𝔇 (quietAt_le (batch_mem hm)) (noCarry_at hm).1 _)
    (headOpen_quiet9 𝔇 h𝔇 hreq htok _ _ (quiet9_batch L pp hb₁ hst) _ _)
    (hO_quiet (batch_mem hm) hlow)

/-- **THE FIELD t5q.** -/
theorem t5q_list (hm : m < 25) (hlinks : links = linksFull) (hpl : pl = plF) (hk : k = batchIx m)
    (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hst : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (pq : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hpq : pq.b = below L.behindB) (eq : ∀ a τ w, pq.ext a τ w = w)
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
    (hlow : lowAtB 𝔇.N pq.base (k + 1) = true) :
    ∀ a τ b w i, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz (k + 1) a →
      pq.ior.red.out a τ = some b →
      onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) ((k + 1) + 1) b →
      relQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) ((k + 1) + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) (k + 1) i →
      ¬ insQ links pl (k + 1) i →
      meansQ 𝔇.N (mgAll 𝔇 Mg₀) (fun s : S => (z, s)) i a (pq.ext a τ w) := by
  subst hlinks hpl hk
  exact t5_quiet 𝔇 Mg₀ 𝔇.N linksFull plF z Rz (batchIx m + 1) L.behindB pq hpq eq
    (quiet9_behind L pp hb₁ hst) (fun _ _ => True) (fun _ _ => trivial) hM
    (carryOpen_idle 𝔇 (quietAt_le (behind_mem hm)) (noCarry_at hm).2 _)
    (headOpen_quiet9 𝔇 h𝔇 hreq htok _ _ (quiet9_behind L pp hb₁ hst) _ _)
    (hO_quiet (behind_mem hm) hlow)

/-- **THE FIELD t5e.** -/
theorem t5e_list (hm : m < 25) (hlinks : links = linksFull) (hpl : pl = plF) (hk : k = batchIx m)
    (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (he : pe.b = below b₃) (ee : ∀ a τ w, pe.ext a τ w = w)
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
    (hlow : lowAtB 𝔇.N pe.base (k + 1 + 1) = true)
    (notIx : ∀ a, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz (k + 1 + 1) a →
      OwnNotIndex a.1) :
    ∀ a τ b w i, onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz (k + 1 + 1) a →
      pe.ior.red.out a τ = some b →
      onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) ((k + 1 + 1) + 1) b →
      relQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) ((k + 1 + 1) + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ First.start links) (k + 1 + 1) i →
      ¬ insQ links pl (k + 1 + 1) i →
      meansQ 𝔇.N (mgAll 𝔇 Mg₀) (fun s : S => (z, s)) i a (pe.ext a τ w) := by
  subst hlinks hpl hk
  exact t5_eq 𝔇 Mg₀ 𝔇.N linksFull plF z Rz (batchIx m + 1 + 1) pw b₃ hb₃ pe he ee
    (fun x _ => OwnNotIndex x.2) (fun a ha => notIx a ha) (fun _ _ _ h => h) hM
    (headOpen_eq 𝔇 h𝔇 hreq htok _ pw b₃ hb₃ _ _)
    (hO_eq (eq_mem hm) hlow)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.noCarry_full
#print axioms VerifiableInference.Desc.LinkJoin.carry_rides_at_shut
#print axioms VerifiableInference.Desc.LinkJoin.t5b_list
#print axioms VerifiableInference.Desc.LinkJoin.t5q_list
#print axioms VerifiableInference.Desc.LinkJoin.t5e_list
