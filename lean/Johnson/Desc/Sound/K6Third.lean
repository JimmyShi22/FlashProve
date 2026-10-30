-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K6Third.lean: THE OUTPUT HEAD'S BLOCK'S THIRD AND FOURTH TIE TO THE TABLE OF
JOINTS, ITEM BY ITEM, AT THE FILLING OF THE SIX LETTERS ON THE ORACLES (`meaningSig`). A rule: the
pins, the stored table's pin and "no mark" are paid; what is left is one premise an item. NO RESULT
ON THE PROTOCOL.

What is said.
  `k6_row`: the table's row at piece 4 of the head's segment: what it closes, opens and reads.
  `K6Items`: what is left of the two ties: members, fence0 (ON THE PLAN) · opened (the four items
    that the row opens, with "small", give K6's files' relation behind) · idn, rider, keys (the
    three clauses of K6's files' relation in front give the items that the row closes) · planes
    (the fourth item that it closes: of which K6's files' relation in front says nothing) · small
    (rides back).
  `k6_t3_of_items`, `k6_t4_of_items`: the two ties in the form of `K6Left`
    (Johnson/Desc/Sound/K6AtSig.lean).

Limits. Every field of `K6Items` but the first two has the table's promise in front, no mark, the
yes and K6's files' condition behind in hand. That they can be met is not said. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.K6AtSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart)

/-- **The table's row at K6's place.** -/
theorem k6_row (links : List ModelPart) (a : Place) (m : ℕ) (hl : a.link = some m)
    (hs : links[m]? = some .head) (hpc : a.piece = 4) :
    (First.rowOf links a).ins = [.constr m .idn, .worth m 3 "planes", .worth m 3 "keys",
        .worth m 3 "rider"] ∧
      (First.rowOf links a).outs = [.formsT m 4 "own", .formsT m 3 "planes", .formsT m 4 "join",
        .formsT m 4 "weights"] ∧
      (First.rowOf links a).ctx = [.pin m 0, .pinW, .constr m .small] := by
  simp [First.rowOf, First.segRow, First.shift, First.joinAt, hl, hs, hpc]

/-- The row of block number k is the row of the place that stands at k. -/
theorem rowQ_of_place (links : List ModelPart) (ps : List Place) (k : ℕ) (a : Place)
    (h : ps[k]? = some a) : rowQ links ps k = First.rowOf links a := by
  unfold rowQ
  rw [h]
  rfl

end VerifiableInference.Desc.Sound

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT onQ meansQ insQ outsQ strsOf
  meaningSig k6_row rowQ_of_place)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (ms msT : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (N : Numbers) (Mg₀ : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List Place) (k m : ℕ)
  (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))

/-- The table's meaning with its six letters on the oracles filled. -/
local notation "MG" => meaningSig cs G arr smp msT decT Mg₀

/-- **WHAT IS LEFT OF K6's THIRD AND FOURTH TIE, ONE FIELD AN ITEM.** -/
structure K6Items : Prop where
  /-- ON THE PLAN: what the head reads are members of the table's list, at seats of the segment's
  first sending -/
  members : ∀ x ∈ ms, x ∈ msT ∧ x.1.seat x.2 ∈ N.sent m 0
  /-- ON THE PLAN: that sending's trees were sent in front of the piece -/
  fence0 : ∀ y ∈ N.sent m 0, y.1 < q.base
  /-- what the row opens, with "small", gives K6's files' relation behind -/
  opened : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    Mg₀.formsT m 4 "own" b.1 (strsOf Fr b.2) w → Mg₀.formsT m 3 "planes" b.1 (strsOf Fr b.2) w →
    Mg₀.formsT m 4 "join" b.1 (strsOf Fr b.2) w → Mg₀.formsT m 4 "weights" b.1 (strsOf Fr b.2) w →
    Mg₀.constr m .small b.1 (strsOf Fr b.2) w → K6Out Wp b.1.2 (compK6 cs arr rd6 w)
  /-- K6's files' relation in front gives three of the four items that the row closes -/
  idn : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → K6In Wp a.1.2 (compK6 cs arr rd6 w) →
    Mg₀.constr m .idn a.1 (strsOf Fr a.2) w
  rider : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → K6In Wp a.1.2 (compK6 cs arr rd6 w) →
    Mg₀.worth m 3 "rider" a.1 (strsOf Fr a.2) w
  keys : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → K6In Wp a.1.2 (compK6 cs arr rd6 w) →
    Mg₀.worth m 3 "keys" a.1 (strsOf Fr a.2) w
  /-- the fourth: with the opened item on the planes behind in hand -/
  planes : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → K6In Wp a.1.2 (compK6 cs arr rd6 w) →
    Mg₀.formsT m 3 "planes" b.1 (strsOf Fr b.2) w → Mg₀.worth m 3 "planes" a.1 (strsOf Fr a.2) w
  /-- "small" rides back -/
  small : ∀ a τ b w, q.ior.red.out a τ = some b → a.1.2.failed = none →
    Mg₀.constr m .small b.1 (strsOf Fr b.2) w → Mg₀.constr m .small a.1 (strsOf Fr a.2) w

variable {cs G arr smp decT ms msT rd6 Wp fld Fr N Mg₀ links ps k m q}

/-- **THE THIRD TIE.** -/
theorem k6_t3_of_items (I : K6Items cs G arr smp decT ms msT rd6 Wp fld Fr N Mg₀ links ps k m q)
    (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m) (hs : links[m]? = some .head)
    (hpc : p.piece = 4) (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (ha : onQ (Fr := Fr) N MG links ps (fun a => a) k a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (hA : K6After Wp b.1.2)
    (hw : relAt (meansQ (Fr := Fr) N MG fun a => a) (outsQ links ps k) b w) :
    relAt (meansK6 cs G arr (fun s => smp (b.1.1, s)) (fun c s => decT c (b.1.1, s)) ms rd6 Wp Fr)
      OutK6 (b.1.2, b.2) w := by
  obtain ⟨_, ro, rc⟩ := k6_row links p m hl hs hpc
  have mem : ∀ i, i ∈ (First.rowOf links p).outs ++ (First.rowOf links p).ctx ++ [.unmarked] →
      meansQ (Fr := Fr) N MG (fun a => a) i b w := fun i hi => hw i (by
    unfold outsQ
    rw [rowQ_of_place links ps k p hp]
    exact hi)
  rw [ro, rc] at mem
  intro j hj
  rcases hj with rfl | rfl
  · exact ⟨I.opened a τ b w ha hm hb hA (mem (.formsT m 4 "own") (by simp))
      (mem (.formsT m 3 "planes") (by simp)) (mem (.formsT m 4 "join") (by simp))
      (mem (.formsT m 4 "weights") (by simp)) (mem (.constr m .small) (by simp)),
      mem .unmarked (by simp)⟩
  · refine ⟨fun x hx => ?_, mem .pinW (by simp)⟩
    exact ((mem (.pin m 0) (by simp)) (x.1.seat x.2) (I.members x hx).2).2 x (I.members x hx).1 rfl

/-- **THE FOURTH TIE.** -/
theorem k6_t4_of_items {l : ℕ} {bef : List (ℕ × ℕ)} {B bS : Block S Claim}
    (H : Seated Wp fld Fr q l bef B bS) (hBl : Blind cs smp decT)
    (I : K6Items cs G arr smp decT ms msT rd6 Wp fld Fr N Mg₀ links ps k m q)
    (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m) (hs : links[m]? = some .head)
    (hpc : p.piece = 4) (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (ha : onQ (Fr := Fr) N MG links ps (fun a => a) k a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (hA : K6After Wp b.1.2)
    (hw : relAt (meansQ (Fr := Fr) N MG fun a => a) (outsQ links ps k) b w)
    (hin : relAt (meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms rd6
      Wp Fr) InK6 (a.1.2, a.2) w) :
    relAt (meansQ (Fr := Fr) N MG fun a => a) (insQ links ps k) a w := by
  obtain ⟨ri, ro, rc⟩ := k6_row links p m hl hs hpc
  have mem : ∀ i, i ∈ (First.rowOf links p).outs ++ (First.rowOf links p).ctx ++ [.unmarked] →
      meansQ (Fr := Fr) N MG (fun a => a) i b w := fun i hi => hw i (by
    unfold outsQ
    rw [rowQ_of_place links ps k p hp]
    exact hi)
  rw [ro, rc] at mem
  have hc := (hin .closed (Or.inl rfl)).1
  intro i hi
  unfold insQ at hi
  rw [rowQ_of_place links ps k p hp, ri, rc] at hi
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl
  · exact I.idn a τ b w ha hm hb hA hc
  · exact I.planes a τ b w ha hm hb hA hc (mem (.formsT m 3 "planes") (by simp))
  · exact I.keys a τ b w ha hm hb hA hc
  · exact I.rider a τ b w ha hm hb hA hc
  · intro y hy
    obtain ⟨h1, h2⟩ := (mem (.pin m 0) (by simp)) y hy
    refine ⟨h1, fun x hx hsx => ?_⟩
    have e : x.1.seat x.2 = (y.1, y.2) := hsx
    refine ((Sound.rides (Cells := Cells) (Tok := Tok) cs G arr smp q [x] ?_ ?_ a b τ hb x
      (List.mem_singleton.2 rfl)).1 w).1 (h2 x hx hsx)
    · intro x' hx'
      rw [List.mem_singleton.1 hx', e]
      exact I.fence0 y hy
    · intro a' τ' b' hb' x' _
      obtain ⟨o, F1, X, Q, _, _, _, e'⟩ := k6_behind H a' b' τ' hb'
      rw [e', hBl.smp]
  · exact (hin .pins (Or.inr rfl)).2
  · exact I.small a τ b w hb hm (mem (.constr m .small) (by simp))
  · exact hm

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Sound.k6_row
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t3_of_items
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t4_of_items
