-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6ItemsCut.lean (at the law with its two sentences on the
witness under the guard "the witness's cells hold an index" (Law/K6CutGuarded.lean): opened is asked
under it; the four items that the row closes are asked from the kind's relation in front UNDER it,
idn with the committed table's pin in hand; general in a condition Rch
that stands beside
the table's promise, a premise of six fields
): THE SUB-PROTOCOL AT THE OUTPUT HEAD'S THIRD AND FOURTH TIE TO THE TABLE
OF JOINTS, ITEM BY ITEM, AT THE LAW WITHOUT A LETTER FOR WHAT IS READ (Law/K6TiedCut.lean:
meansCut), at the filling of the table's six letters on the oracles (meaningSig). A rule: the pins,
the committed table's pin and "no mark" are paid; what is left is one premise an item. ON THE
PATTERN,
AND WITH THE PROOFS, OF Johnson/Desc/Sound/K6Third.lean (K6Items, k6_t3_of_items,
k6_t4_of_items), which stands at the older law.

WHAT PARTS FROM THAT FILE. The components are compCut's. The reader's list and the table's are ONE
list msR: so that file's premise "members" is a theorem here (members_ms0: by ms0's make). The
segment's number is 24. ONE FIELD MORE: base: the law's item "pins" also says that segment 24's
committed symbols are the packing of small integers (base24): it is asked of the table's item
"constr 24 small" behind the sub-protocol.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  members_ms0: a member of ms0 msR N is a member of msR at a seat of N.sent 24 0.
  K6ItemsCut: what is left of the two ties: fence0 (on the plan) · opened (the four items that the
      row opens, with "small", give K6Out at compCut) · base · idn, rider, keys (K6In at compCut
      gives three of the four items that the row closes) · planes (the fourth, with the opened item
      on the planes in hand) · small (rides back).
  k6_t3_cut_of_items, k6_t4_cut_of_items: the two ties in the form of Law/K6TiedAtObject.lean's
      bill.

Every letter under "there is": none.
What it does not say. THAT ANY FIELD CAN BE MET. Every field but the first and the last has the
table's promise in front, no mark, the accept and K6's condition behind in hand: at a filling
where these can never hold together the fields are free. opened: K6's law from the items'
sentences to K6Out is typed at a letter for the cells; Law/CellsOfData.lean fills
it under one premise on symbols. idn, rider, keys, planes: no payer is typed. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.K6CutGuarded
import Johnson.Desc.Sound.K6Third

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT onQ meansQ insQ outsQ strsOf
  meaningSig k6_row rowQ_of_place seatOf)

/-- A member of the pinned list is a member of the reader's list at a seat of the first sending. -/
theorem members_ms0 (msR : List Mem) (N : Numbers) (x : Mem) (hx : x ∈ ms0 msR N) :
    x ∈ msR ∧ x.1.seat x.2 ∈ N.sent 24 0 :=
  ⟨(List.mem_filter.1 hx).1, of_decide_eq_true (List.mem_filter.1 hx).2⟩

section
variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (msR : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (Wp : OnBytes.Model.Verify.Public)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (fld : Fmt.Fld) (Fr : Frame)
  (Mg₀ : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart)
  (ps : List Place) (k : ℕ)
  (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))
  (Rch : ℕ → (P × S) × Fr.E.Str → Prop)

/-- The table's meaning with its six letters on the oracles filled, at the one list. -/
local notation "MG" => meaningSig cs G arr smp msR decT Mg₀

/-- **WHAT IS LEFT OF THE THIRD AND THE FOURTH TIE, ONE FIELD AN ITEM.** -/
structure K6ItemsCut : Prop where
  /-- ON THE PLAN: the first sending's trees were sent in front of the piece -/
  fence0 : ∀ y ∈ N.sent 24 0, y.1 < q.base
  /-- what the row opens, with "small", gives the kind's relation behind -/
  opened : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → Rch k a → a.1.2.failed = none
      →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → VerifiableInference.OnPublicFiles.Flat.InRange w.cells
        →
    Mg₀.formsT 24 4 "own" b.1 (strsOf Fr b.2) w → Mg₀.formsT 24 3 "planes" b.1 (strsOf Fr b.2) w →
    Mg₀.formsT 24 4 "join" b.1 (strsOf Fr b.2) w →
    Mg₀.formsT 24 4 "weights" b.1 (strsOf Fr b.2) w →
    Mg₀.constr 24 .small b.1 (strsOf Fr b.2) w → K6Out Wp b.1.2 (compCut cs arr msR N s seat Wp pl
        w)
  /-- "small" behind says that the committed symbols are the packing of small integers -/
  base : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → 
    Mg₀.constr 24 .small b.1 (strsOf Fr b.2) w → base24 cs arr msR N s seat w
  /-- the kind's relation in front gives three of the four items that the row closes -/
  idn : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 → Sound.pinWOf decT a.1 (strsOf Fr a.2) w →
    (VerifiableInference.OnPublicFiles.Flat.InRange w.cells → K6In Wp a.1.2 (compCut cs arr msR N s seat
              Wp pl w)) →
    Mg₀.constr 24 .idn a.1 (strsOf Fr a.2) w
  rider : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    (VerifiableInference.OnPublicFiles.Flat.InRange w.cells → K6In Wp a.1.2 (compCut cs arr msR N s seat
              Wp pl w)) →
    Mg₀.worth 24 3 "rider" a.1 (strsOf Fr a.2) w
  keys : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    (VerifiableInference.OnPublicFiles.Flat.InRange w.cells → K6In Wp a.1.2 (compCut cs arr msR N s seat
              Wp pl w)) →
    Mg₀.worth 24 3 "keys" a.1 (strsOf Fr a.2) w
  /-- the fourth: with the opened item on the planes behind in hand -/
  planes : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → Rch k a → a.1.2.failed = none
      →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    (VerifiableInference.OnPublicFiles.Flat.InRange w.cells → K6In Wp a.1.2 (compCut cs arr msR N s seat
              Wp pl w)) →
    Mg₀.formsT 24 3 "planes" b.1 (strsOf Fr b.2) w →
    Mg₀.worth 24 3 "planes" a.1 (strsOf Fr a.2) w
  /-- "small" rides back -/
  small : ∀ a τ b w, q.ior.red.out a τ = some b → a.1.2.failed = none →
    Mg₀.constr 24 .small b.1 (strsOf Fr b.2) w → Mg₀.constr 24 .small a.1 (strsOf Fr a.2) w

variable {cs G arr smp decT msR N s seat Wp pl fld Fr Mg₀ links ps k q Rch}

/-- **THE THIRD TIE.** -/
theorem k6_t3_cut_of_items
    (I : K6ItemsCut cs G arr smp decT msR N s seat Wp pl fld Fr Mg₀ links ps k q Rch)
    (p : Place) (hp : ps[k]? = some p) (hl : p.link = some 24) (hs : links[24]? = some .head)
    (hpc : p.piece = 4) (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (ha : onQ (Fr := Fr) N MG links ps (fun a => a) k a) (hrc : Rch k a)
    (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (hA : K6After Wp b.1.2)
    (hw : relAt (meansQ (Fr := Fr) N MG fun a => a) (outsQ links ps k) b w) :
    relAt (meansCutG cs G arr smp decT msR N s seat Wp pl Fr b.1.1) OutK6 (b.1.2, b.2) w := by
  obtain ⟨_, ro, rc⟩ := k6_row links p 24 hl hs hpc
  have mem : ∀ i, i ∈ (First.rowOf links p).outs ++ (First.rowOf links p).ctx ++ [.unmarked] →
      meansQ (Fr := Fr) N MG (fun a => a) i b w := fun i hi => hw i (by
    unfold outsQ
    rw [rowQ_of_place links ps k p hp]
    exact hi)
  rw [ro, rc] at mem
  intro j hj
  rcases hj with rfl | rfl
  · intro hR
    exact ⟨I.opened a τ b w ha hrc hm hb hA hR (mem (.formsT 24 4 "own") (by simp))
      (mem (.formsT 24 3 "planes") (by simp)) (mem (.formsT 24 4 "join") (by simp))
      (mem (.formsT 24 4 "weights") (by simp)) (mem (.constr 24 .small) (by simp)),
      mem .unmarked (by simp)⟩
  · refine ⟨fun x hx => ?_, mem .pinW (by simp),
      I.base a τ b w ha hrc hm hb hA (mem (.constr 24 .small) (by simp))⟩
    exact ((mem (.pin 24 0) (by simp)) (x.1.seat x.2) (members_ms0 msR N x hx).2).2 x
      (members_ms0 msR N x hx).1 rfl

/-- **THE FOURTH TIE.** -/
theorem k6_t4_cut_of_items {l : ℕ} {bef : List (ℕ × ℕ)} {B bS : Block S Claim}
    (H : Seated Wp fld Fr q l bef B bS) (hBl : Blind cs smp decT)
    (I : K6ItemsCut cs G arr smp decT msR N s seat Wp pl fld Fr Mg₀ links ps k q Rch)
    (p : Place) (hp : ps[k]? = some p) (hl : p.link = some 24) (hs : links[24]? = some .head)
    (hpc : p.piece = 4) (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (ha : onQ (Fr := Fr) N MG links ps (fun a => a) k a) (hrc : Rch k a)
    (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (hA : K6After Wp b.1.2)
    (hw : relAt (meansQ (Fr := Fr) N MG fun a => a) (outsQ links ps k) b w)
    (hin : relAt (meansCutG cs G arr smp decT msR N s seat Wp pl Fr a.1.1) InK6 (a.1.2, a.2) w) :
    relAt (meansQ (Fr := Fr) N MG fun a => a) (insQ links ps k) a w := by
  obtain ⟨ri, ro, rc⟩ := k6_row links p 24 hl hs hpc
  have mem : ∀ i, i ∈ (First.rowOf links p).outs ++ (First.rowOf links p).ctx ++ [.unmarked] →
      meansQ (Fr := Fr) N MG (fun a => a) i b w := fun i hi => hw i (by
    unfold outsQ
    rw [rowQ_of_place links ps k p hp]
    exact hi)
  rw [ro, rc] at mem
  have hc : VerifiableInference.OnPublicFiles.Flat.InRange w.cells →
      K6In Wp a.1.2 (compCut cs arr msR N s seat Wp pl w) := fun hR =>
    (hin .closed (Or.inl rfl) hR).1
  have hpin : Sound.pinWOf decT a.1 (strsOf Fr a.2) w := (hin .pins (Or.inr rfl)).2.1
  intro i hi
  unfold insQ at hi
  rw [rowQ_of_place links ps k p hp, ri, rc] at hi
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ((rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl
  · exact I.idn a τ b w ha hrc hm hb hA hpin hc
  · exact I.planes a τ b w ha hrc hm hb hA hc (mem (.formsT 24 3 "planes") (by simp))
  · exact I.keys a τ b w ha hrc hm hb hA hc
  · exact I.rider a τ b w ha hrc hm hb hA hc
  · intro y hy
    obtain ⟨h1, h2⟩ := (mem (.pin 24 0) (by simp)) y hy
    refine ⟨h1, fun x hx hsx => ?_⟩
    have e : x.1.seat x.2 = (y.1, y.2) := hsx
    refine ((Sound.rides (Cells := Fin rows → Fin cols → GE) (Tok := Tok) cs G arr smp q [x] ?_ ?_
      a b τ hb x (List.mem_singleton.2 rfl)).1 w).1 (h2 x hx hsx)
    · intro x' hx'
      rw [List.mem_singleton.1 hx', e]
      exact I.fence0 y hy
    · intro a' τ' b' hb' x' _
      obtain ⟨o, F1, X, Q, _, _, _, e'⟩ := k6_behind H a' b' τ' hb'
      rw [e', hBl.smp]
  · exact (hin .pins (Or.inr rfl)).2.1
  · exact I.small a τ b w hb hm (mem (.constr 24 .small) (by simp))
  · exact hm

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.members_ms0
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t3_cut_of_items
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t4_cut_of_items
