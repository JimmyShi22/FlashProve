-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeMg.lean: the honest side of the kind "lookup"
(K3): FROM THE INNER ITEMS OF THE LIBRARY'S ROW OUT TO THE FIELD worth OF THE TABLE OF JOINTS, at
every filling of the table that says at the lookups' own pieces what the lookups' layer says
(`K3At`, Johnson/Desc/First/Look/K3At.lean); and how the three sentences on a filling pass from one
reading and one family of key vectors to another. Theorems with proofs; no definition.

  `bAt_cell_or_zero`   at a proof file's lookup the place of a bit is a cell or the place "zero"
  `FillsAt.turn`       the three sentences pass to a reading with the same cells and the same value
                       at "zero", and to key vectors whose joint vector is the same at every index
                       below 2 ^ s.shape.v
  `worthK3_attention`, `worthK3_layers`   the field's term at the calls' piece of a segment. TWO
                       TEXTS: the library has the like: `worthK3_att`, `worthK3_lay`
                       (Johnson/Desc/First/Look/K3CallsAt.lean)
  `mg_digits`          at the digits' piece of a segment: worth "planes" and worth "keys"
  `mg_attention`       at the calls' piece of an attention segment: "planes", "keys", "rider"
  `mg_layers`          at the calls' piece of a layers' segment: "planes", "keys", "rider"

The last three are on the library's side alone: each is CONDITIONAL ON `K3At`, on what the public
data hold at the segment, and on the inner items at the table's own reading and key vectors. These
are asked as the library's own arm of the field (`worthDig`, `worthAtt`, `worthLay`,
Johnson/Desc/First/Look/K3FillWorth.lean) at the item's name, with False where the arm has no such
name.

Limits. The lookup on the head's calls is not reached HERE: its arm stands in another layer
(Johnson/Desc/First/Look/K3HeadFill.lean): Honest/K3/Law/Thread/ExchangeHead.lean. The theorem on
the digits speaks of every link at which the public data hold the place, the head's among them.
No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeFillAt
import Johnson.Desc.First.Look.K3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.Look (Sent digAt attAt layAt pubAt sort_calls)

local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 From one reading to another -/

/-- At a proof file's lookup the place of a bit is a cell or the place "zero". -/
theorem bAt_cell_or_zero (h : Shape) (lm jLK : Nat) (θ : GE) (u j : Nat) :
    (∃ r c, (_root_.Fo.numsF h lm jLK θ).bAt u j = .cell r c) ∨
      (_root_.Fo.numsF h lm jLK θ).bAt u j = .zero := by
  show (∃ r c, (match FoNums.cellOf h u j with
    | some x => _root_.Fo.Pl.cell (FoNums.cellRC h lm x).1 (FoNums.cellRC h lm x).2
    | none => _root_.Fo.Pl.zero) = .cell r c) ∨
    (match FoNums.cellOf h u j with
    | some x => _root_.Fo.Pl.cell (FoNums.cellRC h lm x).1 (FoNums.cellRC h lm x).2
    | none => _root_.Fo.Pl.zero) = .zero
  cases FoNums.cellOf h u j with
  | none => exact Or.inr rfl
  | some x => exact Or.inl ⟨_, _, rfl⟩

/-- **The three sentences on a filling pass to a reading with the same cells and the same value at
"zero", and to key vectors whose joint vector is the same at every index below 2 ^ s.shape.v.** -/
theorem FillsAt.turn {s : Site} {a : Ask} {L : LookIn} {kv : Nat → Nat → GE}
    {ν : _root_.Fo.Pl → GE} {theta : GE} {heard : List Fmt.Drawn}
    (h : FillsAt s a L kv ν theta heard) (kv' : Nat → Nat → GE) (ν' : _root_.Fo.Pl → GE)
    (hk : ∀ x, x < 2 ^ s.shape.v → OnBytes.Ends.jointKey s.shape kv' theta x =
      OnBytes.Ends.jointKey s.shape kv theta x)
    (hc : ∀ r c, ν' (.cell r c) = ν (.cell r c)) (hz : ν' .zero = ν .zero) :
    FillsAt s a L kv' ν' theta heard :=
  ⟨h.reads, fun x hx => (h.keys x hx).trans (hk x hx).symm, fun u j hu hj => by
    rw [h.bits u j hu hj]
    rcases bAt_cell_or_zero s.shape s.p.lm s.p.first theta u j with ⟨r, c, e⟩ | e
    · rw [e, hc]
    · rw [e, hz]⟩

/-! ## 2 From the inner items to the field worth -/

section
variable {P Cells Tok : Type} {X : OnBytes.Model.Verify.Public} {D : Sent}
  {Lk : K3Letters Cells Tok} {Mg : Meaning P (Wit Cells Tok MsgT)}

/-- **CONDITIONAL ON `K3At` and on the inner items at the table's own reading and key vectors: at
the digits' piece of a segment.** No instance of these hypotheses is exhibited in this file. -/
theorem mg_digits (hK : K3At X D Lk Mg) (m : Nat) {x : VerifiableInference.Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X m = some (x, tl)) (a : P × FS) (y : Strs)
    (w : Wit Cells Tok MsgT) (h1 : worthDig D Lk x tl "planes" a.2 w False)
    (h2 : worthDig D Lk x tl "keys" a.2 w False) :
    Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m true) "planes" a y w ∧
      Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m true) "keys" a y w := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_digits X D Lk f m hx, worthK3_digits X D Lk f m hx]
  unfold worthDig at h1 h2 ⊢
  rw [if_pos rfl] at h1 ⊢
  rw [if_neg (by decide), if_pos rfl] at h2 ⊢
  exact ⟨h1, h2⟩

/-- The field's term at the calls' piece of an attention segment. -/
theorem worthK3_attention
    (f : Nat → Nat → String → P × FS → Strs → Wit Cells Tok MsgT → Prop) (m : Nat)
    {x : VerifiableInference.Desc.First.Look.Place} {A : OnBytes.Attention.Shape}
    {tl : HTailF2} (hx : attAt X m = some (x, A, tl)) (r : String) (a : P × FS) (y : Strs)
    (w : Wit Cells Tok MsgT) :
    worthK3 X D Lk f m (VerifiableInference.Desc.K3.pieceAt X m false) r a y w =
      worthAtt D Lk x A tl r a.2 w
        (f m (VerifiableInference.Desc.K3.pieceAt X m false) r a y w) := by
  unfold worthK3
  rw [sort_calls, hx]

/-- The field's term at the calls' piece of a layers' segment. -/
theorem worthK3_layers
    (f : Nat → Nat → String → P × FS → Strs → Wit Cells Tok MsgT → Prop) (m : Nat)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} (hna : attAt X m = none)
    (hx : layAt X m = some x) (ht : VerifiableInference.Desc.First.Look.tlAt X m = some tl)
    (r : String) (a : P × FS) (y : Strs)
    (w : Wit Cells Tok MsgT) :
    worthK3 X D Lk f m (VerifiableInference.Desc.K3.pieceAt X m false) r a y w =
      worthLay D Lk x (pubAt X (m / stepAt X)) tl r a.2 w
        (f m (VerifiableInference.Desc.K3.pieceAt X m false) r a y w) := by
  unfold worthK3
  rw [sort_calls, hna, hx, ht]

/-- **CONDITIONAL ON `K3At` and on the inner items at the table's own reading, key vectors and
riders: at the calls' piece of an attention segment.** No instance of these hypotheses is exhibited
in this file. -/
theorem mg_attention (hK : K3At X D Lk Mg) (m : Nat)
    {x : VerifiableInference.Desc.First.Look.Place} {A : OnBytes.Attention.Shape}
    {tl : HTailF2} (hx : attAt X m = some (x, A, tl)) (a : P × FS) (y : Strs)
    (w : Wit Cells Tok MsgT) (h1 : worthAtt D Lk x A tl "planes" a.2 w False)
    (h2 : worthAtt D Lk x A tl "keys" a.2 w False)
    (h3 : worthAtt D Lk x A tl "rider" a.2 w False) :
    Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m false) "planes" a y w ∧
      Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m false) "keys" a y w ∧
      Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m false) "rider" a y w := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_attention f m hx, worthK3_attention f m hx, worthK3_attention f m hx]
  unfold worthAtt at h1 h2 h3 ⊢
  rw [if_pos rfl] at h1 ⊢
  rw [if_neg (by decide), if_pos rfl] at h2 ⊢
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h3 ⊢
  exact ⟨h1, h2, h3⟩

/-- **CONDITIONAL ON `K3At` and on the inner items at the table's own reading, key vectors and
riders: at the calls' piece of a layers' segment.** No instance of these hypotheses is exhibited in
this file. -/
theorem mg_layers (hK : K3At X D Lk Mg) (m : Nat)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} (hna : attAt X m = none)
    (hx : layAt X m = some x) (ht : VerifiableInference.Desc.First.Look.tlAt X m = some tl)
    (a : P × FS) (y : Strs)
    (w : Wit Cells Tok MsgT)
    (h1 : worthLay D Lk x (pubAt X (m / stepAt X)) tl "planes" a.2 w False)
    (h2 : worthLay D Lk x (pubAt X (m / stepAt X)) tl "keys" a.2 w False)
    (h3 : worthLay D Lk x (pubAt X (m / stepAt X)) tl "rider" a.2 w False) :
    Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m false) "planes" a y w ∧
      Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m false) "keys" a y w ∧
      Mg.worth m (VerifiableInference.Desc.K3.pieceAt X m false) "rider" a y w := by
  obtain ⟨f, hf⟩ := hK.worth
  rw [hf, worthK3_layers f m hna hx ht, worthK3_layers f m hna hx ht,
    worthK3_layers f m hna hx ht]
  unfold worthLay at h1 h2 h3 ⊢
  rw [if_pos rfl] at h1 ⊢
  rw [if_neg (by decide), if_pos rfl] at h2 ⊢
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h3 ⊢
  exact ⟨h1, h2, h3⟩

end

#print axioms ProofFile.Honest.K3.Law.Exchange.bAt_cell_or_zero
#print axioms ProofFile.Honest.K3.Law.Exchange.FillsAt.turn
#print axioms ProofFile.Honest.K3.Law.Exchange.mg_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.worthK3_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.worthK3_layers
#print axioms ProofFile.Honest.K3.Law.Exchange.mg_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.mg_layers

end ProofFile.Honest.K3.Law.Exchange
