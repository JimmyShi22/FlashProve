-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeySeatsAt.lean: THE SEATS OF A CHAIN BY THEIR NUMBERS: what is asked of a
chain's given pieces, seat by seat; and how a seat is filled whose block costs no error: in the
words of the description's own block.

The setting. `RowsGood` (Johnson/Desc/Sound/KeyRowsOfPieces.lean) asks along a list of pairs. Each
kind's files fill one seat at a time, and a piece that a maker has cut holds the description's block
with the test below the prime in front, lifted (`liftP P (below b)`).

What is said.
  `keyRowAt A rs i`: the row at border i of a chain: A in front of the first piece, then the rows
    rs.
  `SeatGood εs A ps rs i`: SEAT i IS FILLED: the piece number i is good between the rows at the
    borders i and i + 1, and its errors are shares of at most εs.
  `rowsGood_of_seats`: all seats filled give `RowsGood`. `lastRow_zip`: the last row is the row at
    the last border.
  `held_decide`: where `liftP P (below b)` returns, b returns at the chain's own record, and the
    first part stays.
  `JointRow.atP`, `relLaw_liftAll`: `RelLaw` of a lifted block from `RelLaw` of the block itself at
    each first part. `seat_of_relLaw`: A SEAT IS FILLED BY A PROVED TYPED BLOCK, the law being
    stated of the description's own block at the chain's own record. `seat_of_relLawAt`: the same at
    a piece as it is given: the maps may hang on its stretch.
  `QuietOwn b A B`: the tie on statements in the words of b itself. `quietTie_held`: it gives
    `QuietTie` of `liftP P (below b)`.
  `quietOwn_end`: A CHAIN'S END meets it between every row A and `A.passed`: the same row with "the
    record has passed the chain's own clauses" laid into its invariant.
  `JointRow.push A b`: THE ROW THAT SUCH A BLOCK LEAVES BEHIND A: the strongest that its text gives;
    `quietOwn_push`: b meets `QuietOwn` between A and it; `readsBelow_push`: it reads no tree that A
    does not read. It says nothing by itself: the debt moves to whoever stands behind.
  `block_at`: the piece at a place holds the block at that place. `seat_of_end`: THE LAST SEAT OF A
    CHAIN IS FILLED where the chain's last block hands the record on just where the chain's clauses
    hold.
  `seat_of_quiet`: a seat whose piece holds a block that meets `QuietOwn` is filled, if the piece's
    errors are shares of at most εs and the row behind reads no tree from the piece's place on.

Limits. Rules. No seat of any description is filled here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyPieceLaws
import Johnson.Desc.Sound.BelowLift
import Johnson.Desc.Sound.KeyRowsOfBorders

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.ChainEnd
open _root_.Run (ckP)
open _root_.Iop (Err)

section
variable {S Cl W : Type} {F : Frame}

/-- The row at border i: A in front of the first piece, then the rows rs. -/
def keyRowAt (A : JointRow S F) (rs : List (JointRow S F)) (i : ℕ) : JointRow S F :=
  ((A :: rs)[i]?).getD A

/-- **Seat i is filled.** -/
def SeatGood (εs : ℝ≥0∞) (A : JointRow S F) (ps : List (Piece (ckP .two) F S Cl W))
    (rs : List (JointRow S F)) (i : ℕ) : Prop :=
  ∀ p, ps[i]? = some p →
    (p.bk (keyRowAt A rs i).on (keyRowAt A rs (i + 1)).on (fun a _ => (keyRowAt A rs i).rel a)
      (fun a _ => (keyRowAt A rs (i + 1)).rel a)).Good ∧ Err.Below p.err εs

theorem keyRowAt_succ (A r : JointRow S F) (rs : List (JointRow S F)) (i : ℕ) (h : i ≤ rs.length) :
    keyRowAt A (r :: rs) (i + 1) = keyRowAt r rs i := by
  have hl : i < (r :: rs).length := Nat.lt_succ_of_le h
  show (((r :: rs)[i]?).getD A) = (((r :: rs)[i]?).getD r)
  rw [List.getElem?_eq_getElem hl]
  rfl

/-- **All seats filled give what the rule asks along the list.** -/
theorem rowsGood_of_seats (εs : ℝ≥0∞) : ∀ (A : JointRow S F)
    (ps : List (Piece (ckP .two) F S Cl W)) (rs : List (JointRow S F)), ps.length = rs.length →
    (∀ i, i < ps.length → SeatGood εs A ps rs i) → RowsGood εs A (ps.zip rs)
  | _, [], _, _, _ => trivial
  | _, _ :: _, [], h, _ => by cases h
  | A, p :: ps, r :: rs, h, g => by
    have hl : ps.length = rs.length := Nat.succ.inj h
    refine ⟨g 0 (Nat.succ_pos _) p rfl, rowsGood_of_seats εs r ps rs hl fun i hi q hq => ?_⟩
    have e := g (i + 1) (Nat.succ_lt_succ hi) q hq
    rw [keyRowAt_succ A r rs i (hl ▸ Nat.le_of_lt hi), keyRowAt_succ A r rs (i + 1) (hl ▸ hi)] at e
    exact e

theorem lastRow_zip : ∀ (A : JointRow S F) (ps : List (Piece (ckP .two) F S Cl W))
    (rs : List (JointRow S F)), ps.length = rs.length →
    lastRow A (ps.zip rs) = keyRowAt A rs ps.length
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => by cases h
  | A, _ :: ps, r :: rs, h => by
    have hl : ps.length = rs.length := Nat.succ.inj h
    show lastRow r (ps.zip rs) = keyRowAt A (r :: rs) (ps.length + 1)
    rw [lastRow_zip r ps rs hl, keyRowAt_succ A r rs ps.length (Nat.le_of_eq hl)]

end

section
variable {P S₀ Cl W : Type} {F : Frame}

/-- Where the held block returns, the description's own block returns at the chain's own record. -/
theorem held_decide (b : Block S₀ Cl) (t t' : P × S₀) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (liftP P (below b)).decide t rs gs = .ok t') :
    ∃ e, b.decide t.2 rs gs = .ok e ∧ t' = (t.1, e) := by
  have h' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide t.2 rs gs
      else .error "a word is not below the prime").map fun s => (t.1, s)) = .ok t' := h
  split at h'
  · cases hb : b.decide t.2 rs gs with
    | error e =>
      rw [hb] at h'
      cases h'
    | ok e =>
      rw [hb] at h'
      exact ⟨e, rfl, (Except.ok.inj h').symm⟩
  · cases h'

/-- A row at the pair of what was handed to the chain and the chain's own record, at a fixed first
part: a row at the chain's own record. -/
def JointRow.atP (A : JointRow (P × S₀) F) (p : P) : JointRow S₀ F :=
  ⟨A.J, fun a => A.rd ((p, a.1), a.2), fun a => A.inv ((p, a.1), a.2)⟩

/-- **`RelLaw` of a lifted block, from `RelLaw` of the block itself at each first part.** -/
theorem relLaw_liftAll (b : Block S₀ Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {JA JB : JK} (k : BK JA JB) (M : Maps ds k.R.red.shape)
    (rdA : (P × S₀) × F.E.Str → JA.X × JA.E.Str) (A B : JointRow (P × S₀) F)
    (h : ∀ p : P, RelLaw b base ds back k M (fun a => rdA ((p, a.1), a.2)) (A.atP p) (B.atP p)) :
    RelLaw (liftP P b) base ds back k M rdA A B where
  onIn := fun a ha => (h a.1.1).onIn (a.1.2, a.2) ha
  relIn := fun a w ha hw => (h a.1.1).relIn (a.1.2, a.2) w ha hw
  step := by
    rintro ⟨p, s⟩ t' y τ ha h1 hw h2 h3
    have h3' : (b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
        (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
          (sView (ckP .two) (stg F base ds) y τ).opened)).map (fun s' => (p, s')) = .ok t' := h3
    cases hd : b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
        (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
          (sView (ckP .two) (stg F base ds) y τ).opened) with
    | error e =>
      rw [hd] at h3'
      cases h3'
    | ok s' =>
      rw [hd] at h3'
      have e : (Except.ok (p, s') : Except String (P × S₀)) = .ok t' := h3'
      cases e
      exact (h p).step s s' y τ ha h1 hw h2 hd

/-- **A SEAT IS FILLED BY A PROVED TYPED BLOCK**: where the piece at place i holds the description's
block b (with the test below the prime, lifted), stands on the law's own stretch and has the written
counts along the law's maps as its errors, and b meets `RelLaw` at each first part. -/
theorem seat_of_relLaw (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F)) (i : ℕ)
    (b : Block S₀ Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) {JA JB : JK} (k : BK JA JB)
    (M : Maps ds k.R.red.shape) (rdA : (P × S₀) × F.E.Str → JA.X × JA.E.Str) (hk : k.Good)
    (hB : Nonempty JB.W) (hM : M.OK) (hback : viewWordsBelowPrime ⟨back, []⟩ = true)
    (hp : ∀ p, ps[i]? = some p → ∃ ext,
      p = ⟨liftP P (below b), base, ds, back, ext, M.err k.err⟩)
    (hε : Err.Below (M.err k.err) εs)
    (h : ∀ p : P, RelLaw b base ds back k M (fun a => rdA ((p, a.1), a.2))
      ((keyRowAt A rs i).atP p) ((keyRowAt A rs (i + 1)).atP p)) : SeatGood εs A ps rs i := by
  intro p hp'
  obtain ⟨ext, rfl⟩ := hp p hp'
  refine ⟨?_, hε⟩
  have e : liftP P (below b) = below (liftP P b) := (below_lift _ _ b).symm
  rw [e]
  exact goodOfRelAt _ k (fun _ => M.carry) rdA _ _ hk hB
    (relAt_of_relLaw (liftP P b) base ds back k M rdA _ _ ext hM hback
      (relLaw_liftAll b base ds back k M rdA _ _ h))

/-- The same at a piece as it is given: its own place, stretch and rounds put back; the maps may
hang on them. -/
theorem seat_of_relLawAt (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F)) (i : ℕ)
    (b : Block S₀ Cl) {JA JB : JK} (k : BK JA JB) (rdA : (P × S₀) × F.E.Str → JA.X × JA.E.Str)
    (hk : k.Good) (hB : Nonempty JB.W)
    (h : ∀ p, ps[i]? = some p → p.b = liftP P (below b) ∧ ∃ M : Maps p.ds k.R.red.shape,
      M.OK ∧ viewWordsBelowPrime ⟨p.back, []⟩ = true ∧ p.err = M.err k.err ∧ Err.Below p.err εs ∧
      ∀ q : P, RelLaw b p.base p.ds p.back k M (fun a => rdA ((q, a.1), a.2))
        ((keyRowAt A rs i).atP q) ((keyRowAt A rs (i + 1)).atP q)) : SeatGood εs A ps rs i := by
  intro p hp
  obtain ⟨hb, M, hM, hback, he, hε, hl⟩ := h p hp
  obtain ⟨pb, base, ds, back, ext, err⟩ := p
  dsimp only at hb M hM hback he hε hl
  subst hb he
  refine ⟨?_, hε⟩
  have e : liftP P (below b) = below (liftP P b) := (below_lift _ _ b).symm
  rw [e]
  exact goodOfRelAt _ k (fun _ => M.carry) rdA _ _ hk hB
    (relAt_of_relLaw (liftP P b) base ds back k M rdA _ _ ext hM hback
      (relLaw_liftAll b base ds back k M rdA _ _ hl))

/-- The tie on statements, in the words of the description's own block. -/
def QuietOwn (b : Block S₀ Cl) (A B : JointRow (P × S₀) F) : Prop :=
  ∀ (p : P) (s s' : S₀) (y : F.E.Str) rs gs, A.on ((p, s), y) → b.decide s rs gs = .ok s' →
    B.on ((p, s'), y) ∧ (B.rel ((p, s'), y) → A.rel ((p, s), y))

theorem quietTie_held (b : Block S₀ Cl) (A B : JointRow (P × S₀) F) (h : QuietOwn b A B) :
    QuietTie (liftP P (below b)) A B := by
  intro t t' y rs gs ha hd
  obtain ⟨e, he, rfl⟩ := held_decide b t t' rs gs hd
  exact h t.1 t.2 e y rs gs ha he

/-- **A chain's end**, between every row and the same row with the chain's own clauses passed. -/
theorem quietOwn_end (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S₀ → Clauses) (A : JointRow (P × S₀) F) :
    QuietOwn (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks) A
      (A.passed fun t => asks t.2) := by
  intro p s s' y rs gs ha hd
  obtain ⟨rfl, hc⟩ := (chainEnd_decide_iff chain piece sealed inFront asks s s' rs gs).1 hd
  exact ⟨⟨ha.1, ha.2, hc⟩, fun hr => hr⟩

/-- **A seat whose piece holds a block that costs no error is filled.** -/
theorem seat_of_quiet (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F)) (i : ℕ)
    (b : Block S₀ Cl) (hnd : (F.all.map (·.no)).Nodup)
    (hb : ∀ p, ps[i]? = some p → p.b = liftP P (below b) ∧ Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (i + 1)).on ∧ ReadsBelow p.base (keyRowAt A rs (i + 1)).rel)
    (h : QuietOwn b (keyRowAt A rs i) (keyRowAt A rs (i + 1))) : SeatGood εs A ps rs i := by
  intro p hp
  obtain ⟨e, hε, h1, h2⟩ := hb p hp
  exact ⟨goodOfQuietAt p _ _ hnd h1 h2 (e ▸ quietTie_held b _ _ h), hε⟩

/-- **The row that a block which costs no error leaves behind a row A**: the strongest that its text
gives. Its condition: the statement comes of a statement in A's condition by a yes of b. Its
relation: A's relation holds of every such statement. IT SAYS NOTHING BY ITSELF: what b does is read
out of it by whoever stands behind (`rowLe` against that seat's own row). -/
def JointRow.push (A : JointRow (P × S₀) F) (b : Block S₀ Cl) : JointRow (P × S₀) F :=
  JointRow.ofBorder (W := Unit)
    (fun a => ∃ s rs gs, A.on ((a.1.1, s), a.2) ∧ b.decide s rs gs = .ok a.1.2)
    (fun a _ => ∀ s rs gs, A.on ((a.1.1, s), a.2) → b.decide s rs gs = .ok a.1.2 →
      A.rel ((a.1.1, s), a.2))

theorem quietOwn_push (b : Block S₀ Cl) (A : JointRow (P × S₀) F) : QuietOwn b A (A.push b) :=
  fun _ s _ _ rs gs ha hd =>
    ⟨(ofBorder_on _ _ _).2 ⟨s, rs, gs, ha, hd⟩, fun hr => hr.elim fun _ h => h s rs gs ha hd⟩

/-- It reads no tree that A does not read. -/
theorem readsBelow_push (b : Block S₀ Cl) (A : JointRow (P × S₀) F) (c : ℕ)
    (hon : ReadsBelow c A.on) (hrel : ReadsBelow c A.rel) :
    ReadsBelow c (A.push b).on ∧ ReadsBelow c (A.push b).rel := by
  refine ⟨fun t y y' h1 h2 => ?_, fun t y y' h1 h2 => ?_⟩
  · show ((∃ s rs gs, A.on ((t.1, s), y) ∧ b.decide s rs gs = .ok t.2) ∧ True) =
      ((∃ s rs gs, A.on ((t.1, s), y') ∧ b.decide s rs gs = .ok t.2) ∧ True)
    simp only [hon _ y y' h1 h2]
  · show (∃ _ : Unit, ∀ s rs gs, A.on ((t.1, s), y) → b.decide s rs gs = .ok t.2 →
        A.rel ((t.1, s), y)) =
      (∃ _ : Unit, ∀ s rs gs, A.on ((t.1, s), y') → b.decide s rs gs = .ok t.2 →
        A.rel ((t.1, s), y'))
    simp only [hon _ y y' h1 h2, hrel _ y y' h1 h2]

/-- A block that hands the record on where the clauses hold, and refuses else. -/
theorem quietOwn_of_pass (e : Block S₀ Cl) (asks : S₀ → Clauses)
    (hdec : ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asks s, c.2 = true) ∧ s' = s)
    (A : JointRow (P × S₀) F) : QuietOwn e A (A.passed fun t => asks t.2) := by
  intro p s s' y rs gs ha hd
  obtain ⟨hc, rfl⟩ := hdec s rs gs s' hd
  exact ⟨⟨ha.1, ha.2, hc⟩, fun hr => hr⟩

/-- The piece at a place holds the block at that place. -/
theorem block_at (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (bs : List (Block S₀ Cl))
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s))) (i : ℕ)
    (p : Piece (ckP .two) F (P × S₀) Cl W) (b : Block S₀ Cl) (hp : ps[i]? = some p)
    (hb : bs[i]? = some b) : p.b = liftP P (below b) := by
  have h1 : (ps.map (·.b))[i]? = some p.b := by rw [List.getElem?_map, hp]; rfl
  have h2 : ((bs.map below).map (Block.lift Prod.snd fun (t : P × S₀) s => (t.1, s)))[i]? =
      some (liftP P (below b)) := by
    rw [List.getElem?_map, List.getElem?_map, hb]
    rfl
  rw [hbs, h2] at h1
  exact (Option.some.inj h1).symm

/-- **THE LAST SEAT OF A CHAIN IS FILLED** where the chain's last block hands the record on just
where the chain's own clauses hold: between the row in front of it and the same row with the clauses
passed. -/
theorem seat_of_end (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (p₀ : Piece (ckP .two) F (P × S₀) Cl W) (l : List (Piece (ckP .two) F (P × S₀) Cl W))
    (rs : List (JointRow (P × S₀) F)) (bs : List (Block S₀ Cl))
    (hbs : (p₀ :: l).map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (e : Block S₀ Cl) (he : bs.getLast? = some e) (asks : S₀ → Clauses)
    (hdec : ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asks s, c.2 = true) ∧ s' = s)
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel) :
    SeatGood εs A (p₀ :: l) rs l.length := by
  have hlen : bs.length = l.length + 1 := by
    have := congrArg List.length hbs
    simpa using this.symm
  have hb : bs[l.length]? = some e := by
    rw [List.getLast?_eq_getElem?, hlen] at he
    exact he
  refine seat_of_quiet εs A (p₀ :: l) rs l.length e hnd
    (fun p hp' => ⟨block_at _ bs hbs _ p e hp' hb, hp p hp'⟩) ?_
  rw [hrow]
  exact quietOwn_of_pass e asks hdec _

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.relLaw_liftAll
#print axioms VerifiableInference.Desc.Sound.seat_of_relLaw
#print axioms VerifiableInference.Desc.Sound.seat_of_relLawAt
#print axioms VerifiableInference.Desc.Sound.quietOwn_push
#print axioms VerifiableInference.Desc.Sound.readsBelow_push
#print axioms VerifiableInference.Desc.Sound.block_at
#print axioms VerifiableInference.Desc.Sound.seat_of_end
#print axioms VerifiableInference.Desc.Sound.rowsGood_of_seats
#print axioms VerifiableInference.Desc.Sound.lastRow_zip
#print axioms VerifiableInference.Desc.Sound.quietTie_held
#print axioms VerifiableInference.Desc.Sound.quietOwn_end
#print axioms VerifiableInference.Desc.Sound.seat_of_quiet
