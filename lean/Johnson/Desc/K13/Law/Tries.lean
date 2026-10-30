-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Tries.lean: the premises of `atM3_goodIn` (Johnson/Desc/K13/Law/Good.lean),
met: by the entries that the block itself declares, and by every pin that is a decoder of what was
sent in front of the stretch. And tries of the law's form at the piece. Statements with their
proofs.
Main names:
  `sends_of_entry`: a written round with an entry that draws one element, no position and no matrix
    entry, of a kind that is neither a sealing nor one of seeds, is as the library's maps ask.
  `Declared P dZ d0 ds`: the stretch's written rounds bear the entries that the block declares.
  `pinOf rw dec`: the witness's read part is what a decoder dec makes of the oracles.
  `Local base dec`: dec reads the stored table and the trees sent in front of the stretch alone.
  `atM3_goodIn_dec`: **the law with these two in the premises' place.**
  `pin_true`: with the pin that holds of everything the premise `hdet` says that the reader is
    constant: so it is `hdet` that keeps the law from speaking of a free witness.
  `pieceNo`, `goodIn_no`: a piece whose block refuses all meets the form, at any two relations.
  `yesB`, `pieceYes`, `not_goodIn_yes`: a piece whose block has no round, says yes to all and lays a
    row that is true of everything does not meet the form at `RowsHold`.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/Good.lean names.

What is not claimed. That the kinds in front lay rows that are true of what a decoder decodes. The
block that says yes to all is tried at the piece without a round, and
with the batching's rounds at the text's law (`not_sound_yes_gl`, Johnson/Desc/K13/Law/Pin.lean).
With these rounds at the piece the try would want that each written error is below the number of
written challenges that pass the tests in front of the run, and the format's laws on what is shown
of a written round: not done. What rules out the block that refuses all is the second half of the
text's law (`batt_answers`, Johnson/Desc/K13/Law/Silly.lean) and the run on an honest file. At a
reader that takes all mask entries from one world the premise on the pin cannot be met by a real run
(it fixes a value at every mask entry of every message, and messages are sent behind these draws):
there the law is true and idle. The law to carry on is that of Johnson/Desc/K13/Law/Good2.lean.
`Declared` is a test on a plan's written rounds: an evaluation at two stored sets' public files, a
small and a full-size one, said yes, and five controls said no; no theorem says it of a plan.
`Local` asks only that the decoder reads the stored table and the earlier trees: every such function
meets it. A decoder that reads the oracles alone singles out one member of a list whatever the
samples in the record say: so the laws at such a decoder are idle for the witness that the samples
pin. The form to carry on is that of Johnson/Desc/K13/Law/PinA.lean.

-/
import Johnson.Desc.K13.Law.Pin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- A written round whose entry draws one element and nothing else is as the maps ask. -/
theorem sends_of_entry {d : RDT} (h1 : d.entry.drawE = 1) (hp : d.entry.poss = 0)
    (ht : d.entry.trits = 0) (hz : d.entry.drawNZ ≤ 1) (hl : d.entry.logN ≤ 64)
    (hk : d.kind ≠ .sealed) (hs : d.kind ≠ .seeds) : ∃ n a, SendsDraws (toRD d) n 1 0 a := by
  have h := sendsDraws_of (d := toRD d)
    (r := { entry := d.entry, kind := d.kind, items := d.items }) ⟨rfl, rfl, rfl⟩ ht hk hs
    (by rw [h1]; exact hz) hl
  rw [h1, hp] at h
  exact ⟨_, _, h⟩

/-- The kind of a written round is neither a sealing nor one of seeds. -/
def PlainKind (d : RDT) : Prop := d.kind ≠ .sealed ∧ d.kind ≠ .seeds

/-- **The stretch's written rounds bear the entries that the block declares.** -/
structure Declared (P : Where) (dZ d0 : RDT) (ds : List RDT) : Prop where
  len : P.lin.kCol = ds.length
  sigma : dZ.entry = sigmaEntry P ∧ PlainKind dZ
  eps : d0.entry = epsEntry P ∧ PlainKind d0
  vars : ∀ d ∈ ds, d.entry = roundEntry P ∧ PlainKind d

/-- The witness's read part is what a decoder makes of the oracles. -/
def pinOf {F : Frame} {k : ℕ} (rw : W → Wit GE nR k) (dec : F.E.Str → Wit GE nR k) :
    F.E.Str → W → Prop := fun y w => rw w = dec y

/-- A decoder reads the stored table and the trees sent in front of the stretch alone. -/
def Local {F : Frame} {k : ℕ} (base : ℕ) (dec : F.E.Str → Wit GE nR k) : Prop :=
  ∀ y y', y.1 = y'.1 → (∀ j x, j < base → colAt F y j x = colAt F y' j x) → dec y = dec y'

/-- **The law, at the block's own entries and at any local decoder.** -/
theorem atM3_goodIn_dec (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (rw : W → Wit GE nR ds.length)
    (dec : F.E.Str → Wit GE nR ds.length) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) (fun _ => True)
      (RowsHold rw (pinOf rw dec)) (RowsHold rw (pinOf rw dec)) := by
  obtain ⟨nZ, aZ, hZ⟩ := sends_of_entry (d := dZ) (by rw [hD.sigma.1]; rfl)
    (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; exact Nat.zero_le 1)
    (by rw [hD.sigma.1]; exact Nat.zero_le 64) hD.sigma.2.1 hD.sigma.2.2
  obtain ⟨n0, a0, h0⟩ := sends_of_entry (d := d0) (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; rfl)
    (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; exact Nat.zero_le 1)
    (by rw [hD.eps.1]; exact Nat.zero_le 64) hD.eps.2.1 hD.eps.2.2
  refine atM3_goodIn F P base dZ d0 ds hD.len hZ h0 (fun d hd => ?_) rw (pinOf rw dec)
    (fun y w w' h h' => h.trans h'.symm) ?_
  · obtain ⟨he, hk⟩ := hD.vars d hd
    exact sends_of_entry (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
      (by rw [he]; exact Nat.zero_le 1) (by rw [he]; exact Nat.zero_le 64) hk.1 hk.2
  · exact back_of_reads _ (pinOf rw dec) fun y y' w h1 h2 hw => hw.trans (hloc y y' h1 h2)

/-- With the pin that holds of everything, the premise on the pin says that the reader is constant.
-/
theorem pin_true {F : Frame} {k : ℕ} (rw : W → Wit GE nR k) (y : F.E.Str) :
    (∀ (y : F.E.Str) w w', (fun (_ : F.E.Str) (_ : W) => True) y w →
      (fun (_ : F.E.Str) (_ : W) => True) y w' → rw w = rw w') ↔ ∀ w w', rw w = rw w' :=
  ⟨fun h w w' => h y w w' trivial trivial, fun h _ w w' _ _ => h w w'⟩

/-- The piece with a block in the joined block's place that refuses all. -/
def pieceNo (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT) :
    Piece (ckP .two) F S Cl W where
  b := { atM3 P with decide := fun _ _ _ => .error "no" }
  base := base
  ds := dZ :: d0 :: ds
  back := []
  ext := fun _ _ w => w
  err := (mapsOf dZ d0 ds).err (errK P.rows ds.length)

/-- It meets the form, at any two relations: a bound on what a cheating prover can reach is met by a
block that refuses all. -/
theorem goodIn_no (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (R R' : S × F.E.Str → W → Prop) :
    (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) (fun _ => True) R R'
    := by
  intro a _
  refine Doomed.of_forall _ _ fun τ b hb => ?_
  have hb' : (if sTests (ckP .two) (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ
      then (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).run a.1
        (sView (ckP .two) (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ)
      else none).map (fun xo =>
        (xo, (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).ior.imp a.2 τ)) = some b := hb
  split at hb'
  · cases hrun : (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).run a.1
        (sView (ckP .two) (pieceNo (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      obtain ⟨_, _, hdec⟩ := single_ok hrun
      have hdec' : (Except.error "no" : Except String S) = .ok s' := hdec
      cases hdec'
  · cases hb'

/-! ## A block that says yes to all and lays a row that is true of everything -/

/-- It has no round. Whatever the record, it lays the empty row with the target 0 as the claim. -/
def yesB : Block S Cl where
  name := "yes"
  place := ⟨1, none, 0, .K13⟩
  planOk := true
  rounds := []
  oracles := []
  before := []
  decide := fun s _ _ =>
    .ok { s with here := .mem ⟨#[], #[], some { claim := memberClaim ⟨[], [], [], zeroE⟩ }⟩ }
  claims := []
  after := []

/-- The piece that holds it: no written round, no error. -/
def pieceYes (F : Frame) (base : ℕ) : Piece (ckP .two) F S Cl W where
  b := yesB
  base := base
  ds := []
  back := []
  ext := fun _ _ w => w
  err := ()

/-- A record in front of the chain's end whose pile holds one row, which is false of everything. -/
def falsePile : S :=
  { S.blank with here := .between
                 out := { S.blank.out with pending := [⟨[], [], [], oneE⟩] } }

/-- **It does not meet the form of the law**: at every frame, at all oracles, with the witnesses
pinned to any one value. -/
theorem not_goodIn_yes (F : Frame) (base k : ℕ) (y : F.E.Str) (w₀ : Wit GE nR k) :
    ¬ (pieceYes (Cl := Cl) (W := Wit GE nR k) F base).GoodIn (fun _ => True) (fun _ => True)
      (RowsHold id (pinOf id fun _ => w₀)) (RowsHold id (pinOf id fun _ => w₀)) := by
  intro h
  have h1 : ∀ b, (pieceYes (Cl := Cl) (W := Wit GE nR k) F base).ior.red.out (falsePile, y) () =
      some b → True ∧ ∀ w, RowsHold id (pinOf id fun _ => w₀) b w →
        RowsHold id (pinOf id fun _ => w₀) (falsePile, y) w := h (falsePile, y) trivial
  have h2 := (h1 _ rfl).2 w₀ ⟨rfl, fun r hr => by
    obtain rfl := List.mem_singleton.1 hr
    show lhs ρg w₀ _ = ρg.val zeroE
    rw [rowOfClaim_member, lhs_nil, ρg.zero]⟩
  have h3 : lhs ρg w₀ (⟨[], [], [], oneE⟩ : TensorRow) = ρg.val oneE :=
    h2.2 _ (List.mem_singleton.2 rfl)
  rw [lhs_nil, ρg.one] at h3
  exact zero_ne_one h3

end VerifiableInference.Desc.K13.Law
