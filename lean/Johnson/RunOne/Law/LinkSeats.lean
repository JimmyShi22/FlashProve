-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkSeats.lean: THE SIX
SEATS OF A LOOKUP'S LINK ARE BOUND: in a row of pieces that hold a flat list's blocks, where six
seats in a row hold the six blocks of the link of lookup number i (Johnson/Desc/Key/Link.lean:
lookupLink), and the seven rows at their borders are ours (JoinKeyD.lean), a family over what is
handed to the chain, lifted (upF, SeatsAtFK.lean): each of the six pieces is good between its two
rows, with its errors below the bound (SeatGood, Johnson/Desc/Sound/KeySeatsAt.lean). The typed
block at the kind's seat is ONE for all that can be handed to the chain: what is handed lies in its
typed statement (TK P, RideKeyD.lean), so the decoder may read it.

"Bound", not "filled": the theorem stands under letters that are not exhibited.

Main names:
  andQ_on, low_andQ, low_row0, low_rowJ: the rows read, of the oracles, what the decoder reads.
  link_flat: the link's flat list: six blocks, and what each decides. rows7: the seven rows.
  rows7_meet: the last row of a link is the first row of the next.
  kAt, mapsAt: the proved typed block and the maps at the link. err_blind: its errors along the maps
    read none of the rows' letters.
  quiet_seats, k3_seat, link_seats: five seats; the seat of the kind's block; THE SIX SEATS.

Limits. Letters and debts, by name: the decoder dec, its condition cond and what else rides, Oth
(Blind; LowDec at each piece's place) · Prom (Promise: Hands and Fits lookup by lookup) AND, named
nowhere in the theorem, that Prom 0 holds at the record that stands behind the sending of the second
message, in front of the first link: without it the promise that never holds meets Promise, the rows
are off everywhere and the six seats say nothing · wd, mx · Adm · l.d ≤ 64 · lookupOk · fitsMatrix ·
lookups[i]? · the layout's first block fits · i < n · the pieces hold the flat list's blocks, six of
which are the link's · the seven rows are the link's · no two trees of the frame's list have one
number · a value st0 of the riding part's type · the witnesses' type M × Wp is not empty · each
piece's errors lie below the bound · the piece of the kind's block puts no round back, its stretch
is MadeOf the lookup's shape, and the typed lookup's errors along the maps lie below its errors.
Promise is met at a promise written out in PromKeyD.lean.

-/
import Johnson.RunOne.Law.JoinKeyD
import Johnson.RunOne.Law.SeatsAtFK
import Johnson.Desc.Sound.KeySeatsLe

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinkSeats
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Block claimsIn viewWordsBelowPrime afterIn)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim LookupRecord lookupSeat caller layer lookupLink
  layerOrder lookupPlace)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkKeyD
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsAtFK

variable {Fr : Frame} {P : Type}

theorem andQ_on (X : JointRow FirstState Fr) (Q : FirstState → Prop) (a : FirstState × Fr.E.Str) :
    (andQ X Q).on a ↔ X.on a ∧ Q a.1 :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- A promise on the record reads no oracle. -/
theorem low_andQ {X : JointRow FirstState Fr} {c : ℕ} (Q : FirstState → Prop)
    (h : ReadsBelow c (up P X).on ∧ ReadsBelow c (up P X).rel) :
    ReadsBelow c (up P (andQ X Q)).on ∧ ReadsBelow c (up P (andQ X Q)).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, h.2⟩
  have e : X.on (t.2, y) = X.on (t.2, y') := h.1 t y y' h1 h2
  show (andQ X Q).on (t.2, y) ↔ (andQ X Q).on (t.2, y')
  rw [andQ_on, andQ_on, e]

variable {one : OneTime} {set : Setting} {id : ℕ} {m : Wf.Matrix} {L : ℕ → WfLookup}
  {oL kL : ℕ → List ℕ} {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE}
  {dec : TK P × Fr.E.Str → Option M} {cond : TK P × Fr.E.Str → Prop} {n : ℕ}
  {Oth : TK P → M × Wp → Prop}

theorem low_row0 {A : Lk6.Dat GE} {stOf : FirstState → A.St} {Kc : Type}
    {R0 : IOR.Rels Kc A.St Fr.E (M × Wp)} {msg : M → A.J → GE} {i : ℕ} {l : WfLookup}
    {o k : List ℕ} {c : ℕ} (h : ReadsLow A R0 c) :
    ReadsBelow c (up P (row0 one i id m l o k idxN A stOf R0 msg)).on ∧
      ReadsBelow c (up P (row0 one i id m l o k idxN A stOf R0 msg)).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, fun t y y' h1 h2 => propext ?_⟩
  · exact and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).1
  · exact exists_congr fun w => and_congr_left fun _ => (h (stOf t.2) y y' h1 h2).2 w

theorem low_rowJ (p₀ : P) (Q : FirstState → Prop) (i c : ℕ) (h : LowDec dec cond c) :
    ReadsBelow c (up P (rowJ p₀ id m L wd mx dec cond n Oth Q i)).on ∧
      ReadsBelow c (up P (rowJ p₀ id m L wd mx dec cond n Oth Q i)).rel := by
  refine ⟨fun t y y' h1 h2 => propext ?_, fun t y y' h1 h2 => propext ?_⟩
  · exact and_congr_left fun _ => and_congr_left fun _ => (h (stK p₀ i t.2) y y' h1 h2).2
  · refine exists_congr fun w => and_congr_left fun _ => ?_
    show dec (stK p₀ i t.2, y) = some w.1 ↔ dec (stK p₀ i t.2, y') = some w.1
    rw [(h (stK p₀ i t.2) y y' h1 h2).1]

/-- The link's flat list: six blocks, and what each decides. -/
theorem link_flat (one : OneTime) (set : Setting) (i : ℕ) (x : VerifiableInference.Desc.Key.Lookup)
    :
    ∃ c0 c4 c5 : Block FirstState Claim,
      (lookupLink one set i x).blocksInOrder =
        [c0, caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x),
          layer one set i x
            (claimsIn [caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i
                    x)]
              [(1, "objects"), (1, "planes"), (1, "guests")]), c4, c5] ∧
      (∀ s rs gs, c0.decide s rs gs = (lookupLink one set i x).lay s) ∧
      (∀ s rs gs, c4.decide s rs gs =
        afterIn [caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)] []
            s) ∧
      ∀ s rs gs, c5.decide s rs gs = (lookupLink one set i x).clear s :=
  ⟨_, _, _, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The seven rows at the borders of the link of lookup number i.** -/
def rows7 (p₀ : P) (one : OneTime) (set : Setting) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup)
    (oL kL : ℕ → List ℕ) (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
    (dec : TK P × Fr.E.Str → Option M) (cond : TK P × Fr.E.Str → Prop) (n : ℕ) (Prom : ℕ →
        FirstState →
        Prop)
    (i : ℕ) (Wp : Type) (Oth : TK P → M × Wp → Prop) : ℕ → JointRow FirstState Fr
  | 0 => rowJ p₀ id m L wd mx dec cond n Oth (Prom i) i
  | 1 => andQ (row0At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom i)
  | 2 => andQ (rowInAt p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1))
  | 3 => andQ (rowOutAt p₀ one set id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1))
  | 4 => andQ (row3At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1))
  | 5 => andQ (row3At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1))
  | _ => rowJ p₀ id m L wd mx dec cond n Oth (Prom (i + 1)) (i + 1)

/-- The last row of a link is the first row of the next. -/
theorem rows7_meet (p₀ : P) (one : OneTime) (set : Setting) (id : ℕ) (m : Wf.Matrix) (L : ℕ →
    WfLookup)
    (oL kL : ℕ → List ℕ) (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
    (dec : TK P × Fr.E.Str → Option M) (cond : TK P × Fr.E.Str → Prop) (n : ℕ) (Prom : ℕ →
        FirstState →
        Prop)
    (i : ℕ) (Oth : TK P → M × Wp → Prop) :
    rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom i Wp Oth 6 =
      rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom (i + 1) Wp Oth 0 :=
  rfl

variable {W : Type} {Prom : ℕ → FirstState → Prop} (εs : ℝ≥0∞) (A0 : JointRow (P × FirstState) Fr)
  (ps : List (Piece (ckP .two) Fr (P × FirstState) Claim W)) (rs : List (JointRow (P × FirstState)
      Fr))
  (bs : List (Block FirstState Claim)) (a i : ℕ)

/-- **The five seats of the link that cost no error are bound.** -/
theorem quiet_seats
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hlink : ∀ j < 6, bs[a + j]? =
      (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]?)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (a + j) =
      upF fun p₀ => (rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom i Wp Oth j))
    (hnd : (Fr.all.map (·.no)).Nodup) (hP : Promise one id m L oL kL idxN n Prom)
    (hB : Blind dec cond Oth) (hi : i < n)
    (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p)
    (hlo : Wf.lookupOk Wf.fBits (L i) = true) (hfm : Wf.fitsMatrix m (L i) = true)
    (hli : one.ranges.lookups[i]? = some (L i))
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true)
    (hpc : ∀ j < 6, ∀ p, ps[a + j]? = some p → Err.Below p.err εs ∧ LowDec dec cond p.base) :
    ∀ j < 6, j ≠ 2 → SeatGood εs A0 ps rs (a + j) := by
  obtain ⟨c0, c4, c5, hF, d0, d4, d5⟩ := link_flat one set i (Wf.lookupOf id m (L i))
  have hY : ∀ j < 6, keyRowAt A0 rs (a + j + 1) =
      upF fun p₀ => (rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom i Wp Oth (j + 1)) :=
      fun j hj => by
    rw [Nat.add_assoc]
    exact hr (j + 1) hj
  have hat : ∀ j (hj : j < 6) (c : Block FirstState Claim),
      (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]? = some c →
      ∀ p, ps[a + j]? = some p → p.b = liftP P (below c) := fun j hj c hc p hp =>
    block_at ps bs hbs (a + j) p c hp ((hlink j hj).trans hc)
  intro j hj hj2
  have cases6 : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases cases6 with rfl | rfl | rfl | rfl | rfl
  · exact tie_seatF εs A0 ps rs (a + 0)
      (fun p₀ => laid_tie (p₀ := p₀) (b := c0) (fun s s' rs gs h => lay_same ((d0 s rs gs) ▸ h))
        (Prom i) i fun s => hP.gives i s hi) (hr 0 (by omega)) (hY 0 hj) hnd fun p hp =>
      ⟨hat 0 hj c0 (by rw [hF]; rfl) p hp, (hpc 0 hj p hp).1,
        low_upF fun _ => low_andQ (Prom i) (low_row0 (low_R i p.base (hpc 0 hj p hp).2))⟩
  · exact tie_seatF εs A0 ps rs (a + 1) (fun p₀ => callerJ_tie (p₀ := p₀) hP i) (hr 1 (by omega))
      (hY 1 hj) hnd fun p hp => ⟨hat 1 hj _ (by rw [hF]; rfl) p hp, (hpc 1 hj p hp).1,
        low_upF fun _ => low_andQ (Prom (i + 1)) (low_rowIn (low_R i p.base (hpc 1 hj p hp).2))⟩
  · exact tie_seatF εs A0 ps rs (a + 3)
      (fun p₀ => layerJ_tie (p₀ := p₀) hP i hadm hlo hfm hli hla) (hr 3 (by omega))
      (hY 3 hj) hnd fun p hp => ⟨hat 3 hj _ (by rw [hF]; rfl) p hp, (hpc 3 hj p hp).1,
        low_upF fun _ => low_andQ (Prom (i + 1)) (low_row3 (low_R i p.base (hpc 3 hj p hp).2))⟩
  · exact tie_seatF εs A0 ps rs (a + 4)
      (fun _ => same_tie (b := c4) _ fun s s' rs gs h => after_same ((d4 s rs gs) ▸ h))
      (hr 4 (by omega))
      (hY 4 hj) hnd fun p hp => ⟨hat 4 hj c4 (by rw [hF]; rfl) p hp, (hpc 4 hj p hp).1,
        low_upF fun _ => low_andQ (Prom (i + 1)) (low_row3 (low_R i p.base (hpc 4 hj p hp).2))⟩
  · exact tie_seatF εs A0 ps rs (a + 5)
      (fun p₀ => cleared_tie (p₀ := p₀) (b := c5)
        (fun s s' rs gs h => clear_eq ((d5 s rs gs) ▸ h)) hB (Prom (i + 1))
        (Prom (i + 1)) i fun s => hP.blind (i + 1) s none none #[]) (hr 5 (by omega)) (hY 5 hj) hnd
      fun p hp =>
      ⟨hat 5 hj c5 (by rw [hF]; rfl) p hp, (hpc 5 hj p hp).1,
        low_upF fun p₀ => low_rowJ p₀ (Prom (i + 1)) (i + 1) p.base (hpc 5 hj p hp).2⟩

/-- The proved typed block at the link of lookup number i. -/
abbrev kAt (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ → List ℕ)
    (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE) (dec : TK P × Fr.E.Str → Option M)
    (cond : TK P × Fr.E.Str → Prop) (n i : ℕ) (Wp : Type) (Oth : TK P → M × Wp → Prop) :=
  bkLam (AK one id m (L i) (oL i) (kL i) idxN (TK P)) (PK one id m (L i) (oL i) (kL i) idxN (TK P))
      Fr.E
    (R id m L wd mx dec cond n Oth i) (msgk one i id m (L i) (oL i) (kL i) idxN (TK P) wd mx)

/-- The maps from a written stretch to the typed lookup's rounds. -/
abbrev mapsAt (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ → List ℕ)
    (idxN i : ℕ) (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p) (hd : (L i).d ≤ 64)
    (st0 : TK P) (ds : List RDT)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf id m (L i))))) :=
  mapsOf (Lk6.lamS_runs (AK one id m (L i) (oL i) (kL i) idxN (TK P))
    (PK one id m (L i) (oL i) (kL i) idxN (TK P)) Fr.E).rd ds
    (meets_typed (AK one id m (L i) (oL i) (kL i) idxN (TK P)) st0
      (PK one id m (L i) (oL i) (kL i) idxN (TK P)) Fr.E (faceOfLkp (Wf.lookupOf id m (L i)))
      (faceIsK (TK P) id m (L i) (homeT one id m (L i) (oL i) (kL i) idxN).toList st0 hadm hd) hadm
          ds
      hds).1.length_eq

/-- The typed lookup's errors along the maps read neither the decoder, nor its condition, nor what
else rides, nor how a witness's messages are read. -/
theorem err_blind (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ → List ℕ)
    (idxN : ℕ) (wd wd' : M → Means.Words GE) (mx mx' : M → ℕ → ℕ → GE)
    (dec dec' : TK P × Fr.E.Str → Option M) (cond cond' : TK P × Fr.E.Str → Prop) (n i : ℕ)
    (Oth Oth' : TK P → M × Wp → Prop) (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p)
    (hd : (L i).d ≤ 64) (st0 : TK P) (ds : List RDT)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf id m (L i))))) :
    (mapsAt (Fr := Fr) one id m L oL kL idxN i hadm hd st0 ds hds).err
        (kAt one id m L oL kL idxN wd mx dec cond n i Wp Oth).err =
      (mapsAt (Fr := Fr) one id m L oL kL idxN i hadm hd st0 ds hds).err
        (kAt one id m L oL kL idxN wd' mx' dec' cond' n i Wp Oth').err :=
  rfl

set_option maxHeartbeats 1600000 in
/-- **The seat of the kind's own block is bound.** -/
theorem k3_seat
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hlink : ∀ j < 6, bs[a + j]? =
      (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]?)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (a + j) =
      upF fun p₀ => (rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom i Wp Oth j))
    (hnd : (Fr.all.map (·.no)).Nodup) (hP : Promise one id m L oL kL idxN n Prom)
    (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p) (hd : (L i).d ≤ 64) (st0 : TK P)
    (hne : Nonempty (M × Wp))
    (hpc : ∀ j < 6, ∀ p, ps[a + j]? = some p → Err.Below p.err εs ∧ LowDec dec cond p.base)
    (hk3 : ∀ p, ps[a + 2]? = some p → p.back = [] ∧
      ∃ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf id m (L i)))),
        Err.le ((mapsAt (Fr := Fr) one id m L oL kL idxN i hadm hd st0 p.ds hds).err
          (kAt one id m L oL kL idxN wd mx dec cond n i Wp Oth).err) p.err) :
    SeatGood εs A0 ps rs (a + 2) := by
  obtain ⟨c0, c4, c5, hF, -, -, -⟩ := link_flat one set i (Wf.lookupOf id m (L i))
  refine seat_of_relLawLe εs A0 ps rs (a + 2)
    (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i (Wf.lookupOf id m (L i))))
    (kAt one id m L oL kL idxN wd mx dec cond n i Wp Oth) (fun t => (stK t.1.1 i t.1.2, t.2))
    (bkLam_good _ _ Fr.E _ _ hadm (pins_R i)) hne fun p hp => ?_
  obtain ⟨hb0, hds, herr⟩ := hk3 p hp
  refine ⟨block_at ps bs hbs (a + 2) p _ hp ((hlink 2 (by omega)).trans (by rw [hF]; rfl)),
    mapsAt one id m L oL kL idxN i hadm hd st0 p.ds hds, mapsOf_ok _ p.ds (meets_typed _ st0 _ Fr.E
      _ (faceIsK (TK P) id m (L i) _ st0 hadm hd) hadm p.ds hds).1, by rw [hb0]; rfl, herr,
    (hpc 2 (by omega) p hp).1, fun q => ?_⟩
  rw [hr 2 (by omega), Nat.add_assoc, hr 3 (by omega), hb0]
  refine relLaw_upF q ?_
  exact k3Q_law (one := one) (set := set) (id := id) (m := m) (idxN := idxN)
    (A := AK one id m (L i) (oL i) (kL i) idxN (TK P)) (sl := slk one id m (L i) (oL i) (kL i) idxN
        (TK P))
    (stOf := stK q i) (R0 := R id m L wd mx dec cond n Oth i)
    (msg := msgk one i id m (L i) (oL i) (kL i) idxN (TK P) wd mx) (l := L i) (o := oL i) (k := kL
        i)
    (Prom (i + 1)) (hP.blind (i + 1)) i [(1, 0), (1, 1)] 0 p.base p.ds (rides_stK q i) hnd
    (fun st => faceIsK (TK P) id m (L i) _ st hadm hd) hadm
    (low_R i p.base (hpc 2 (by omega) p hp).2) hds st0

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER i ARE BOUND.** a: the place of the link's first
block in the flat list. -/
theorem link_seats
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hlink : ∀ j < 6, bs[a + j]? =
      (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]?)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (a + j) =
      upF fun p₀ => (rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom i Wp Oth j))
    (hnd : (Fr.all.map (·.no)).Nodup) (hP : Promise one id m L oL kL idxN n Prom)
    (hB : Blind dec cond Oth) (hi : i < n)
    (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p) (hd : (L i).d ≤ 64)
    (hlo : Wf.lookupOk Wf.fBits (L i) = true) (hfm : Wf.fitsMatrix m (L i) = true)
    (hli : one.ranges.lookups[i]? = some (L i))
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true)
    (st0 : TK P) (hne : Nonempty (M × Wp))
    (hpc : ∀ j < 6, ∀ p, ps[a + j]? = some p → Err.Below p.err εs ∧ LowDec dec cond p.base)
    (hk3 : ∀ p, ps[a + 2]? = some p → p.back = [] ∧
      ∃ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf id m (L i)))),
        Err.le ((mapsAt (Fr := Fr) one id m L oL kL idxN i hadm hd st0 p.ds hds).err
          (kAt one id m L oL kL idxN wd mx dec cond n i Wp Oth).err) p.err) :
    ∀ j < 6, SeatGood εs A0 ps rs (a + j) := by
  intro j hj
  by_cases h2 : j = 2
  · subst h2
    exact k3_seat εs A0 ps rs bs a i hbs hlink hr hnd hP hadm hd st0 hne hpc hk3
  · exact quiet_seats εs A0 ps rs bs a i hbs hlink hr hnd hP hB hi hadm hlo hfm hli hla hpc j hj h2

end Johnson.RunOne.Law.LinkSeats

#print axioms Johnson.RunOne.Law.LinkSeats.low_andQ
#print axioms Johnson.RunOne.Law.LinkSeats.low_row0
#print axioms Johnson.RunOne.Law.LinkSeats.low_rowJ
#print axioms Johnson.RunOne.Law.LinkSeats.link_flat
#print axioms Johnson.RunOne.Law.LinkSeats.rows7_meet
#print axioms Johnson.RunOne.Law.LinkSeats.err_blind
#print axioms Johnson.RunOne.Law.LinkSeats.quiet_seats
#print axioms Johnson.RunOne.Law.LinkSeats.k3_seat
#print axioms Johnson.RunOne.Law.LinkSeats.link_seats
