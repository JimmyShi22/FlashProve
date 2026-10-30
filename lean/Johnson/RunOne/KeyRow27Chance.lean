-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow27Chance.lean: THE KEY FILE, ROW 2.7 ("LIN zeta"): THE CHANCE's HALF, at the
letters of the key file's tables (Johnson/RunOne/KeyRows23At.lean: on₂, R₂, L₂),
in the form that keeps₂_of_halves' asks
(KeyHalves23.lean): Leads (on₂ … 7) (fun x x' => L₂ … 8 x' → L₂ … 7 x) at the piece's own
errors.

OBJECT   a piece pc whose block's yes leaves what was handed to the chain and is linZeta on the
chain's own record (hz): meant: the
         key file's description's eighth block of the shared chain, K14's "LIN zeta", as the maker
         holds it.
USER     the joining of the two halves into Keeps (keeps₂_of_halves',
Johnson/RunOne/KeyHalves23.lean): CALLED in
         Johnson/RunOne/KeyRow27Keeps.lean [not in this library]; then the field r2_7 of The21.
LETTERS  the tables': F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂. Beside: a finite field K, a
reading ρ, a count c, and G:
         the written round read as one typed draw.
FOR THE FIELD r2_7 (the key file's frame on the plain road, The35.lean): NOT PAID HERE.

  claim₂_zeta · rides_zeta   every item but (Fold) rides back over "LIN zeta": from the record and
  the strings behind to those in front
  of_eq_of_pins     beside the promise's NoColl two pinned witnesses show one table at message k
  (pin_one, Johnson/Desc/Msg.lean; Free₂.reads)
  zeta_half₂        THE HALF. By fold_core (the chance of "LIN zeta" with no kind named): the set of
  bad points is counted at one
                    witness; of_eq_of_pins at messages 3 and 4 makes it the set of every pinned
                    witness. Then (DotOm) is (DotU)
                    (dotOm_iff_dotU, KeyMeaning23.lean).
  hz_held · zeta_half₂_at   hz PAID at a block b whose yes is linZeta (hb), as the maker holds it:
  the test "below the prime" in front,
                    lifted to the rule's record · zeta_hb: hb at K14's own seventh block
                    (zeta_of_blocks, Johnson/Desc/K14/Law/
                    BlocksSound.lean) AND AT WHATEVER BLOCK HAS ITS decide: so at the block as the
                    key file's description seats it.
  zetaSeat · zeta_half₂_seat   THE CARRIAGE PAID TOO (c, G, fits, hread), as in
  Johnson/Desc/K14/Law/ZetaRead.lean: the piece at ONE
                    written round d that draws kRow elements and no position (SendsDraws), in the
                    library's field (Reading.gl), at
                    the written count that bears e ≥ kRow |K| ^ (kRow - 1). LEFT THERE: hb · hd · he
                    · hsame · hbase · hpins.

PREMISES, each with its payer. hz: K14's files (the block's text) · hsame: whoever fills the letter
R (meant as ρ a = ρ b) ·
hbase: public: the open pins' trees lie in front of the piece · hpins: whoever fills G₂: under the
promise in
front, the reading's samples and record do not read zFd (at the tables' own BaseSt.h₂ it is rfl:
pinsStay_h₂_zeta,
Johnson/RunOne/KeyRow27Pins.lean) · c, G, fits, hread: paid in § 6 · that the written count lies
below
the maker's cap: a number (K14_rounds), not here.
NO MEMBER SHOWN: no statement inside on₂ … 7 is shown at the key file's own letters: until
then this law MAY BE TRUE AND
EMPTY AT THE REAL PROTOCOL and closes nothing. A CONDITION ON THE LETTER M:
NoColl is EQUALITY IN M, while the
claims' "is" is "reads as" (R.same): at an M with two tables of one reading (words not below the
prime; places that enc and meets do
not read) the promise's NoColl and the pins cross, and this half is idle: the filling of M must have
one table a reading.
A block that refuses all has the law too. No soundness of a verifier.

-/
import Johnson.RunOne.KeyMap23
import Johnson.RunOne.KeyIdPiece
import Johnson.Desc.Key.KeyKeeps
import Johnson.Desc.Key.KeyLetters
import Johnson.Desc.Plain.PieceYes
import Johnson.Desc.K14.Law.ZetaRead
import Johnson.Desc.K14.Law.ZetaWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR)
open _root_.Iop.IOR (drawRound)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14 (linZeta)
open _root_.Desc.K14.Law (fold_core linZeta_one linZeta_inv zeta_of_blocks vecMaps vecMaps_ok
    vecMaps_pass drawn_shown shownAt
  piece_tests)
open _root_.Desc.K14.Law.ZetaWords

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-! ## 1 The table at the two borders -/

theorem open₂_78 : ∀ i ∈ open₂ 7, i = KItem.claim 2 "DotU" ∨ (i ∈ open₂ 8 ∧ i ≠ KItem.claim 2
    "Fold") := by decide
theorem pinned₂_87 : ∀ j ∈ pinned (open₂ 8), j ∈ pinned (open₂ 7) := by decide

/-! ## 2 What rides back -/

/-- A claim of the shared chain but (Fold) reads nothing of zFd, and of the strings the stored cells
alone. -/
theorem claim₂_zeta (c : Nat) (n : String) (hcn : ¬ (c = 2 ∧ n = "Fold")) (p : P₂) (s : St₂) (d :
    List E) (y y' : Strs)
    (w : Wit Cells Unit M) (h : y'.cell = y.cell)
    (hu : (meaning₂ S K₁ R enc rad).claim c n (p, { s with loc := { s.loc with zFd := d } }) y' w) :
    (meaning₂ S K₁ R enc rad).claim c n (p, s) y w := by
  simp only [meaning₂, claim₂, NearUAt] at hu ⊢
  rw [h] at hu
  simp only [if_neg hcn] at hu ⊢
  exact hu

/-- **Every item but (Fold) rides back over "LIN zeta".** -/
theorem rides_zeta (O : List KItem) (i : KItem) (hi : i ∈ O) (hF : i ≠ KItem.claim 2 "Fold") (p :
    P₂) (s : St₂) (d : List E)
    (y y' : Strs) (w : Wit Cells Unit M) (Hy : StrsStay F at_ O y y')
    (hp : PinsStay G₂ at_ (pinned O) (p, s) (p, { s with loc := { s.loc with zFd := d } }))
    (hu : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) (p, { s with loc := { s.loc with zFd := d } })
        y' w) :
    i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) (p, s) y w := by
  cases i with
  | pinT => exact rides_pinT2_at G₂ _ _ y y' w hp.recOf Hy.cell hu
  | pin k => exact rides_pin2_at F G₂ _ _ _ _ y y' w (hp.smp k (mem_pinned O k hi)) (Hy.word k
      (mem_pinned O k hi)) hu
  | claim c n =>
    exact claim₂_zeta S K₁ R enc rad c n (fun h => hF (by rw [h.1, h.2])) p s d y y' w Hy.cell hu
  | _ => exact hu

/-! ## 3 Two pinned witnesses show one table -/

theorem of_eq_of_pins (k : Nat) (hk : k ∈ [0, 2, 3, 4, 5]) (hk7 : k ∈ pinned (open₂ 7)) (x : (P₂ ×
    St₂) × Fr₂.E.Str)
    (hx : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x) (w w' : Wit Cells Unit M)
    (q : PIN F G₂ (at_ k).1 (at_ k).2 x.1 (strsOf Fr₂ x.2) w) (q' : PIN F G₂ (at_ k).1 (at_ k).2 x.1
        (strsOf Fr₂ x.2) w') :
    R.of w' k = R.of w k := by
  unfold on₂ onAt at hx
  rcases hx with h0 | ⟨-, -, hfree, hnc⟩
  · exact (h0 trivial).elim
  · rw [hfree.reads w' k hk, hfree.reads w k hk]
    exact (pin_one F G₂ _ _ _ _ w w' (hnc k hk7) q q').symm

/-! ## 4 The half -/

variable {K : Type} [Field K] [Fintype K] (ρ : OnBytes.Model.Reading K)

omit [Fintype K] in
theorem sameLaws_of_val (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) : SameLaws R.same :=
  ⟨fun _ => (hsame _ _).2 rfl, fun h => (hsame _ _).2 ((hsame _ _).1 h).symm,
    fun h k => (hsame _ _).2 (((hsame _ _).1 h).trans ((hsame _ _).1 k)),
    fun h k => (hsame _ _).2 (by rw [ρ.add, ρ.add, (hsame _ _).1 h, (hsame _ _).1 k]),
    fun h k => (hsame _ _).2 (by rw [ρ.mul, ρ.mul, (hsame _ _).1 h, (hsame _ _).1 k])⟩

/-- **ROW 2.7, THE CHANCE's HALF.** -/
theorem zeta_half₂ (pc : Piece C Fr₂ (P₂ × St₂) Cl W)
    (hz : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ linZeta z.2 rs = some z'.2)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < pc.base)
    (hpins : ∀ x, on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x → ∀ d,
      PinsStay G₂ at_ (pinned (open₂ 8)) (x.1.1, x.1.2) (x.1.1, { x.1.2 with loc := { x.1.2.loc with
          zFd := d } }))
    (c : Nat) (hc : S.kRow * Fintype.card K ^ (S.kRow - 1) ≤ c)
    (G : (P₂ × St₂) × Fr₂.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin S.kRow → K)])
    (fits : ∀ x, (G x).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ x τ x', on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x → pc.ior.red.out x τ =
        some x' →
      ∃ z, (G x).tr τ = some (((), ()), z, ()) ∧ x'.1.2.loc.zFd.map ρ.val = List.ofFn z) :
    pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7)
      (fun x x' => L₂ F Fr₂ G₂ at_ S K₁ R enc rad 8 x' → L₂ F Fr₂ G₂ at_ S K₁ R enc rad 7 x) pc.err
          := by
  -- what a yes does to the record
  have step : ∀ x τ x', pc.ior.red.out x τ = some x' →
      ∃ d, x'.1 = (x.1.1, { x.1.2 with loc := { x.1.2.loc with zFd := d } }) := by
    intro x τ x' hout
    obtain ⟨e1, e2⟩ := hz _ _ _ _ (piece_decides_at pc x τ x' hout)
    obtain ⟨r, hr⟩ := linZeta_one _ _ _ e2
    rw [hr] at e2
    exact ⟨_root_.Desc.K14.drawn r, Prod.ext e1 (linZeta_inv _ _ r e2)⟩
  have hback : ∀ x τ x' (w : Wit Cells Unit M), on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7
      x →
      pc.ior.red.out x τ = some x' → R₂ F Fr₂ G₂ at_ S K₁ R enc rad 8 x' w →
      ∀ i ∈ open₂ 8, i ≠ KItem.claim 2 "Fold" → i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1
          (strsOf Fr₂ x.2) w := by
    intro x τ x' w hx hout hw i hi hF
    obtain ⟨d, hd⟩ := step x τ x' hout
    have Hy7 := strsStay_of_out F Fr₂ at_ pc (open₂ 7) hbase x x' τ hout
    have Hy : StrsStay F at_ (open₂ 8) (strsOf Fr₂ x.2) (strsOf Fr₂ x'.2) :=
      ⟨Hy7.cell, fun k hk => Hy7.word k (pinned₂_87 k hk)⟩
    have hu := hw i hi
    rw [hd] at hu
    exact rides_zeta F G₂ at_ S K₁ R enc rad (open₂ 8) i hi hF x.1.1 x.1.2 d _ _ w Hy (hpins x hx d)
        hu
  have core := fold_core (K := K) (idPiece (Wit Cells Unit M) pc) S
      (_root_.Desc.K14.Law.le_two_pow_ceilLog2 _) (fun _ _ _ => rfl)
    (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7) (fun _ => True)
    (fun x w => ∀ i ∈ open₂ 8, i ≠ KItem.claim 2 "Fold" →
      i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) w)
    (fun x' w => R₂ F Fr₂ G₂ at_ S K₁ R enc rad 8 x' w)
    (fun x => (x.1.2.loc.psiSh.take S.kLo).map ρ.val) (fun x => x.1.2.loc.zFd.map ρ.val)
    (fun x w j => ρ.val (omOf (plan₂ S) R x.1.2.st.codes w j))
    (fun x w i => ρ.val (uOf (plan₂ S) R x.1.2.st.codes w i))
    (fun _ _ _ _ _ => trivial) hback
    (fun x w w' hx h h' => by
      have e4 := of_eq_of_pins F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 4 (by decide) (by
          decide) x hx w w'
        (h (.pin 4) (by decide) (by decide)) (h' (.pin 4) (by decide) (by decide))
      have e3 := of_eq_of_pins F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 3 (by decide) (by
          decide) x hx w w'
        (h (.pin 3) (by decide) (by decide)) (h' (.pin 3) (by decide) (by decide))
      refine ⟨funext fun j => ?_, funext fun i => ?_⟩
      · show ρ.val (omOf (plan₂ S) R x.1.2.st.codes w' j) = ρ.val (omOf (plan₂ S) R x.1.2.st.codes w
          j)
        unfold omOf
        rw [e4]
      · show ρ.val (uOf (plan₂ S) R x.1.2.st.codes w' i) = ρ.val (uOf (plan₂ S) R x.1.2.st.codes w
          i)
        unfold uOf
        rw [e3])
    (fun x τ x' w _ hout => by
      obtain ⟨d, hd⟩ := step x τ x' hout
      dsimp only
      rw [hd]
      exact ⟨rfl, rfl, rfl⟩)
    c hc G fits hread
  intro x hx
  refine Iop.Doomed.mono _ _ (fun τ hτ x' hout => ?_) (core x hx)
  rintro ⟨w, hw⟩
  have hfold : FoldAt R.same (plan₂ S).lin ((readers₂ S).psi x'.1) ((readers₂ S).zeta x'.1.2)
      (uOf (plan₂ S) R ((readers₂ S).st x'.1.2).codes w) (omOf (plan₂ S) R ((readers₂ S).st
          x'.1.2).codes w) :=
    hw (.claim 2 "Fold") (by decide)
  obtain ⟨hA, hcol⟩ := (hτ x' hout).2 w ⟨hw, foldEq_of_val ρ S _ _ _ _ ((hsame _ _).1 hfold)⟩
  refine ⟨w, fun i hi => ?_⟩
  rcases open₂_78 i hi with rfl | hi8
  · have hdo : ∃ g, (readers₂ S).g x.1 = some g ∧ DotOmAt R.same (plan₂ S).lin g ((readers₂ S).psi
      x.1)
        (omOf (plan₂ S) R ((readers₂ S).st x.1.2).codes w) (vOf' (plan₂ S) R ((readers₂ S).st
            x.1.2).codes w) :=
      hA (.claim 2 "DotOm") (by decide) (by decide)
    obtain ⟨g, hg, hdot⟩ := hdo
    have hdu : ∃ g, (readers₂ S).g x.1 = some g ∧ DotUAt R.same (plan₂ S).lin g ((readers₂ S).psi
        x.1)
        (uOf (plan₂ S) R ((readers₂ S).st x.1.2).codes w) (vOf' (plan₂ S) R ((readers₂ S).st
            x.1.2).codes w) :=
      ⟨g, hg, (dotOm_iff_dotU (sameLaws_of_val R ρ hsame) S g _ _ _ _
        (fun y hy => (hsame _ _).2 (val_of_colIs ρ S _ _ _ hcol y hy))).1 hdot⟩
    exact hdu
  · exact hA i hi8.1 hi8.2

/-! ## 5 The object: K14's own seventh block, as the maker holds it -/

omit [Field K] [Fintype K] in
/-- As the maker holds a block (the test "below the prime" in front; lifted to the rule's record):
hz. -/
theorem hz_held {P : Type} (b : Block St₂ Cl) (hb : ∀ d rs gs d', b.decide d rs gs = .ok d' →
    linZeta d rs = some d')
    (z : P × St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (z' : P × St₂)
    (hd : (Block.lift Prod.snd (fun t s => (t.1, s)) (below b) : Block (P × St₂) Cl).decide z rs gs
        = .ok z') :
    z'.1 = z.1 ∧ linZeta z.2 rs = some z'.2 := by
  have hd' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide z.2 rs gs
      else .error "a word is not below the prime").map fun s => (z.1, s)) = .ok z' := hd
  split at hd'
  · cases hb' : b.decide z.2 rs gs with
    | error e => rw [hb'] at hd'; cases hd'
    | ok s' =>
      rw [hb'] at hd'
      obtain rfl : (z.1, s') = z' := Except.ok.inj hd'
      exact ⟨rfl, hb _ _ _ _ hb'⟩
  · cases hd'

/-- **ROW 2.7, THE CHANCE's HALF, AT A BLOCK AS THE MAKER HOLDS IT**: b: any block whose yes is
linZeta (hb): K14's own seventh block
(zeta_of_blocks), or that block as a description seats it (retyped, its claims bared: the same
decide). -/
theorem zeta_half₂_at (b : Block St₂ Cl) (hb : ∀ d rs gs d', b.decide d rs gs = .ok d' → linZeta d
    rs = some d')
    (pc : Piece C Fr₂ (P₂ × St₂) Cl W) (hpc : pc.b = Block.lift Prod.snd (fun t s => (t.1, s))
        (below b))
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < pc.base)
    (hpins : ∀ x, on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x → ∀ d,
      PinsStay G₂ at_ (pinned (open₂ 8)) (x.1.1, x.1.2) (x.1.1, { x.1.2 with loc := { x.1.2.loc with
          zFd := d } }))
    (c : Nat) (hc : S.kRow * Fintype.card K ^ (S.kRow - 1) ≤ c)
    (G : (P₂ × St₂) × Fr₂.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin S.kRow → K)])
    (fits : ∀ x, (G x).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ x τ x', on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x → pc.ior.red.out x τ =
        some x' →
      ∃ z, (G x).tr τ = some (((), ()), z, ()) ∧ x'.1.2.loc.zFd.map ρ.val = List.ofFn z) :
    pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7)
      (fun x x' => L₂ F Fr₂ G₂ at_ S K₁ R enc rad 8 x' → L₂ F Fr₂ G₂ at_ S K₁ R enc rad 7 x) pc.err
          :=
  zeta_half₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ ρ pc
    (fun z rs gs z' h => hz_held b hb z rs gs z' (hpc ▸ h))
    hsame hbase hpins c hc G fits hread

end

/-! ## 6 The carriage paid: one written round that draws kRow elements, in the library's field -/

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- The piece that holds K14's block as the maker holds it, at one written round d; its errors: the
written count that bears e. -/
def zetaSeat (b : Block St₂ Cl) (base : Nat) (d : RDT) (n e : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → Iop.Tr (uLT (_root_.Run.ckP .two) [d]) → W → W) :
    Piece (_root_.Run.ckP .two) Fr₂ (P₂ × St₂) Cl W :=
  ⟨Block.lift Prod.snd (fun t s => (t.1, s)) (below b), base, [d], [], ext, (vecMaps d n).err ((e,
      ()) : Nat × Unit)⟩

/-- **ROW 2.7, THE CHANCE's HALF, AT THE SEAT**: a block whose yes is linZeta, as the maker holds
it, at one written round that draws
kRow elements and no position, in the library's field, at the written count that bears e ≥ kRow |K|
^ (kRow - 1). -/
theorem zeta_half₂_seat (b7 : Block St₂ Cl) (hb : ∀ d rs gs d', b7.decide d rs gs = .ok d' → linZeta
    d rs = some d')
    (base : Nat) (d : RDT) {ns a' : Nat} (hd : OnBytes.Slice.SendsDraws (toRD d) ns S.kRow 0 a') (e
        : Nat)
    (he : S.kRow * Fintype.card OnBytes.Slice.GE ^ (S.kRow - 1) ≤ e)
    (ext : (P₂ × St₂) × Fr₂.E.Str → Iop.Tr (uLT (_root_.Run.ckP .two) [d]) → W → W)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base)
    (hpins : ∀ x, on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 7 x → ∀ z,
      PinsStay G₂ at_ (pinned (open₂ 8)) (x.1.1, x.1.2) (x.1.1, { x.1.2 with loc := { x.1.2.loc with
          zFd := z } })) :
    (zetaSeat Fr₂ b7 base d S.kRow e ext).ior.red.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll
        last₁ off₂ 7)
      (fun x x' => L₂ F Fr₂ G₂ at_ S K₁ R enc rad 8 x' → L₂ F Fr₂ G₂ at_ S K₁ R enc rad 7 x)
      (zetaSeat Fr₂ b7 base d S.kRow e ext).err := by
  refine zeta_half₂_at F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ OnBytes.Model.Reading.gl b7 hb
    (zetaSeat Fr₂ b7 base d S.kRow e ext) rfl hsame hbase hpins e he
    (fun _ => (vecMaps d S.kRow).carry) (fun _ => (vecMaps d S.kRow).fits (vecMaps_ok hd) _) ?_
  intro x τ x' _ hout
  have ht := piece_tests _ x τ x' hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (vecMaps d S.kRow).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
  have hdec := piece_decides_at _ x τ x' hout
  obtain ⟨m, c, ⟨⟩⟩ := τ
  obtain ⟨-, e2⟩ := hz_held b7 hb _ _ _ _ hdec
  have e3 : x'.1.2 = { x.1.2 with loc := { x.1.2.loc with zFd := _root_.Desc.K14.drawn (noDigest
      (shownAt d m c)) } } :=
    linZeta_inv _ _ (noDigest (shownAt d m c)) e2
  refine ⟨OnBytes.Slice.gVec S.kRow _ (OnBytes.Slice.valsOf (toRD d) c), (vecMaps d
      S.kRow).tr_of_pass (m, c, ()) hp, ?_⟩
  rw [e3]
  exact drawn_shown hd m c

/-- hb at K14's own seventh block, and at whatever block has its decide (as a description seats it:
retyped, its claims bared). -/
theorem zeta_hb (Q : _root_.Desc.K14.P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit)
    (hbl : _root_.Desc.K14.blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St₂ Cl) (hd
        : b.decide = b7.decide) :
    ∀ d rs gs d', b.decide d rs gs = .ok d' → linZeta d rs = some d' := fun d rs gs d' h =>
  zeta_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl d rs gs d' (hd ▸ h)

end

end Johnson.RunOne.KeyRows23
