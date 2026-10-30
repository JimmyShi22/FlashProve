-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.Road
import Johnson.Desc.Sound.TiedAtErr
import Johnson.Desc.K13.Law.DeclaredOfWritten
import Johnson.Desc.K13.Law.AtTable
import Johnson.Goal.Numbers.K13CapAt
/-
K13's SHARE OF THE CHAIN OF PROMISES' FIELD AT PIECES THAT CARRY THE CAP (Iop.Err.cap 128): the family of errors that the rule of composition's
caller lays at every piece. K13's files' tie at the table (k13_tied_seat, Johnson/Desc/K13/Law/AtTable.lean) stands at the kind's OWN errors; it reaches the description's piece
by «a tie goes up in the errors» (tiedAt_err, Johnson/Desc/Sound/TiedAtErr.lean) and «the kind's own errors are at most the cap».
  capB P            three comparisons with code, on the rows' number and the three entries' work (roundB, Johnson/Goal/Numbers/K14RoundsAt.lean).
  capB_real · capB_no   they hold at 13 rows and no work; they fail at 2 ^ 70 rows.
  err_le_cap        Declared · KindsM3 · capB P = true → the kind's own errors are at most the cap (maps_below_pow, K13CapAt.lean).
  HasM3Cap          the description's piece has the law's piece's letters, WITH THE CAP AS ITS ERRORS.
  hasM3Cap_of_cut   at the maker's row, where the family of rests lays the cap at the block's number.
  k13_law_cap       KindTied … K13 at such a piece.
NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)

open _root_.Desc.K14.Law (roundsIn cutRow_at roundB)
open _root_.Iop (Err)

/-- The three comparisons. -/
def capB (P : Where) : Bool :=
  roundB (sigmaEntry P) .elems (P.rows - 1) 128 && roundB (epsEntry P) .join 1 128 &&
    roundB (roundEntry P) .elems 2 128

/-- **The comparisons can be met**: at thirteen rows and no work, the numbers of a proof file at the
full size. -/
theorem capB_real (P : Where) (h1 : P.rows = 13) (h2 : P.work = (0, 0, 0)) : capB P = true := by
  unfold capB sigmaEntry epsEntry roundEntry
  rw [h1, h2]
  decide +kernel

/-- And they can say no: at 2 ^ 70 rows. -/
theorem capB_no (P : Where) (h1 : P.rows = 2 ^ 70) (h2 : P.work = (0, 0, 0)) : capB P = false := by
  unfold capB sigmaEntry epsEntry roundEntry
  rw [h1, h2]
  decide +kernel

/-- **The kind's own errors are at most the cap.** -/
theorem err_le_cap (P : Where) (dZ d0 : RDT) (ds : List RDT) (hD : Declared P dZ d0 ds)
    (hK : KindsM3 dZ d0 ds) (hB : capB P = true) :
    Err.le ((mapsOf dZ d0 ds).err (errK P.rows ds.length))
      (Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds))) := by
  unfold capB at hB
  simp only [Bool.and_eq_true] at hB
  obtain ⟨⟨h1, h2⟩, h3⟩ := hB
  exact Err.le_cap_of_below_inv 128 _ (maps_below_pow P dZ d0 ds hD 128
    (by rw [hD.sigma.1, hK.1]; exact h1) (by rw [hD.eps.1, hK.2.1]; exact h2)
    fun d hd => by rw [(hD.vars d hd).1, hK.2.2 d hd]; exact h3)

/-- The law's piece at a block c, with the cap as its errors. -/
noncomputable def pieceM3Cap {W : Type} (Fr : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (c : Block S Cl) : Piece (ckP .two) Fr S Cl W :=
  { (pieceM3 (Cl := Cl) (W := W) Fr P base dZ d0 ds).seat c with
    err := Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds)) }

/-- The piece q (over the public part and the chain's state) has these letters. -/
def HasM3Cap {Pp W : Type} (Fr : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (q : Piece (ckP .two) Fr (Pp × S) Cl W) : Prop :=
  ∀ c : Block S Cl, (⟨c, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Piece (ckP .two) Fr S Cl W) = pieceM3Cap Fr P base dZ d0 ds c

theorem hasM3Cap_pieceOf {Pp W : Type} {Fr : Frame} (P : Where) (base : ℕ) (dZ d0 : RDT)
    (ds : List RDT) (x : Block (Pp × S) Cl) (Rs : Rest (ckP .two) Fr (Pp × S) W (dZ :: d0 :: ds))
    (he : Rs.err = Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds))) :
    HasM3Cap Fr P base dZ d0 ds (pieceOf x base (dZ :: d0 :: ds) [] Rs) := by
  intro c
  show (⟨c, base, dZ :: d0 :: ds, [], fun _ _ w => w, Rs.err⟩ : Piece (ckP .two) Fr S Cl W) =
    ⟨c, base, dZ :: d0 :: ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds))⟩
  rw [he]

/-- **At the maker's row.** -/
theorem hasM3Cap_of_cut {Pp W : Type} {Fr : Frame}
    (rest : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) Fr (Pp × S) W ds) (putBack : List Fmt.RoundView)
    (l : List (Block (Pp × S) Cl)) (b : Block (Pp × S) Cl) (all : List RDT) (k : ℕ)
    (x : Block (Pp × S) Cl) (hx : (b :: l)[k]? = some x) (hlen : k < l.length)
    (P : Where) (dZ d0 : RDT) (ds : List RDT)
    (hds : (all.drop (roundsIn ((b :: l).take k))).take x.rounds.length = dZ :: d0 :: ds)
    (herr : (rest k (dZ :: d0 :: ds)).err = Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds)))
    (q : Piece (ckP .two) Fr (Pp × S) Cl W)
    (hq : ((cutRow rest putBack 0 0 all b l).1 :: (cutRow rest putBack 0 0 all b l).2)[k]? =
      some q) :
    HasM3Cap Fr P (nTrees (all.take (roundsIn ((b :: l).take k)))) dZ d0 ds q := by
  obtain ⟨q', h0, _, h2, h3, _, h5⟩ := cutRow_at rest putBack l b 0 0 all k x hx hlen
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans h0)
  rw [h5, h2, h3.trans hds, Nat.zero_add, Nat.zero_add]
  exact hasM3Cap_pieceOf P _ dZ d0 ds x _ herr

/-- **K13's share, at a piece that carries the cap.** -/
theorem k13_law_cap {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt (ckP .two) D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E 355 a b w = w)
    {nR : ℕ} (base : ℕ) (dZ d0 : RDT) (ds : List RDT) (hD : Declared (K13.whereOf Z) dZ d0 ds)
    (hle : Err.le ((mapsOf dZ d0 ds).err (errK (K13.whereOf Z).rows ds.length))
      (Err.cap 128 (uLT (ckP .two) (dZ :: d0 :: ds))))
    (rw : ProofFile.InstPub × S → W → Wit GE nR (K13.whereOf Z).lin.kCol)
    (hRow : RowM3 N Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true) 355)
    (hF : FillM3 Cl (K13.whereOf Z) N Mg rw
      ((First.pubSets Mg.more Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD []))
    (hbase : N.index.1 < base)
    (hQ : ∀ q, (T.p₁ :: T.l₁)[355]? = some q →
      HasM3Cap (frameAt D all D.key₁ T.ft₁) (K13.whereOf Z) base dZ d0 ds q) :
    KindTied N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true) E (T.p₁ :: T.l₁)
      KindName.K13 := by
  intro i q a hq ha hk
  obtain ⟨rfl, -⟩ := k13_places_full i a ha hk
  obtain ⟨⟨e, hflat, _, hu⟩, _⟩ := k13_sits_flat hS hR O
  exact tiedAt_of_seatTie hT hflat hq Sound.linksFull _ N Mg (E 355) hE
    (fun c' => pieceM3Cap _ (K13.whereOf Z) base dZ d0 ds c') (hQ q hq)
    fun z => tiedAt_err N Mg Sound.linksFull _ _ 355
      ((pieceM3 (Cl := Cl) (W := W) _ (K13.whereOf Z) base dZ d0 ds).seat (below e)) _ hle
      (k13_tied_seat _ (K13.whereOf Z) base dZ d0 ds hD _ (below_underR hu) z N Mg Sound.linksFull _
        355 rw hRow hF hbase)

end VerifiableInference.Desc.K13.Law
