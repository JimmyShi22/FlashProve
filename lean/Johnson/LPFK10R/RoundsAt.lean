-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/RoundsAt.lean: THE SEATED BLOCK OF K10 DECLARES JUST THE FORMAT's ROUNDS OF WHICH K10's LAW SPEAKS: "BAT" at the lot's rows, "FOLD epsilon", and the lot's k times "FOLD round". Statements and proofs.
WHY. K10's law is typed at a piece pieceOn b base dB dE dR k .. whose rounds' data are letters, under iB | iE | iR : IsRd (toRD d) (rBatN n | rEps na | rTwo nb). By reading: where these data are not the
block's declared rounds the piece refuses everything and the law holds for nothing: 25 fillings are owed.
  seated_rounds     b LaidAlone .. (K9.closing Q).retype ..: b.rounds are the kind's at Q (alone_rounds; the rest by the make).
  seated_written    so, where Q has no proof of work: WrittenAs e b.rounds (roundsOf Q.rows Q.k) (Johnson/Desc/First/Close/Law/RoundsOfPar.lean: kind_written; WrittenAs: Johnson/Desc/Sound/Tiles.lean: the premise from which the
                    road makes a chain's data of its declared rounds).
  seated_len        the piece of the law at k := Q.k has as many rounds as the block declares: the first half of Piece.Owed (Johnson/Desc/Sound/ChainRule.lean).
  k10_rounds_sit    in scope: at EVERY block b of c.blocksInOrder whose place is of the kind K10: l < 25, p, Q as in k10_sits_each, and: IF Q.workField = 0 and Q.workClose = 0: WrittenAs e b.rounds (roundsOf Q.rows Q.k), for every e.
SO A FILLING IS: n := Q.rows · na := "FOLD epsilon" · nb := "FOLD round" · k := Q.k, and dB | dE | dR := the data that the road makes of rBatN Q.rows | rEps .. | rTwo ...
THE NUMBERS, BY A RUN (ParGuard.lean, a file that is not in this library; no theorem): at the full size's shipped public files: at all 25 links both works are 0 and (rows, k) = (6, 8) at l = 0 · (3295, 7) at l odd · (1324, 8) at l = 2 .. 22 · (1322, 8) at l = 24.
LIMITS. (1) THE LAST STEP IS NOT TYPED: that the data which the road makes of these written rounds satisfy iB | iE | iR, and that the description's own piece at the block (the table's cut) IS pieceOn b .. at these data: the first is
the road's text, the second other files' tiling. (2) "No proof of work" is a premise on two numbers of Q: true by a run at one set of public files. (3) n := Q.rows asks a typed batching of just so many rows (num : R.G.Row B ≃ Fin n): that
the typed group with its B has so many is not shown. (4) The second half of Piece.Owed (the leaves read are the leaves opened: both none here) is not typed. (5) At secondHashFunction, in scope, the first chain, the full size. Nothing on soundness.

-/
import Johnson.LPFK10R.SitsAll
import Johnson.Desc.First.Close.Law.RoundsOfPar

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par kind roundsOf kind_written kind_rounds_length pieceOn)
open VerifiableInference.Desc.Sound (WrittenAs)
open VerifiableInference.OnPublicFiles
open ProofFile (Cl)
open IM

/-- The seated block's declared rounds are the kind's at the lot's numbers. -/
theorem seated_rounds {same : S → S → Bool} {b : Block S Cl} {Q : Par} {name : String} {a : Place}
    (h : LaidAlone same b (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype name a) :
    b.rounds = (kind (Cl := Unit) Q).rounds := alone_rounds h

/-- **They are the format's own rounds**, where the place has no proof of work. -/
theorem seated_written {same : S → S → Bool} {b : Block S Cl} {Q : Par} {name : String} {a : Place}
    (h : LaidAlone same b (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype name a)
    (e : List (List ByteArray × ByteArray)) (h1 : Q.workField = 0) (h2 : Q.workClose = 0) :
    WrittenAs e b.rounds (roundsOf Q.rows Q.k) := by
  rw [seated_rounds h]
  exact kind_written Q e h1 h2

/-- The law's piece at k := the lot's k has as many rounds as the block declares. -/
theorem seated_len {same : S → S → Bool} {b : Block S Cl} {Q : Par} {name : String} {a : Place}
    (h : LaidAlone same b (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype name a)
    {W : Type} {F : VerifiableInference.Desc.Sound.Frame} (base : ℕ) (dB dE dR : OnBytes.Maker.RDT)
    (ext) (err) :
    (pieceOn (W := W) (F := F) b base dB dE dR Q.k ext err).ds.length +
        (pieceOn (W := W) (F := F) b base dB dE dR Q.k ext err).back.length =
      (pieceOn (W := W) (F := F) b base dB dE dR Q.k ext err).b.rounds.length := by
  show (dB :: dE :: List.replicate Q.k dR).length + ([] : List Fmt.RoundView).length = b.rounds.length
  rw [seated_rounds h, kind_rounds_length]
  simp only [List.length_cons, List.length_replicate, List.length_nil]
  omega

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At every seated block of K10.** -/
theorem k10_rounds_sit (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l, l < 25 ∧ ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
        c.blocksInOrder[ixK10 l]? = some b ∧ b.rounds = (kind (Cl := Unit) Q).rounds ∧
        (Q.workField = 0 → Q.workClose = 0 →
          ∀ e, WrittenAs e b.rounds (roundsOf Q.rows Q.k)) := by
  intro b hb hk
  obtain ⟨l, hl, Lk, p, Q, -, h2, h3, -, h5, h6⟩ := k10_sits_each hS hR O b hb hk
  exact ⟨l, hl, p, Q, h2, h3, h5, seated_rounds h6, fun h1 h2' e => seated_written h6 e h1 h2'⟩

end LPFK10

#print axioms LPFK10.seated_rounds
#print axioms LPFK10.seated_written
#print axioms LPFK10.seated_len
#print axioms LPFK10.k10_rounds_sit
