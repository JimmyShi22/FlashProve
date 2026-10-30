-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/AtSeat.lean: THE CARRYING ONE STOREY UP, ITS FIRST HALF: THE RULES ON "ONE DECODER", WHICH ARE TYPED AT THE SHARED CHAIN's STATE St, SPEAK AT THE PROOF FILE's DESCRIPTION's OWN TERM: the frame fileDescBy (Johnson/Desc/ProofFile/Frames1.lean) at the shared chain's seat sharedSeatOf (Johnson/Desc/ProofFile/Lot/K14Seat.lean), pulled
along the seated map from (request, record) to instances, instanceAsPlainRecord (Johnson/Desc/Laid/ProofFull.lean). One abbreviation, six theorems (three of them equations by rfl).

  descAt …: the term.
  s2_at: its second state's type IS St · pub_at: its public part's type IS InstPub · start2_at: its start₂ IS fun q => first codes q.key: ALL THREE BY rfl. (That this state's key is the public part's is then rfl too: other files have that sentence by name; here it is spent inline.)
  hd_at_seat: **AT THE TERM, AT EVERY INSTANCE z = (request, record) OF THE TOP STATEMENTS: the first table's decoder decShared, at the term's own start₂, at the oracles' reader, at the public part that the pulled description makes of z, IS (kcReq numsFull pp E).conf.D AT z's RECORD.** Its premises on the key are PAID here: eKey by
    the seated map's own law (instOf_key), hkey by rfl. Left: the one test on the plan (fullShapeB at the seat's own parameters).
  tp_at_seat, pw_at_seat: **(TP) and (PW), to the letter of TieEnd.lean, AT THE PULLED TERM's OWN
    TYPES AND start₂**, at every b; get := (the public part, getS of the first state). UNDER TWO
    PREMISES EACH: hM (Mg₁.decodes | Mg₁.pinW is made of decShared at the term's start₂) and hP
    (Pm.tablePromise | Mg.pinT is made of decK).
WHAT IT IS NOT: a sentence at the VALUE that the description's maker returns (onlineDescription): that value is this term at some letters by the maker's text: a theorem of other files, to be called in front. c (the first chain), B (the last chain's seat), mk, Z, the planner's chains and the seat's other letters stay letters.

Limits. Equations of texts, and two rules called at a term. No law of a block. The full size alone. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.OneByMake
import Johnson.Desc.Sound.PlanAsk
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.ProofFile.Lot.K14Seat
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Desc.Plain
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Strs Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.Sound (CellsOf decodesOf pinWOf MsgT strsOf strsOfAct frameAt EAll ThreeAt actQ tiedNumbers)
open VerifiableInference.OnPublicFiles (kcReq)

section Seat
variable {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (ch : OnBytes.Model.Verify.Chains)
  (bp : List (Nat × Nat)) (tests : P14 → List (Block St Unit)) (standIns : List String)
  (last : List (Block St Unit) → Block St Unit) (fok : Bool) (B : ProofFile.SecondSeat)
  (getS : σ → VerifiableInference.Desc.First.S) (start : ProofFile.InstPub → σ) (c : Chain σ ProofFile.Cl)

/-- **The proof file's description's own term**, at the shared chain's seat. -/
abbrev descAt : FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy o mk Z (Desc.K14.sharedSeatOf ch bp tests standIns last fok) B getS start c

/-- Its second state's type is the shared chain's state. -/
theorem s2_at : (descAt o mk Z ch bp tests standIns last fok B getS start c).S₂ = St := rfl

/-- Its public part's type is the instance without the asked reply. -/
theorem pub_at : (descAt o mk Z ch bp tests standIns last fok B getS start c).XiPub = ProofFile.InstPub := rfl

/-- Its start₂ lays the public part's key into the first state. -/
theorem start2_at (q : ProofFile.InstPub) :
    (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ q = first (p14Of ch bp).codes q.key := rfl

/-- **At the term, at every instance of the top statements, the first table's decoder is conf.D at the instance's record.** -/
theorem hd_at_seat {S : Type} (err : Nat) (h : fullShapeB (p14Of ch bp).par.S = true) (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (z : (kcReq numsFull pp E).conf.X × (kcReq numsFull pp E).conf.Rec) (DP : WholeD) (all : List LeftT)
    (key : ℕ → ℕ) (ft : ℕ) (y : (frameAt (DP.at frS.P.T.a) all key ft).E.Str) (s : S) :
    decShared (p14Of ch bp).par err 2852142980 (rankLib (p14Of ch bp).par.S.fold)
        (heldFull (p14Of ch bp).par err (p14Of ch bp).par.S.fold.index.saltBytes
          (full_index (p14Of ch bp).par.S h) numsFull pp E)
        (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂
        (strsOf (frameAt (DP.at frS.P.T.a) all key ft) y).cell
        (((descAt o mk Z ch bp tests standIns last fok B getS start c).pull LPFD.Full.instanceAsPlainRecord).pub z, s) =
      (kcReq numsFull pp E).conf.D y.1 z.2 :=
  shared_at_oracles (p14Of ch bp).par err _ (full_index (p14Of ch bp).par.S h) numsFull pp E
    (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ (fun q : ProofFile.InstPub => q.key)
    (fun _ => rfl) _ z.2 (LPFD.Full.instOf_key z) DP all key ft y s

variable {Cells : Type} (p : Par) (err₂ eM : Nat)
  (rank : ((Fin p.S.fold.index.v → Bool) →
    Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
  (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)

/-- **(TP) at the pulled term's own types and start₂.** -/
theorem tp_at_seat {Xi' X₁ X₂ W : Type} (instP : Xi' → ProofFile.Inst) (C : CK) (D : WholeD) (all : List LeftT)
    (T : ThreeAt C D all ((descAt o mk Z ch bp tests standIns last fok B getS start c).pull instP) X₁ X₂ W)
    (N₁ : Numbers) (Mg₁ : Meaning ProofFile.InstPub W) (Ns : NumbersS) (Pm : PromMeaning St)
    (hM : Mg₁.decodes = decodesOf (decShared p err₂ eM rank held
      (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂))
    (hP : Pm.tablePromise = decodesOf (decK p err₂ eM rank held)) :
    ∀ b : (ProofFile.InstPub × σ) × (EAll D all).Str,
      Mg₁.decodes (b.1.1, getS b.1.2) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise ((descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ b.1.1)
        (strsOfAct (frameAt D all D.key₂ T.ft₂)
          ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2
            ((b.1, (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ b.1.1), b.2))) :=
  tp_by_make p err₂ eM rank held C D all Xi' ProofFile.InstPub σ B.σ X₁ X₂ ProofFile.Cl W
    (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ T
    (fun a => (a.1, getS a.2)) (fun _ => rfl) N₁ Mg₁ Ns Pm hM hP

/-- **(PW) at the pulled term's own types and start₂.** -/
theorem pw_at_seat {Xi' X₁ X₂ Tok : Type} (instP : Xi' → ProofFile.Inst) (C : CK) (D : WholeD) (all : List LeftT)
    (T : ThreeAt C D all ((descAt o mk Z ch bp tests standIns last fok B getS start c).pull instP) X₁ X₂
      (Wit Cells Tok MsgT))
    (N₁ : Numbers) (Mg₁ : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)) (Ns : NumbersS)
    (Mg : MeaningS St (ProofFile.InstPub × σ) (Wit Cells Tok MsgT))
    (hM : Mg₁.pinW = pinWOf (decShared p err₂ eM rank held
      (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂))
    (hP : Mg.pinT = pinWOf (decK p err₂ eM rank held)) :
    ∀ (b : (ProofFile.InstPub × σ) × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      Mg.pinT ((descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ b.1.1)
        (strsOfAct (frameAt D all D.key₂ T.ft₂)
          ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2
            ((b.1, (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ b.1.1), b.2))) w →
      Mg₁.pinW (b.1.1, getS b.1.2) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w :=
  pw_by_make p err₂ eM rank held C D all Xi' ProofFile.InstPub σ B.σ X₁ X₂ ProofFile.Cl
    (descAt o mk Z ch bp tests standIns last fok B getS start c).start₂ T
    (fun a => (a.1, getS a.2)) (fun _ => rfl) N₁ Mg₁ Ns Mg hM hP

end Seat

end Desc.K14.Law

#print axioms Desc.K14.Law.s2_at
#print axioms Desc.K14.Law.start2_at
#print axioms Desc.K14.Law.hd_at_seat
#print axioms Desc.K14.Law.tp_at_seat
#print axioms Desc.K14.Law.pw_at_seat
