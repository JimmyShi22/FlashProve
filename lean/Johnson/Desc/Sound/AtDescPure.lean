-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/AtDescPure.lean: the carrying one storey up, its second half: the value that the proof file's description's maker returns (onlineDescription, Johnson/Desc/ProofFile/OnlineDescription.lean) is the term of Johnson/Desc/Sound/AtSeat.lean at some letters; so what is said at that term at all letters is said of the value. Three definitions, eight theorems. (descPure_is calls the opening of the maker IM.seat_open, Johnson/IMR/SeatOpen.lean · descPure_elim hands on the whole record IM.Open of that file: with the first chain a free letter it would hand on less than is held, and a sentence on the value's run is false at an arbitrary chain).
secondAt IS A NAME: it is P2Third.secondSeatOf Z N; second_is ties it to onlineLastChain Z. No conclusion here ends at secondAt: descPure_term | descPure_elim hand it to a PROOF; what is said of the value ends at F₀, and
descPure_is ends at onlineLastChain Z = some B.
THE WALK THROUGH THE MAKER's TEXT IS ANOTHER FILE's: IM.seat_open (Johnson/IMR/SeatOpen.lean): onlineDescription … = .ok F → Open … (the public part · the seat's tables · no fault · nothing lacking · the base blocks · the chain · both later seats as LETTERS with their equations · F = fileDescBy …). IT IS
CALLED HERE, NOT TYPED ANEW. WHAT IS ADDED: the shared chain's seat AS A TERM (so that S₂ is St by rfl), the last chain's by name, the rule descPure_elim. The maker's own files have the like (descPure_parts, Johnson/Desc/ProofFile/Law/PureMade.lean).

  p14_shape: the seat's parameters read the plan's shape at ch.made.sized.proof.batch.shape: rfl.
  descPure_is: onlineDescription o pol lay KL = .ok F₀ → there are Z, N, B, c with: the plain road's public part of the three files is Z · the places' numbers of Z's made plan are N · the last chain's seat at Z is B · F₀ = descAt … : the frame at the shared chain's seat (Desc.K14.sharedSeatOf, Johnson/Desc/ProofFile/Lot/K14Seat.lean) at Z's own planner's chains.
  secondAt Z N · second_is: the last chain's seat BY NAME (P2Third.secondSeatOf Z N; second_is: where the places' numbers of Z's made plan are N, onlineLastChain Z = some (secondAt Z N)) · descPure_term: so F₀ = descZ o Z N (secondAt Z N) c: THE FIRST CHAIN c ALONE STAYS A LETTER · states_at: at that term S₁ | S₂ | S₃ ARE the
    first table's record, the shared chain's St, the last chain's S₃: rfl.
  seatZ · descPure_open: onlineDescription … = .ok F₀ → ∃ Z Bs base c N, ‹the places' equation› ∧ IM.Open o pol lay KL F₀ Z Bs base c (seatZ Z N) (secondAt Z N): IM.Open's NINE FIELDS, WITH BOTH LATER SEATS AS TERMS.
  descPure_elim: **THE CARRYING, AS ONE RULE: what holds of the term at all Z, Bs, base, c, N WITH THAT WHOLE OPENING IN HAND (chainBy Z base ‹frames› ‹road› = .ok c among it) holds of the maker's value.**
  hd_at_descPure: **OF THE VALUE: it IS the term descZ o Z N B c at some Z, N, B, c, AND at that term's own start₂ the first table's decoder decShared (decK at start₂ of the public part) is (kcReq numsFull pp E).conf.D at every instance's record.** The equation F₀ = … stands IN the conclusion: a form "there is a decoder with
    that equation" would be met by any decoder that is made of conf.D itself, and would say nothing of decK. Under the one test on the plan, asked at the public part Z that the road makes of the three files.
HOW IT IS MEANT TO BE USED: an end theorem whose conclusion is a sentence on F₀ (its run, its data) is proved by descPure_elim (or begins with "obtain ⟨Z, N, c, hZ, hN, rfl⟩ := descPure_term … h"): from there on every letter is chosen at the term, where the second state's type is St by rfl (s2_at), and AtSeat.lean's theorems apply as they stand.

Limits. Texts' equations. No law of a block. That onlineDescription returns a value anywhere is a run's word. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.AtSeat
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Desc.Plain
open VerifiableInference.Desc (Block Chain FileDescription Strs Wit)
open VerifiableInference.Desc.Sound (CellsOf strsOf frameAt)
open VerifiableInference.OnPublicFiles (kcReq)

/-- The term at the public part Z: the frame at the shared chain's seat (Desc.K14.sharedSeatOf) at Z's own planner's chains. -/
abbrev descZ (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B : ProofFile.SecondSeat)
    (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl) : FileDescription ProofFile.Inst :=
  descAt o ProofFile.pureRoad.links Z Z.p.chains (beforePointOf N)
    (fun _ => VerifiableInference.Desc.K12.Seat.tests N) [] VerifiableInference.Desc.K12.Seat.last
    (VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains) B (fun s => s) (ProofFile.startS Z) c

/-- **The last chain's seat at Z, by name**: THE NAME THAT THE LAST CHAIN's OWN FILES GIVE IT (P2Third.secondSeatOf, Johnson/Desc/ProofFile/Lot/LastChain.lean). -/
def secondAt (Z : ProofFile.Pub) (N : H2U.Places4) : ProofFile.SecondSeat := P2Third.secondSeatOf Z N

/-- It is what the last chain's own text (P2Third.secondSeat) returns. -/
theorem second_is (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N) :
    ProofFile.onlineLastChain Z = some (secondAt Z N) := by
  show P2Third.secondSeat Z = _
  unfold P2Third.secondSeat
  rw [hN]
  rfl

/-- The seat's parameters read the plan's shape at one path, whatever messages are named in front of the point. -/
theorem p14_shape (ch : OnBytes.Model.Verify.Chains) (bp : List (Nat × Nat)) :
    (p14Of ch bp).par.S = ch.made.sized.proof.batch.shape := rfl

/-- **The maker's value is the term**: the opening of the maker (IM.seat_open, Johnson/IMR/SeatOpen.lean), with the shared chain's seat read off its own files' text. -/
theorem descPure_is (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F₀ : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F₀) :
    ∃ Z N B c, ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineLastChain Z = some B ∧ F₀ = descZ o Z N B c := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open h
  have hA' : Desc.K14.sharedSeatAt Z = some A := O.shared
  unfold Desc.K14.sharedSeatAt at hA'
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at hA'
    cases hA'
  | ok N =>
    rw [hN] at hA'
    obtain rfl := Option.some.inj hA'
    exact ⟨Z, N, B, c, O.pub, hN, O.second, O.desc⟩

/-- **The maker's value is the term, with both later seats by name**: the first chain alone stays a letter. -/
theorem descPure_term (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F₀ : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F₀) :
    ∃ Z N c, ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F₀ = descZ o Z N (secondAt Z N) c := by
  obtain ⟨Z, N, B, c, hZ, hN, hB, hF⟩ := descPure_is o pol lay KL F₀ h
  obtain rfl := Option.some.inj (hB.symm.trans (second_is Z N hN))
  exact ⟨Z, N, c, hZ, hN, hF⟩

/-- The three states' types at that term: the first table's record · the shared chain's state · the last chain's state: by rfl. -/
theorem states_at (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl) :
    (descZ o Z N (secondAt Z N) c).S₁ = VerifiableInference.Desc.First.S ∧
      (descZ o Z N (secondAt Z N) c).S₂ = St ∧
      (descZ o Z N (secondAt Z N) c).S₃ = VerifiableInference.Desc.Third.S₃ := ⟨rfl, rfl, rfl⟩

/-- The shared chain's seat sharedSeatOf at Z and the places' numbers N: the term inside descZ. -/
abbrev seatZ (Z : ProofFile.Pub) (N : H2U.Places4) : ProofFile.SharedSeat :=
  Desc.K14.sharedSeatOf Z.p.chains (beforePointOf N) (fun _ => VerifiableInference.Desc.K12.Seat.tests N) []
    VerifiableInference.Desc.K12.Seat.last (VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains)

/-- **The maker's value, opened, with both later seats as terms**: the WHOLE record IM.Open (Johnson/IMR/SeatOpen.lean) is handed on: the public part · the seat's tables · no fault · nothing lacking · the base blocks · HOW THE FIRST CHAIN c IS MADE · the description's equation. -/
theorem descPure_open (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F₀ : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F₀) :
    ∃ Z Bs base c N, H2U.placesOfMade Z.made = .ok N ∧
      IM.Open o pol lay KL F₀ Z Bs base c (seatZ Z N) (secondAt Z N) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open h
  have hA' : Desc.K14.sharedSeatAt Z = some A := O.shared
  unfold Desc.K14.sharedSeatAt at hA'
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at hA'
    cases hA'
  | ok N =>
    rw [hN] at hA'
    obtain rfl := Option.some.inj hA'
    obtain rfl := Option.some.inj (O.second.symm.trans (second_is Z N hN))
    exact ⟨Z, Bs, base, c, N, hN, O⟩

/-- **THE CARRYING, AS ONE RULE**: what holds of the term at all its letters, WITH THE WHOLE OPENING IN HAND (so also how its first chain is made), holds of the maker's value. -/
theorem descPure_elim (motive : FileDescription ProofFile.Inst → Prop) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (F₀ : FileDescription ProofFile.Inst) (h : ProofFile.onlineDescription o pol lay KL = .ok F₀)
    (H : ∀ Z Bs base c N, H2U.placesOfMade Z.made = .ok N →
      IM.Open o pol lay KL (descZ o Z N (secondAt Z N) c) Z Bs base c (seatZ Z N) (secondAt Z N) →
      motive (descZ o Z N (secondAt Z N) c)) : motive F₀ := by
  obtain ⟨Z, Bs, base, c, N, hN, O⟩ := descPure_open o pol lay KL F₀ h
  have e : F₀ = descZ o Z N (secondAt Z N) c := O.desc
  subst e
  exact H Z Bs base c N hN O

/-- **Of the value**: it is the term, and at the term's own start₂ the first table's decoder decShared is conf.D at every instance's record. -/
theorem hd_at_descPure (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F₀ : FileDescription ProofFile.Inst)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F₀)
    (hS : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z →
      fullShapeB Z.p.chains.made.sized.proof.batch.shape = true)
    (err : Nat) (pp : Inst.Model.ScalesAndPolicy) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B : ProofFile.SecondSeat) (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl)
      (hs : fullShapeB (p14Of Z.p.chains (beforePointOf N)).par.S = true),
      F₀ = descZ o Z N B c ∧
      ∀ (z : (kcReq numsFull pp E).conf.X × (kcReq numsFull pp E).conf.Rec) (DP : WholeD) (all : List LeftT)
        (key : ℕ → ℕ) (ft : ℕ) (y : (frameAt (DP.at frS.P.T.a) all key ft).E.Str)
        (s : VerifiableInference.Desc.First.S),
        decShared (p14Of Z.p.chains (beforePointOf N)).par err 2852142980
            (rankLib (p14Of Z.p.chains (beforePointOf N)).par.S.fold)
            (heldFull (p14Of Z.p.chains (beforePointOf N)).par err
              (p14Of Z.p.chains (beforePointOf N)).par.S.fold.index.saltBytes
              (full_index (p14Of Z.p.chains (beforePointOf N)).par.S hs) numsFull pp E)
            (descZ o Z N B c).start₂
            (strsOf (frameAt (DP.at frS.P.T.a) all key ft) y).cell
            (((descZ o Z N B c).pull LPFD.Full.instanceAsPlainRecord).pub z, s) =
          (kcReq numsFull pp E).conf.D y.1 z.2 := by
  obtain ⟨Z, N, B, c, hZ, _, _, hF⟩ := descPure_is o pol lay KL F₀ h
  exact ⟨Z, N, B, c, hS Z hZ, hF, fun z DP all key ft y s =>
    hd_at_seat o ProofFile.pureRoad.links Z Z.p.chains (beforePointOf N) _ [] _ _ B (fun s => s) (ProofFile.startS Z) c err
      (hS Z hZ) pp E z DP all key ft y s⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.p14_shape
#print axioms Desc.K14.Law.descPure_is
#print axioms Desc.K14.Law.second_is
#print axioms Desc.K14.Law.descPure_term
#print axioms Desc.K14.Law.states_at
#print axioms Desc.K14.Law.descPure_open
#print axioms Desc.K14.Law.descPure_elim
#print axioms Desc.K14.Law.hd_at_descPure
