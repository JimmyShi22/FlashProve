-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesFive.lean: the five statements at the key file's test
on the ranges, member 15 of the first chain's thread, at the key file's prover with the four tests
laid and the table of trees tbRng: PlaysS, BehindS, ExchangeS, RidesPastS and AcceptedS, at every
letter Said and every letter for a fall.

  Five           the five statements at a thread's member
  five_of_tb     they hold at any list of halves that finds the test's half and any table of trees
                 with TbIsSent and the test's tables behind the trees 2, 3, 4
  five_at_side   so at the table tbRng: at any list of halves in which a search by the test's place finds the
                 test's half, from the rows' truth at the sender's rows
  five_rng       so at the key file's prover with the four tests laid
  five_of_wit    the same from the tie on the letter L (WitIsJob, E2E/KeyRangesGrows.lean): the rows'
                 truth is then taken off the thread's own open sentence

What is left, by whom.
  On the parts: Kp.AtPlaces: the other halves of the first chain bear their places.
  On the letter L: kind₁ at 15 lies between RngYes and RngKept; SmOnly, the numbers of the plan, the
  seats, sameness.
  On the rows: RowsTrueOf at the sender's rows, at every stand of the pair, or WitIsJob there: L's
  witness reads as the job's words; either is asked by AcceptedS alone (RangesSent.lean says what
  it binds). By WitIsJob the content moves to the thread's own sentence at the border 15, which the
  sub-protocols 0 to 14 owe.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: all five have the pair ThrS as a premise.
- The five at one member: nothing is said of the thread's standing at this border.
- In scope; at the written sizes.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesSent
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesRides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces ArrOk)
open OnBytes.Slice (GF readE)
open Johnson.Prover.Send (shapeAt)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23 (atSix)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyTest (sMsg)
open AtPublicFiles.KeyThread (KeyFill laid₁ one₀ rangesTestJob sentRanges WitIsJob)
open AtFullSide.K12 (withTests)
open VerifierAndGoals (InScope)

/-- **The five statements at a member of a thread.** -/
structure Five {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (fall : Nat → S → List Fmt.Drawn → Option String)
    (b : Nat) : Prop where
  plays : PlaysS T Said b
  behind : BehindS T Said b
  exchange : ExchangeS T Said b
  rides : RidesPastS T Said b
  accepted : AcceptedS T Said fall b

variable {W₀ Rc Cells M Smp Rec X₀ X Wk : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
  (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (own₀ : X)
  (rest : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Kp : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12)

/-- **The five, at any halves and any table that meet the test.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem five_of_tb (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
    (tb : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X) Xs N Pl entry groups first)))
    (hkind : ∀ s s', RngYes Xs N s s' → L.kind₁ 15 s s')
    (hkept : ∀ s s', L.kind₁ 15 s s' → RngKept s s') (hSm : L.base.SmOnly)
    (horc : L.base.orc₁ = (plan₁ (one₀ Xs)).orc) (hArr : ArrOk L.base.h₁ atSix [0, 1, 2])
    (hsame : L.R.same = fun a b => readE a = readE b)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      AtPublicFiles.KeyThread.TbIsSent Xs N Pl entry groups first L w₀ rc x hs tb k m)
    (htb : ∀ τ, τ < 3 → tb (.own (2 + τ)) =
      testTbl 0 (rangesTestJob (X' := X) Xs N Pl entry groups first) own₀
        (roundsTo (AtPublicFiles.KeyThread.D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ)
    (hRows : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)] 0 = .ok c →
      RowsTrue (X' := X) Xs N Pl entry groups first s m
        (restCoins (rangesTestJob (X' := X) Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Five (laid₁ Xs N Pl L w₀ rc x hs tb) Said fall 15 :=
  ⟨playsS_rng Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope Said hhalf hTb own₀ htb,
    behindS_rng Xs N Pl L w₀ rc x _ _ hsrc scope hkind Said,
    exchangeS_rng Xs N Pl L w₀ rc x _ _ Said,
    ridesPastS_rng Xs N Pl L w₀ rc x _ _ hsrc scope hkept hSm horc hArr hsame Said,
    acceptedS_rng Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope Said hhalf hTb hRows fall⟩

/-- **The five, at any list of halves that finds the test's half.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem five_at_side (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X) Xs N Pl entry groups first)))
    (hkind : ∀ s s', RngYes Xs N s s' → L.kind₁ 15 s s')
    (hkept : ∀ s s', L.kind₁ 15 s s' → RngKept s s') (hSm : L.base.SmOnly)
    (horc : L.base.orc₁ = (plan₁ (one₀ Xs)).orc) (hArr : ArrOk L.base.h₁ atSix [0, 1, 2])
    (hsame : L.R.same = fun a b => readE a = readE b)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hRows : ∀ k s m E (c₁ : Cs (K1.dueR (sentRanges Xs entry groups first).P
        (sentRanges Xs entry groups first).ride)),
      ThrS (laid₁ Xs N Pl L w₀ rc x hs (tbRng Xs N Pl entry groups first own₀ rest)) Said 15
        k s m E →
      ((k.look 0) sMsg).2.cut ⟨0, 0⟩
        (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) =
          some c₁ →
      RowsTrueOf s (K1.rowsR (sentRanges Xs entry groups first).P
          (sentRanges Xs entry groups first).ride
          ((sentRanges Xs entry groups first).data m.st.input) c₁ 0)
        ((shapeAt (sentRanges Xs entry groups first).P 0).mainDeg == 3))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Five (laid₁ Xs N Pl L w₀ rc x hs (tbRng Xs N Pl entry groups first own₀ rest)) Said fall 15 :=
  ⟨playsS_rng Xs N Pl entry groups first L w₀ rc x hs _ hK hsrc scope Said hhalf
      (fun k _ m _ _ => tbRng_sent Xs N Pl entry groups first own₀ rest L w₀ rc x hs hsrc scope k m)
      own₀ fun _ hτ => tbRng_test Xs N Pl entry groups first own₀ rest hτ,
    behindS_rng Xs N Pl L w₀ rc x _ _ hsrc scope hkind Said,
    exchangeS_rng Xs N Pl L w₀ rc x _ _ Said,
    ridesPastS_rng Xs N Pl L w₀ rc x _ _ hsrc scope hkept hSm horc hArr hsame Said,
    acceptedS_rng Xs N Pl entry groups first L w₀ rc x hs _ hK hsrc scope Said hhalf
      (fun k _ m _ _ => tbRng_sent Xs N Pl entry groups first own₀ rest L w₀ rc x hs hsrc scope k m)
      (fun k s m E c hT hc => by
        obtain ⟨c₁, hown⟩ := AtPublicFiles.KeyThread.purse_cut Xs N Pl entry groups first hK hsrc scope k
        exact rowsTrue_of_sent Xs N Pl entry groups first hK hsrc scope k c hc c₁ hown s m
          (hRows k s m E c₁ hT hown))
      fall⟩

/-- **The five, at the key file's test on the ranges.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem five_rng (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (hkind : ∀ s s', RngYes Xs N s s' → L.kind₁ 15 s s')
    (hkept : ∀ s s', L.kind₁ 15 s s' → RngKept s s') (hSm : L.base.SmOnly)
    (horc : L.base.orc₁ = (plan₁ (one₀ Xs)).orc) (hArr : ArrOk L.base.h₁ atSix [0, 1, 2])
    (hsame : L.R.same = fun a b => readE a = readE b)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hRows : ∀ k s m E (c₁ : Cs (K1.dueR (sentRanges Xs entry groups first).P
        (sentRanges Xs entry groups first).ride)),
      ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
        (tbRng Xs N Pl entry groups first own₀ rest)) Said 15 k s m E →
      ((k.look 0) sMsg).2.cut ⟨0, 0⟩
        (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) =
          some c₁ →
      RowsTrueOf s (K1.rowsR (sentRanges Xs entry groups first).P
          (sentRanges Xs entry groups first).ride
          ((sentRanges Xs entry groups first).data m.st.input) c₁ 0)
        ((shapeAt (sentRanges Xs entry groups first).P 0).mainDeg == 3))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Five (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
      (tbRng Xs N Pl entry groups first own₀ rest)) Said fall 15 :=
  five_at_side Xs N Pl entry groups first L w₀ rc x own₀ rest hK hsrc scope _
    (find_rng _ Xs N Pl entry groups first
      (atPlaces_withTests Kp Xs N Pl entry groups first hP hsrc scope pU pO) rfl)
    hkind hkept hSm horc hArr hsame Said hRows fall

/-- **The five, from the tie on the witness.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem five_of_wit (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (hkind : ∀ s s', RngYes Xs N s s' → L.kind₁ 15 s s')
    (hkept : ∀ s s', L.kind₁ 15 s s' → RngKept s s') (hSm : L.base.SmOnly)
    (horc : L.base.orc₁ = (plan₁ (one₀ Xs)).orc) (hArr : ArrOk L.base.h₁ atSix [0, 1, 2])
    (hsame : L.R.same = fun a b => readE a = readE b)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hW : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
        (tbRng Xs N Pl entry groups first own₀ rest)) Said 15 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)] 0 = .ok c →
      WitIsJob (X' := X) Xs N Pl entry groups first L k s m
        (restCoins (rangesTestJob (X' := X) Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Five (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
      (tbRng Xs N Pl entry groups first own₀ rest)) Said fall 15 :=
  ⟨playsS_at_table Xs N Pl entry groups first own₀ rest L w₀ rc x Kp pU pO hK hsrc scope hP Said,
    behindS_rng Xs N Pl L w₀ rc x _ _ hsrc scope hkind Said,
    exchangeS_rng Xs N Pl L w₀ rc x _ _ Said,
    ridesPastS_rng Xs N Pl L w₀ rc x _ _ hsrc scope hkept hSm horc hArr hsame Said,
    acceptedS_at_table Xs N Pl entry groups first own₀ rest L w₀ rc x Kp pU pO hK hsrc scope hP Said
      (fun k s m E c hT hc => rowsTrue_of_wit Xs N Pl entry groups first L w₀ rc x _ _ hsrc scope
        hT.1 _ (hW k s m E c hT hc)) fall⟩

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.five_of_tb
#print axioms ProofFile.Honest.K12.AtKey.five_at_side
#print axioms ProofFile.Honest.K12.AtKey.five_rng
#print axioms ProofFile.Honest.K12.AtKey.five_of_wit
