-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Pays210Name.lean: The key
file's tables, row 2.10 (the proximity test on Omega's group G_omega; the test's second arm): `Pays`
AT The21AtName's OWN TERMS (X N P D · baseAt X decN recBack · readAt tab · collN …), IN THE FORM OF
THE PREMISE hpay OF `keepsAt_k12₂` (Johnson/RunOne/Law/K12AtField.lean): at whatever the row's own
look-up gives. In the form of K12Pays29Name.lean (row 2.9).
WHAT IT IS NOT, FIRST. IT FILLS NO FIELD OF THE TABLES: `Owed210` AND hrow ARE PREMISES, AND NO
EXAMPLE SHOWS THAT THEY CAN BE MET. WRITTEN AND NOT CALLED: ten_facts_key (declared nowhere in
this library: what it concludes stands as hrow and as eleven fields of `Owed210`). No soundness is
claimed. Nothing on hiding.
OF THE VERIFIER's STATE AND THE STRINGS NOTHING IS LEFT AS A PREMISE: ALL IS READ OFF «on10 10 a»
(the tables' invariant and the history). CALLED HERE: `fwd_210_name` at `fk_O_at`
(the invariant behind) · `s10_scope` (the sendings' invariant at Omega and at the split's masks; its
hfit is Free₂.fits) · `shapeIs_2910_placed` (the book's trees' shapes) · `seatFits_one_scope` ·
`seats_six_scope` (told · hlog) · `hi_at` · `hSm_at` · `openKinds_at_reached₂`
· `bookStep_of_shape₂` · Free₂.placed | shown | fits · `num₁_210` · `stages_32` ·
`evalIn_of_free₂` · `depth_of_planOk` · `keyPlan_O` ·
`sm_of_seed` · `dep_at_210` · `pays_210S` with all beneath · AND hal IS ⟨rfl, rfl, rfl⟩: at the
table's own sub-protocol bareB (retype (onGomega …)) name, rounds and decision are the seated test's
by unfolding.
  `on10`: the row's «on»: the tables' invariant, and at border 10 the history. THIS ROW's OWN
    LETTER: nobody may chain it with row 2.9's.
  `Owed210`: what is owed, at the look-up's base and stretch: SIXTEEN FIELDS, ALL PUBLIC: on the
    made place, the look-up's base and stretch, and the row's errors.
  `keeps_210_name`: `keepsAt_O` takes it: KeepsAt at «on10».
  WHOEVER SPENDS EITHER MUST HOLD on10 (the invariant AND, at border 10, the history), not the
  tables' invariant alone.
  `owed_210`: `Owed210` itself at the look-up, in scope: for the door's
  files.
  `pays_210_full` · `keeps_210_full`: hrow and `Owed210Seat`
  paid: NOTHING IS OWED BUT THE SEAT's OWN, the chains' heads, hoffN, hcap and the filler's nine.
  `pays_210_seat`: at the seat's letters, K12PlaceAtName.lean's payers
  called: `Owed210Seat`: seven fields are left.
  `pays_210_name`. BESIDE THE SCOPE's PREMISES: hN (the ranges' numbers) · hD (the data of the key
    file are D) · hoffN (the seats' offsets are the written ones) · hlo (the shared chain's first
    own tree is number 6).

-/
import Johnson.RunOne.Law.K12Pays210
import Johnson.RunOne.Law.K12Members29
import Johnson.RunOne.Law.K12FwdName
import Johnson.RunOne.Law.KeyAt2932Scope
import Johnson.RunOne.KeyWalkAny
import Johnson.Loose.H2K12.RoundsAtKeySeats
import Johnson.RunOne.Law.KeySeeds2910
import Johnson.RunOne.Law.BookAt2910
import Johnson.RunOne.KeyFillSeed2At
import Johnson.RunOne.KeyBookAtSeats
import Johnson.RunOne.KeyEvalIn
import Johnson.Top.Fire.Code.KeyAt32Letters
import Johnson.Desc.Sound.SeamDesc
import Johnson.Desc.K12.Coin.GameJ
import Johnson.RunOne.Law.StepSide2
import Johnson.RunOne.Law.K12PlaceAtName
import Johnson.Desc.K12.Law.KeyPreLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Pays210Name
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held pieceOf Rest smpSt atDesc piecesAt)
open Cb Johnson.Pack
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows1 (plan₁)
open LPFD.CandLaid
open LPFD (readAt decN recBack collN MsgN Hist₂)
open H2K.Pin (tabP)
open H2K.Pub (johOk batV0 sgOf PayPub)
open Johnson.RunOne.Law.K12AtField (Pays)
open Johnson.RunOne.Law.K12Back210 (i4 i5)
open Johnson.RunOne.Law.K12Pays210 (Debts210S pays_210S)
open Johnson.RunOne.Law.K12Members210 (dep_at_210)
open Johnson.RunOne.Law.K12Members29 (sm_of_seed)
open H2K.Member (rKOFull)

/-- The place. -/
abbrev pi10 (nO : H2U.PlaceNums) : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO

/-- The table's own sub-protocol at the row (`O_at`, K12AtField.lean). -/
abbrev B10 (nO : H2U.PlaceNums) : Block St₂ Key.Claim :=
  Johnson.RunOne.Sound.bareB
    (Block.retype (Cl := Unit) (Cl' := Key.Claim) (Seat.onGomega (proximityTestKind guardedProximityTestParts (pi10 nO))))

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  (tab : MsgN → ℕ → ℕ → OnBytes.F) (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat)
  (off₂ : Nat → Nat)

/-- **The row's «on»**: the tables' invariant; at border 10 also the history. -/
def on10 (k : ℕ) (a : (P₂ × St₂) × (fr₂ D).E.Str) : Prop :=
  On₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ k a ∧
    (k = 10 → Hist₂ (Fk X N P) D 10 a.1)

/-- **All that is owed at the row**, at the base and the stretch that the row's look-up gives: all
public (the made place · the look-up's base and stretch · the row's errors). -/
structure Owed210 {W : Type} (nO : H2U.PlaceNums) (r : Fmt.M1.Stage → ℕ)
    (base : ℕ) (dB : RDT) (dt : List RDT)
    (x' : Rest (ckP .two) (fr₂ D) (P₂ × St₂) W (dB :: dt)) : Prop where
  /-- owed (K12's files'): every open pin's tree lies below the piece's base -/
  pins : ∀ k ∈ pinned (open₂ 10), (atSix k).1 < base
  /-- owed (K12's files': the tile's base) -/
  baseIs : base = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own (pi10 nO).nums.free)
  /-- owed (K12's files': ten_facts_key's TenFacts.place) -/
  place : AtPlaceOwn (fr₂ D) (pi10 nO) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1) Sg.lstJ Sg.flC Sg.flZ
    Sg.flZ (fun s => r s.st)
    (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own (pi10 nO).nums.free)) dB dt (errJ (pi10 nO) r dt)
  /-- owed (K12's files': TenFacts.pays, first) -/
  pay : PayPub (pi10 nO) (fun s => r s.st) dB.entry.rows (batV0 (pi10 nO) r)
  /-- owed (K12's files': TenFacts.pays, second): the form of the round "BAT" -/
  bat : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]
  /-- owed (K12's files': TenFacts.pays, third) -/
  log64 : dB.entry.logN ≤ 64
  /-- owed (K12's files': TenFacts.own) -/
  own : (pi10 nO).nums.ownMask = true
  /-- owed (K12's files': TenFacts.labels) -/
  labels : ownLabelsB (pi10 nO) = true
  /-- owed (K12's files': at the closed place) -/
  ne : H2K.Made.firstNe (pi10 nO) = true
  /-- owed (K12's files': at the closed place) -/
  free : 0 < (pi10 nO).nums.free
  /-- owed (K12's files': TenFacts.small where the row's errors are the cap) -/
  cap : Err.le ((batV0 (pi10 nO) r * (bsRound .two dB.entry dB.kind).w, errJ (pi10 nO) r dt) :
    Err (uLT (ckP .two) (dB :: dt))) x'.err
  /-- owed (K12's files': TenFacts.joh at the made place) -/
  joh : johOk (pi10 nO) r = true
  /-- owed (K12's files': TenFacts.ft) -/
  ft : (pi10 nO).nums.firstTree = 0
  /-- owed (K12's files'): the fit at the place's first stage, at Omega -/
  fit2 : ∀ s rest, (pi10 nO).nums.stages = s :: rest →
    r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1)
  /-- owed (K12's files'): … and at the split's masks -/
  fit3 : ∀ s rest, (pi10 nO).nums.stages = s :: rest →
    r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1)
  /-- owed (K12's files'): the split's masks' code is no deeper than the first stage's mask code -/
  stageZ : ∀ s rest, (pi10 nO).nums.stages = s :: rest → aOf csKey (six.get i5).1 ≤ s.Z.a

variable {W : Type}
  (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl)
  (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))
  (c₂ : Block (Key.descriptionFromSource X N P).S₂ (Key.descriptionFromSource X N P).Cl)
  (k₂ : List (Block (Key.descriptionFromSource X N P).S₂ (Key.descriptionFromSource X N P).Cl))
  (c₃ : Block (Key.descriptionFromSource X N P).S₃ (Key.descriptionFromSource X N P).Cl)
  (k₃ : List (Block (Key.descriptionFromSource X N P).S₃ (Key.descriptionFromSource X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (fr₁ D)
    ((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (fr₂ D)
    (((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁) × (Key.descriptionFromSource X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (fr₃ X N P D)
    (((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂) × (Key.descriptionFromSource X N P).S₃)
    W ds)
  (dW wEnd : W)

set_option maxHeartbeats 1000000 in
/-- **`Pays` at row 2.10, at the name's terms, in the form of `keepsAt_k12₂`'s hpay.** -/
theorem pays_210_name {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    (hD : (Fk X N P).data "key file" = .ok D)
    (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (n : ℕ) (hn : n = 10) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z)
    (hlo : numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0) = 6)
    (hrow : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base ds back (rest₂ n ds)) →
      ∃ dB dt, ds = dB :: dt ∧ back = [])
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed210 X N P D nO r base dB dt (rest₂ n (dB :: dt))) :
    ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base ds back (rest₂ n ds)) →
      Pays (fr₂ D) (pi10 nO) (fun s t => Seat.enter (·.gOmega) (fun _ => none) s = .ok t)
        (fun s t s' => Seat.leave s t = .ok s') (held (B10 nO))
        (on10 X N P D tab enc rad off₂)
        (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) n base ds back
        (rest₂ n ds) := by
  intro base ds back hl
  obtain ⟨dB, dt, rfl, rfl⟩ := hrow base ds back hl
  have O := owed base dB dt hl
  subst hn
  have seats := KeyAt2932.seats_six_scope (N := N) (P := P) hZ hP hm hX hp hw DK hD₀ hDK
  have fits := fun i => seatFits_one_scope (N := N) (P := P) hZ hP hm hX hp hw DK hD₀ hDK i
  have hoff : ∀ q, off₂ q = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0) + q := fun q => by
    rw [hoffN, hlo]
    rfl
  have hfw := K12FwdName.fwd_210_name X N P D tab enc rad off₂ hZ hP hm hX hL hp nO hO (B10 nO)
    (K12SeatsAt.fk_O_at X N P nO hO)
  exact pays_210S (Fk X N P) (fr₂ D) decN recBack (plan₁ (oneAt X)).orc tab (shapeAt X)
    (plan₁ (oneAt X)) enc rad (oneAt X).given.plan.samples collN (last₁At (oneAt X)) off₂ (pi10 nO)
    (Fk X N P).t₁ (Fk X N P).t₂ r rdN oNo mem rd hrd (on10 X N P D tab enc rad off₂)
    (fun a h => h.1) (fun b h => ⟨h, fun e => absurd e (by decide)⟩) (B10 nO) hfw
    ⟨rfl, rfl, rfl⟩ (H2K.JointK.keyPlan_O X N P hp nO hO) O.ft O.joh hoff ho2 ho3 O.fit2 O.fit3
    (fun i _ => fits i)
    (fun i _ u hu e he hno =>
      _root_.Desc.K14.Law.Fence.depth_of_planOk (Fk X N P) "key file" D hp hD D.key₂ 0 _ u hu e he
        hno)
    (KeyAt2932.hi_at X) (KeyAt2932.hSm_at X) (fun i _ => (seats i).2)
    (fun i _ => (seats i).1) hmem3 hmem2 base O.pins dB dt (rest₂ 10 (dB :: dt))
    (fun a τ b ha hout => by
      obtain ⟨hshape, _, hfree, _⟩ := id (ha.1.resolve_left (fun h => h trivial))
      obtain ⟨s2, s3⟩ := KeySeeds2910.s10_scope hZ hP hm hX hL hp hw hN D a (ha.2 rfl) hfree.fits
      have hB := (bookStep_of_shape₂ (shapeAt X) _ 10 a.1.2 hshape).2
      obtain ⟨o5, q5, e5, hq5, hat5⟩ := hfree.placed 5 (by decide)
      obtain rfl : 3 = o5 := Option.some.inj e5
      have told := fun (k' : ℕ) (hk' : k' ∈ [3, 4, 5])
          (hl : k' ∈ (pinned (open₂ 10)).filter (3 ≤ ·)) (o' : ℕ)
          (ho' : (plan₂ (shapeAt X)).orc k' = some o') (q : ℕ × ℕ)
          (hq : a.1.2.book.place[o']? = some q) =>
        BookAt2910.shapeIs_2910_placed hZ hP hm hX hp hw DK hD₀ hDK D 10 a.1 (by decide) (by decide)
          (ha.2 rfl) off₂ hoffN _ hfree.placed k' hk' hl o' ho' q hq
      exact
        { seed2 := s2
          seed3 := s3
          dep := dep_at_210 (Fk X N P) (pi10 nO) _ off₂ hoff O.ft a.1.2 hB i5 3 q5 hq5 hat5
            (seats i5).1 (seats i5).2 (told 5 (by decide) (by decide) 3 rfl q5 hq5) O.stageZ
          tree := fun i o hio q hq _ => by
            rcases hio with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact told 5 (by decide) (by decide) 3 rfl q hq
            · exact told 4 (by decide) (by decide) 2 rfl q hq
          sm := fun i hi => by
            rcases hi with rfl | rfl
            · exact sm_of_seed _ oNo i5 (by decide) 3 rfl ho3 a.1 s3
            · exact sm_of_seed _ oNo i4 (by decide) 2 rfl ho2 a.1 s2
          shown := fun i hi x hx => by
            obtain ⟨ht, hlg⟩ := seats i
            obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 ht
            rcases hi with rfl | rfl
            · exact hfree.shown 5 (by decide) o ho x (by rw [hlg o ho]; exact hx)
            · exact hfree.shown 4 (by decide) o ho x (by rw [hlg o ho]; exact hx)
          kinds := KeyWalk.openKinds_at_reached₂ D 10 a.1 (ha.2 rfl) })
    (LPFD.num₁_210 (N := N) (P := P) hZ hP hm hX hp)
    (fun a ha => by
      obtain ⟨_, _, hfree, _⟩ := id (ha.1.resolve_left (fun h => h trivial))
      exact evalIn_of_free₂ (Fk X N P) _ atSix (shapeAt X) (oneAt X) _ collN off₂ [0, 2, 4]
        (by decide) (by decide) (LPFD.stages_32 (N := N) (P := P) hZ hP hm hX hp) 10 a.1 _ hfree)
    O.baseIs Sg.lstJ Sg.flC Sg.flZ Sg.flZ _ (batV0 (pi10 nO) r) (errJ (pi10 nO) r dt)
    O.place O.pay O.bat O.log64 (Nat.le_refl _) O.own O.labels O.ne O.free O.cap

/-- **THE FIT, BY LEAN: `keepsAt_O` TAKES `pays_210_name`**: the tables' field's own
form (KeepsAt) at the row's number, under `pays_210_name`'s premises and q₂. (The number is
`keepsAt_O`'s own; it is 10 by `table_eight`.) AT «on10», NOT AT THE TABLES' OWN INVARIANT ALONE. -/
theorem keeps_210_name {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    (hD : (Fk X N P).data "key file" = .ok D)
    (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (n : ℕ) (hidx : n = 1 + ((K12SeatsAt.tableBlocks X P).length + 1)) (r : Fmt.M1.Stage → ℕ)
    (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z)
    (hlo : numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0) = 6)
    (hrow : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base ds back (rest₂ n ds)) →
      ∃ dB dt, ds = dB :: dt ∧ back = [])
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed210 X N P D nO r base dB dt (rest₂ n (dB :: dt)))
    (q₂ : (Key.descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂) :
    LPFD.KeepsAt (on10 X N P D tab enc rad off₂)
      (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad)
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂) n := by
  subst hidx
  exact K12AtField.keepsAt_O X N P D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
    (on10 X N P D tab enc rad off₂)
    (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) q₂ nO hO
    (pays_210_name X N P D tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX
      hL hN hp hw DK hD₀ hDK hD nO hO _
      (by have := StepSide2.table_eight X N P hp; omega) r rdN oNo mem rd hrd ho2 ho3 hmem3 hmem2
      hoffN hlo hrow owed)

/-- **What is still owed at the row, at the seat's letters** (the radii rKOFull): SEVEN FIELDS, all
on the tile's piece and the made place: K12PlaceAtName.lean's to pay. -/
structure Owed210Seat {W : Type} (nO : H2U.PlaceNums) (base : ℕ) (dB : RDT) (dt : List RDT)
    (x' : Rest (ckP .two) (fr₂ D) (P₂ × St₂) W (dB :: dt)) : Prop where
  /-- owed (K12's files': the tile's base) -/
  baseIs : base = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own (pi10 nO).nums.free)
  /-- owed (K12's files': TenFacts.place) -/
  place : AtPlaceOwn (fr₂ D) (pi10 nO) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1) Sg.lstJ Sg.flC Sg.flZ
    Sg.flZ (fun s => rKOFull s.st)
    (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own (pi10 nO).nums.free)) dB dt
    (errJ (pi10 nO) rKOFull dt)
  /-- owed (K12's files': TenFacts.pays, first) -/
  pay : PayPub (pi10 nO) (fun s => rKOFull s.st) dB.entry.rows (batV0 (pi10 nO) rKOFull)
  /-- owed (K12's files': TenFacts.pays, second) -/
  bat : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]
  /-- owed (K12's files': TenFacts.pays, third) -/
  log64 : dB.entry.logN ≤ 64
  /-- owed (K12's files': TenFacts.labels) -/
  labels : ownLabelsB (pi10 nO) = true
  /-- owed (K12's files': TenFacts.small where the row's errors are the cap) -/
  cap : Err.le ((batV0 (pi10 nO) rKOFull * (bsRound .two dB.entry dB.kind).w,
    errJ (pi10 nO) rKOFull dt) : Err (uLT (ckP .two) (dB :: dt))) x'.err

/-- **`pays_210_name` AT THE SEAT's LETTERS** (D the written data at the frame's depth · the
radii rKOFull), with K12PlaceAtName.lean's payers called: pins₂ · joh_210 ·
ft_210 · fit2_210 · fit3_210 · stageZ_210 · lo_six · nums_210 with three kernel lines. GONE: hD ·
hlo · the letter r · nine fields (pins · joh · ft · fit2 · fit3 · stageZ · own · ne · free). NEW:
hasks (the accept of every test that the key file's laws ask; the seat hands it) · q₁ q₂ q₃. -/
theorem pays_210_seat {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (n : ℕ) (hn : n = 10) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hrow : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base ds back (rest₂ n ds)) →
      ∃ dB dt, ds = dB :: dt ∧ back = [])
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed210Seat X N P D nO base dB dt (rest₂ n (dB :: dt))) :
    ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base ds back (rest₂ n ds)) →
      Pays (fr₂ D) (pi10 nO) (fun s t => Seat.enter (·.gOmega) (fun _ => none) s = .ok t)
        (fun s t s' => Seat.leave s t = .ok s') (held (B10 nO))
        (on10 X N P D tab enc rad off₂)
        (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) n base ds back
        (rest₂ n ds) := by
  subst hDD
  subst hn
  refine pays_210_name X N P _ tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
    hX hL hN hp hw DK hD₀ hDK hD₀ nO hO 10 rfl rKOFull rdN oNo mem rd hrd ho2 ho3 hmem3 hmem2 hoffN
    (K12PlaceAtName.lo_six hZ hP hm hL X N hp hasks) hrow (fun base dB dt hl => ?_)
  have O := owed base dB dt hl
  have hnums := K12PlaceAtName.nums_210 hZ hP hm hL X N hp hasks nO hO
  exact
    { pins := K12PlaceAtName.pins₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX
        hp hw hDK q₁ q₂ q₃ 10 _ hl
      baseIs := O.baseIs
      place := O.place
      pay := O.pay
      bat := O.bat
      log64 := O.log64
      own := by rw [hnums]; decide +kernel
      labels := O.labels
      ne := by unfold H2K.Made.firstNe; rw [hnums]; decide +kernel
      free := by rw [hnums]; decide +kernel
      cap := O.cap
      joh := K12PlaceAtName.joh_210 hZ hP hm hL X N hp nO hO
      ft := K12PlaceAtName.ft_210 hL X N hp nO hO
      fit2 := K12PlaceAtName.fit2_210 hZ hP hm hL X N hp nO hO
      fit3 := K12PlaceAtName.fit3_210 hZ hP hm hL X N hp nO hO
      stageZ := K12PlaceAtName.stageZ_210 hZ hP hm hL X N hp nO hO }

/-- **`Pays` AT ROW 2.10 WITH NOTHING OWED**: `pays_210_seat` with hrow AND `Owed210Seat` PAID
by `place_210` (the stretch is dB :: dt · the base · AtPlaceOwn · the three on
"BAT"'s round · the cap), `small_210` (the labels) and `row_cut₂` (nothing is put behind). BINDERS:
the seat's own (hZ hP hm hX hp hw · DK hD₀ hDK · hL · hN · hasks) · hDD · nO hO · hoffN · the
chains' heads q₁ q₂ q₃ · n hn · hcap («the row's errors are the cap at 128»: rfl at capRest) · the
filler's nine. FIRST LIMIT: NO EXAMPLE SHOWS THAT THESE CAN BE MET TOGETHER; it stands on every file
beneath it.
-/
theorem pays_210_full {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (n : ℕ) (hn : n = 10) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hcap : ∀ ds, (rest₂ n ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base ds back (rest₂ n ds)) →
      Pays (fr₂ D) (pi10 nO) (fun s t => Seat.enter (·.gOmega) (fun _ => none) s = .ok t)
        (fun s t s' => Seat.leave s t = .ok s') (held (B10 nO))
        (on10 X N P D tab enc rad off₂)
        (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) n base ds back
        (rest₂ n ds) := by
  subst hDD
  subst hn
  have hlen : 10 = (H2K.JointK.keySharedPre X.chains P ++ [H2K.JointK.keyGu P]).length :=
    ((H2K.JointK.keySharedPreGu_length X.chains P).trans
      (by rw [show (_root_.Desc.K14.blocksOr
        (Key.sharedPar X.chains (Key.beforeSharedPoint P))).length = 8 from
          StepSide2.table_eight X N P hp])).symm
  have P210 := K12PlaceAtName.place_210 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP
    hm hL hp hD₀ hasks q₂ nO hO 10 hlen
  have hfl : (Fk X N P).shared.blocksInOrder =
      (H2K.JointK.keySharedPre X.chains P ++ [H2K.JointK.keyGu P]) ++
        H2K.JointK.keyOmega nO :: H2K.JointK.keySharedEnd X.chains P :: [] :=
    H2K.JointK.key_shared_flat_omega X N P nO hO
  exact pays_210_seat X N P _ tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
    hX hL hN hp hw DK rfl hD₀ hDK hasks nO hO 10 rfl rdN oNo mem rd hrd ho2 ho3 hmem3 hmem2 hoffN q₁
    q₂ q₃
    (fun base ds back hl => by
      obtain ⟨dB, dt, e, _⟩ := P210 _ hl
      have tr : ∀ k : ℕ, 10 = k →
          ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁
              c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
            (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁
              c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[k]? =
            some (pieceOf (held (B10 nO)) base ds back (rest₂ 10 ds)) := fun k hk => by
        subst hk
        exact hl
      exact ⟨dB, dt, e, (K12PlaceAtName.row_cut₂ (Fk X N P) _ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd (H2K.JointK.keySharedPre X.chains P ++ [H2K.JointK.keyGu P]) (H2K.JointK.keyOmega nO)
        (H2K.JointK.keySharedEnd X.chains P) [] (q₂.symm.trans hfl) _ (tr _ hlen)).2.1⟩)
    (fun base dB dt hl => by
      obtain ⟨dB', dt', e, hb, hA, ⟨hpay, hbat, hlg⟩, hC⟩ := P210 _ hl
      obtain ⟨rfl, rfl⟩ := List.cons.inj e
      have hb' : base = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own (pi10 nO).nums.free) := hb
      subst hb'
      exact
        { baseIs := rfl
          place := hA
          pay := hpay
          bat := hbat
          log64 := hlg
          labels := (K12PlaceAtName.small_210 hZ hP hm hL X N hp hasks nO hO).2.1
          cap := by rw [hcap]; exact hC })

/-- **THE TABLES' FIELD's OWN FORM AT THE ROW, WITH NOTHING OWED**: `keepsAt_O` (K12AtField.lean)
over `pays_210_full`: KeepsAt at `on10` (the invariant, and at border 10 the history). The join of
`on10` with the tables' On₂′ is other files' to show. -/
theorem keeps_210_full {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (n : ℕ) (hidx : n = 1 + ((K12SeatsAt.tableBlocks X P).length + 1)) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hcap : ∀ ds, (rest₂ n ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    LPFD.KeepsAt (on10 X N P D tab enc rad off₂)
      (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad)
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂) n := by
  subst hidx
  exact K12AtField.keepsAt_O X N P D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
    (on10 X N P D tab enc rad off₂)
    (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) q₂ nO hO
    (pays_210_full X N P D tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX
      hL hN hp hw DK hDD hD₀ hDK hasks nO hO _
      (by have := StepSide2.table_eight X N P hp; omega) rdN oNo mem rd hrd ho2 ho3 hmem3 hmem2
      hoffN q₁ q₂ q₃ hcap)

/-- **`Owed210` ITSELF, AT THE LOOK-UP, IN SCOPE** (for the door's files: the one premise that
their «from Owed to the field» still asks at this row): all sixteen fields at the radii rKOFull, by
K12PlaceAtName.lean's payers. `pays_210_name`'s hlo beside it is `lo_six`. NO EXAMPLE. -/
theorem owed_210 {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (nO : H2U.PlaceNums) (hO : P.O = some nO) (n : ℕ) (hn : n = 10)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hcap : ∀ ds, (rest₂ n ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B10 nO)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed210 X N P D nO rKOFull base dB dt (rest₂ n (dB :: dt)) := by
  subst hDD
  subst hn
  have hlen : 10 = (H2K.JointK.keySharedPre X.chains P ++ [H2K.JointK.keyGu P]).length :=
    ((H2K.JointK.keySharedPreGu_length X.chains P).trans
      (by rw [show (_root_.Desc.K14.blocksOr
        (Key.sharedPar X.chains (Key.beforeSharedPoint P))).length = 8 from
          StepSide2.table_eight X N P hp])).symm
  intro base dB dt hl
  have hpins := K12PlaceAtName.pins₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
    hX hp hw hDK q₁ q₂ q₃ 10 _ hl
  obtain ⟨dB', dt', e, hb, hA, ⟨hpay, hbat, hlg⟩, hC⟩ :=
    K12PlaceAtName.place_210 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hL hp hD₀
      hasks q₂ nO hO 10 hlen _ hl
  obtain ⟨rfl, rfl⟩ := List.cons.inj e
  obtain ⟨hown, hlab, hne, hfree⟩ := K12PlaceAtName.small_210 hZ hP hm hL X N hp hasks nO hO
  have hb' : base = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own (pi10 nO).nums.free) := hb
  subst hb'
  exact
    { pins := hpins
      baseIs := rfl
      place := hA
      pay := hpay
      bat := hbat
      log64 := hlg
      own := hown
      labels := hlab
      ne := hne
      free := hfree
      cap := by rw [hcap]; exact hC
      joh := K12PlaceAtName.joh_210 hZ hP hm hL X N hp nO hO
      ft := K12PlaceAtName.ft_210 hL X N hp nO hO
      fit2 := K12PlaceAtName.fit2_210 hZ hP hm hL X N hp nO hO
      fit3 := K12PlaceAtName.fit3_210 hZ hP hm hL X N hp nO hO
      stageZ := K12PlaceAtName.stageZ_210 hZ hP hm hL X N hp nO hO }

end Johnson.RunOne.Law.K12Pays210Name

#print axioms Johnson.RunOne.Law.K12Pays210Name.pays_210_name
#print axioms Johnson.RunOne.Law.K12Pays210Name.keeps_210_name
#print axioms Johnson.RunOne.Law.K12Pays210Name.pays_210_seat
#print axioms Johnson.RunOne.Law.K12Pays210Name.pays_210_full
#print axioms Johnson.RunOne.Law.K12Pays210Name.keeps_210_full
#print axioms Johnson.RunOne.Law.K12Pays210Name.owed_210
