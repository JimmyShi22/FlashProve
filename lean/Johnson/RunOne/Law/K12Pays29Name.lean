-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Pays29Name.lean: The key
file's tables, row 2.9 (the proximity test on the folded row's group G_u): `Pays` AT The21AtName's
OWN TERMS (X N P D · baseAt X decN recBack · readAt tab · collN …), IN THE FORM OF THE PREMISE hpay
OF `keepsAt_k12₂` (Johnson/RunOne/Law/K12AtField.lean): at whatever the row's own look-up gives.
WHAT IS LEFT STANDS AS ONE STRUCTURE OF NAMED DEBTS, a field a debt.
WHAT IT IS NOT, FIRST. IT FILLS NO FIELD OF THE TABLES: `Owed29` AND hrow ARE PREMISES, AND NO
EXAMPLE SHOWS THAT THEY CAN BE MET. NOT YET CALLED, THOUGH THEY LIE:
`nine_facts_key` (written, but declared nowhere in this library) and
K12PlaceAtName.lean's
payers at the place: what they conclude stands as hrow and as `Owed29`'s ten fields. No
soundness is claimed. Nothing on hiding.
OF THE VERIFIER's STATE AND THE STRINGS NOTHING IS LEFT AS A PREMISE: every such fact is had off
«on» at border 9 (the tables' invariant and the history) by a call.
CALLED HERE: `fwd_29_name` (the invariant behind) at `fk_U_at` · `seats_six_scope`
(told · hlog) · `fold_scope` (h1 h2) · `hi_at` · `hSm_at` · `s9_scope` (K1.SeedIs at the two
members, off the history; its hfit is Free₂.fits) · `shapeIs_2910_placed` (the book's tree has the
told shape) · `seatFits_one_scope` · `keepsAt_U` with `table_eight` · `openKinds_at_reached₂`
· `bookStep_of_shape₂` · `evalIn_of_free₂` · `stages_32` · `num₁_29` · `samples_32` ·
`depth_of_planOk` · the tables' own Free₂.shown | .placed | .fits ·
`keyPlan_U` · OF K12's FILES: `pays_29S` with all beneath · `shape29_facts` · `hU_six` | `hSp_six` ·
`word_at_29` (over

`word_29`) · `sm_of_seed` · `dep_at_29` · AND hal IS ⟨rfl, rfl, rfl⟩: at the table's own
sub-protocol bareB (retype (onGu …)) name, rounds and decision are the seated test's by unfolding.
  `on9`: the row's «on»: the tables' invariant, and at border 9 the history. THIS ROW's OWN LETTER:
    nobody may chain it with row 2.10's.
  `Owed29`: TEN FIELDS, ALL ON THE PLACE AND THE PIECE, NONE ON A STATE: pins · place · joh · batOne
  ·
    labels · cap · fit0 · fit3 · ft · stageZ.
  `pays_29_name`. MEANT FOR ITS FREE LETTERS: r: the planner's radii at the place (rKUFull) · lo:
  the
    shared chain's first tree's number over the file (6) · num: numAt t₁ t₂ 1 · rdN: any · oNo |
    mem: closed terms with the four equations by rfl · rd: tabP's own reading · off₂: the written
    offsets.
  `keeps_29_name`: `keepsAt_U` (K12AtField.lean) takes it: the fit by Lean.
  `pays_29_seat`: at the seat's letters, with seven
  of the ten called (K12PlaceAtName.lean): left: hrow · `Owed29P` (place · labels · cap).

  `pays_29_full` · `keeps_29_full`: hrow and
  `Owed29P` paid (`place_29` ·
    `row_cut₂`): nothing owed but the seat's own premises, hcap and the filler's rfl's.
  `owed_29`: `Owed29` itself, paid, in the
  ∀-form over the row's look-up.

-/
import Johnson.RunOne.Law.K12Pays29
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
import Johnson.RunOne.Law.StepSide2
import Johnson.Desc.Sound.SeamDesc
import Johnson.RunOne.Law.K12PlaceAtName
import Johnson.Desc.K12.Law.KeyPreLength
import Johnson.Desc.K12.Law.KeyTileFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Pays29Name
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
open H2K.Pin (tabP strOf layOf)
open H2K.Pub (johOk batV0 sgOf)
open H2K.First (batOneOk)
open Johnson.RunOne.Law.K12AtField (Pays)
open Johnson.RunOne.Law.K12Law29Core (i3 i5)
open Johnson.RunOne.Law.K12Pays29 (Debts29S pays_29S shape29_facts)
open Johnson.RunOne.Law.K12Members29 (hU_six hSp_six word_at_29 sm_of_seed dep_at_29)

/-- The place. -/
abbrev pi9 (P : LaterPlaces) : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U

/-- The table's own sub-protocol at the row (`U_at`, K12AtField.lean). -/
abbrev B9 (P : LaterPlaces) : Block St₂ Key.Claim :=
  Johnson.RunOne.Sound.bareB
    (Block.retype (Cl := Unit) (Cl' := Key.Claim) (Seat.onGu (proximityTestKind guardedProximityTestParts (pi9 P))))

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  (tab : MsgN → ℕ → ℕ → OnBytes.F) (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat)
  (off₂ : Nat → Nat)

/-- **The row's «on»**: the tables' invariant; at border 9 also the history. -/
def on9 (k : ℕ) (a : (P₂ × St₂) × (fr₂ D).E.Str) : Prop :=
  On₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ k a ∧
    (k = 9 → Hist₂ (Fk X N P) D 9 a.1)

/-- **All that is owed at the row**, at the base and the stretch that the row's look-up gives. -/
structure Owed29 {W : Type} (r : Fmt.M1.Stage → ℕ) (lo : ℕ) (num : Fmt.TreeSource → ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT)
    (x' : Rest (ckP .two) (fr₂ D) (P₂ × St₂) W (dB :: dt)) : Prop where
  /-- owed (K12's files'): every open pin's tree lies below the piece's base -/
  pins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < base
  /-- owed (K12's files': nine_facts_key's NineFacts.place) -/
  place : AtPlace (fr₂ D) (pi9 P) num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt
    (errJ (pi9 P) r dt)
  /-- owed (K12's files': ClosedL.joh at the made place) -/
  joh : johOk (pi9 P) r = true
  /-- owed (K12's files': NineFacts.batOne) -/
  batOne : batOneOk (pi9 P) = true
  /-- owed (K12's files': labelsPub_own) -/
  labels : LabelsPub (pi9 P) num (nlAt (pi9 P) lo) base
  /-- owed (K12's files': NineFacts.small where the row's errors are the cap) -/
  cap : Err.le ((batV0 (pi9 P) r * (bsRound .two dB.entry dB.kind).w, errJ (pi9 P) r dt) :
    Err (uLT (ckP .two) (dB :: dt))) x'.err
  /-- owed (K12's files'): the fit at the place's first stage, at U -/
  fit0 : ∀ s rest, (pi9 P).nums.stages = s :: rest →
    r (sgOf s).st < ((six.get i3).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i3).1)
  /-- owed (K12's files'): … and at the split's masks -/
  fit3 : ∀ s rest, (pi9 P).nums.stages = s :: rest →
    r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1)
  /-- owed (K12's files': later_more): the place's first tree is 0: THE WORD WANTS IT -/
  ft : (pi9 P).nums.firstTree = 0
  /-- owed (K12's files': a closed comparison at the made place): the split's masks' code is no
  deeper than the first stage's mask code -/
  stageZ : ∀ s rest, (pi9 P).nums.stages = s :: rest → aOf csKey (six.get i5).1 ≤ s.Z.a

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
/-- **`Pays` at row 2.9, at the name's terms, in the form of `keepsAt_k12₂`'s hpay.** -/
theorem pays_29_name {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (hD : (Fk X N P).data "key file" = .ok D) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z) (n : ℕ) (hn : n = 9) (r : Fmt.M1.Stage → ℕ) (lo : ℕ)
    (hlo : lo = 6) (num : Fmt.TreeSource → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hrow : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base ds back (rest₂ n ds)) →
      ∃ dB dt, ds = dB :: dt ∧ back = [])
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed29 P D r lo num base dB dt (rest₂ n (dB :: dt))) :
    ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base ds back (rest₂ n ds)) →
      Pays (fr₂ D) (pi9 P) (fun s t => Seat.enter (·.gU) (·.firstMask) s = .ok t)
        (fun s t s' => Seat.leave s t = .ok s') (held (B9 P))
        (on9 X N P D tab enc rad off₂)
        (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) n base ds back
        (rest₂ n ds) := by
  intro base ds back hl
  obtain ⟨dB, dt, rfl, rfl⟩ := hrow base ds back hl
  have O := owed base dB dt hl
  subst hn
  have seats := KeyAt2932.seats_six_scope (N := N) (P := P) hZ hP hm hX hp hw DK hD₀ hDK
  have fold := KeyAt2932.fold_scope hZ hP hm hX
  exact pays_29S (Fk X N P) (fr₂ D) decN recBack (plan₁ (oneAt X)).orc tab (shapeAt X)
    (plan₁ (oneAt X)) enc rad (oneAt X).given.plan.samples collN (last₁At (oneAt X)) off₂ (pi9 P) lo
    r rdN oNo mem rd hrd (on9 X N P D tab enc rad off₂) (fun a h => h.1)
    (fun b h => ⟨h, fun e => absurd e (by decide)⟩) (B9 P)
    (K12FwdName.fwd_29_name X N P D tab enc rad off₂ hZ hP hm hX hL hp (B9 P)
      (K12SeatsAt.fk_U_at X N P))
    ⟨rfl, rfl, rfl⟩ (H2K.JointK.keyPlan_U X N P hp) (KeyAt2932.hSm_at X) base O.pins dB dt
    (rest₂ 9 (dB :: dt)) (LPFD.num₁_29 hZ hP hm hX hp)
    (fun a ha => evalIn_of_free₂ (Fk X N P) (LPFD.baseAt X decN recBack).h₂ atSix (shapeAt X)
      (oneAt X) (readAt tab) collN off₂ [0, 2, 4, 5] (by decide) (by decide)
      (LPFD.stages_32 hZ hP hm hX hp) 9 a.1 (strsOf (fr₂ D) a.2)
      (id (ha.1.resolve_left (fun h => h trivial))).2.2.1)
    num O.place O.joh O.batOne O.labels O.cap (KeyAt2932.hi_at X)
    (fun i _ => (seats i).2) (fun i _ => (seats i).1) hmem0 hmem3 fold.1 fold.2 ho0 ho3 hU_six
    hSp_six O.fit0 O.fit3 (LPFD.samples_32 hZ hP hm hX hp)
    (fun a τ b ha hout => by
      obtain ⟨hshape, _, hfree, _⟩ := id (ha.1.resolve_left (fun h => h trivial))
      obtain ⟨s0, s3⟩ := KeySeeds2910.s9_scope hZ hP hm hX hL hp hw hN D a (ha.2 rfl) hfree.fits
      have hB := (bookStep_of_shape₂ (shapeAt X) _ 9 a.1.2 hshape).2
      have hmk : a.1.2.loc.firstMask.isSome = true := by
        rw [(shape29_facts _ _ _ hshape).2.2.1]
        rfl
      have hoff : ∀ q, off₂ q = lo + q := fun q => by
        rw [hoffN, hlo]
        rfl
      obtain ⟨o3, q3, e3, hq3, hat3⟩ := hfree.placed 3 (by decide)
      obtain rfl : 0 = o3 := Option.some.inj e3
      obtain ⟨o5, q5, e5, hq5, hat5⟩ := hfree.placed 5 (by decide)
      obtain rfl : 3 = o5 := Option.some.inj e5
      have shown : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
          Sound.ShownAt (Fk X N P) csKey six (seatAt six numSix atSix) (strsOf (fr₂ D) a.2) i := by
        intro i hi x hx
        obtain ⟨ht, hlg⟩ := seats i
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 ht
        rcases hi with rfl | rfl
        · exact hfree.shown 3 (by decide) o ho x (by rw [hlg o ho]; exact hx)
        · exact hfree.shown 5 (by decide) o ho x (by rw [hlg o ho]; exact hx)
      have fits := fun i => seatFits_one_scope (N := N) (P := P) hZ hP hm hX hp hw DK hD₀ hDK i
      have told := fun (k' : ℕ) (hk' : k' ∈ [3, 4, 5])
          (hl : k' ∈ (pinned (open₂ 9)).filter (3 ≤ ·)) (o' : ℕ)
          (ho' : (plan₂ (shapeAt X)).orc k' = some o') (q : ℕ × ℕ)
          (hq : a.1.2.book.place[o']? = some q) =>
        BookAt2910.shapeIs_2910_placed hZ hP hm hX hp hw DK hD₀ hDK D 9 a.1 (by decide) (by decide)
          (ha.2 rfl) off₂ hoffN _ hfree.placed k' hk' hl o' ho' q hq
      have depth := fun (i : Fin six.length) u
          (hu : (Fk X N P).oracleAt (seatAt six numSix atSix i).1 = some u) =>
        _root_.Desc.K14.Law.Fence.depth_of_planOk (Fk X N P) "key file" D hp hD D.key₂ 0 _ u hu
      obtain ⟨ρ, yv, h0⟩ := id s0
      exact ⟨h0.1, s0, s3,
        dep_at_29 (Fk X N P) (pi9 P) lo off₂ hoff O.ft a.1.2 hmk hB i5 3 q5 hq5 hat5 (seats i5).1
          (seats i5).2 (told 5 (by decide) (by decide) 3 rfl q5 hq5) O.stageZ,
        word_at_29 (Fk X N P) (fr₂ D) (pi9 P) lo off₂ hoff O.ft a hmk hB i3 _ _ rfl 0 q3 hq3 hat3 s0
          (fits i3) (shown i3 (Or.inl rfl)) (told 3 (by decide) (by decide) 0 rfl q3 hq3)
          (depth i3),
        word_at_29 (Fk X N P) (fr₂ D) (pi9 P) lo off₂ hoff O.ft a hmk hB i5 _ _ rfl 3 q5 hq5 hat5 s3
          (fits i5) (shown i5 (Or.inr rfl)) (told 5 (by decide) (by decide) 3 rfl q5 hq5)
          (depth i5),
        fun i hi => by
          rcases hi with rfl | rfl
          · exact sm_of_seed _ oNo i3 (by decide) 0 rfl ho0 a.1 s0
          · exact sm_of_seed _ oNo i5 (by decide) 3 rfl ho3 a.1 s3,
        shown, KeyWalk.openKinds_at_reached₂ D 9 a.1 (ha.2 rfl)⟩)

/-- **THE FIT, BY LEAN: `keepsAt_U` TAKES `pays_29_name`**: the tables' field's own
form (KeepsAt) at the row's number, under `pays_29_name`'s premises and q₂. (The number is
K12AtField.lean's term; it is 9 by
StepSide2.lean's
`table_eight`.) -/
theorem keeps_29_name {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (hD : (Fk X N P).data "key file" = .ok D) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z) (n : ℕ)
    (hidx : n = 1 + ((K12SeatsAt.tableBlocks X P).length + 0)) (r : Fmt.M1.Stage → ℕ) (lo : ℕ)
    (hlo : lo = 6) (num : Fmt.TreeSource → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hrow : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base ds back (rest₂ n ds)) →
      ∃ dB dt, ds = dB :: dt ∧ back = [])
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed29 P D r lo num base dB dt (rest₂ n (dB :: dt)))
    (q₂ : (Key.descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂) :
    LPFD.KeepsAt (on9 X N P D tab enc rad off₂)
      (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad)
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂) n := by
  subst hidx
  exact K12AtField.keepsAt_U X N P D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
    (on9 X N P D tab enc rad off₂)
    (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) q₂
    (pays_29_name X N P D tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX
      hL hN hp hw hD DK hD₀ hDK hoffN _ (by rw [StepSide2.table_eight X N P hp]) r lo hlo num rdN
      oNo mem rd hrd ho0 ho3 hmem0 hmem3 hrow owed)

/-- **What is owed at the row when K12PlaceAtName.lean's payers at the place are called**: three
fields, each at the look-up's own piece. r := the planner's radii at the place · num := the file's
numbering of the shared chain's trees · lo := its first tree's number. -/
structure Owed29P {W : Type} (base : ℕ) (dB : RDT) (dt : List RDT)
    (x' : Rest (ckP .two) (fr₂ D) (P₂ × St₂) W (dB :: dt)) : Prop where
  /-- owed (K12's files': atPlace_tile₂ at the row's own piece) -/
  place : AtPlace (fr₂ D) (pi9 P) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => H2K.Member.rKUFull s.st) base dB dt (errJ (pi9 P) H2K.Member.rKUFull dt)
  /-- owed (K12's files': labelsPub_own) -/
  labels : LabelsPub (pi9 P) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1)
    (nlAt (pi9 P) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0))) base
  /-- owed (K12's files': where the row's errors are the cap) -/
  cap : Err.le ((batV0 (pi9 P) H2K.Member.rKUFull * (bsRound .two dB.entry dB.kind).w,
    errJ (pi9 P) H2K.Member.rKUFull dt) : Err (uLT (ckP .two) (dB :: dt))) x'.err

/-- **`pays_29_name` AT THE SEAT's LETTERS, WITH SEVEN OF `Owed29`'s TEN CALLED**
(K12PlaceAtName.lean): D is the written data at the frame's depth · r := rKUFull · lo = 6 by
`lo_six` · pins ⇐ `pins₂` · joh ⇐ `joh_29` · batOne ⇐ `batOne_29` · fit0 | fit3 ⇐ `fit0_29` |
`fit3_29` · ft ⇐
`ft_29` ·
stageZ ⇐ `stageZ_29`. NEW BINDERS: hasks (the yes of every test that the key file's laws ask: the
seat hands it) · q₁ q₂ q₃. LEFT: hrow · `Owed29P` (place · labels · cap). -/
theorem pays_29_seat {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : OnBytes.Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) (n : ℕ)
    (hn : n = 9) (rdN : ℕ → ℕ) (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hrow : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base ds back (rest₂ n ds)) →
      ∃ dB dt, ds = dB :: dt ∧ back = [])
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base (dB :: dt) [] (rest₂ n (dB :: dt))) →
      Owed29P X N P D base dB dt (rest₂ n (dB :: dt))) :
    ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base ds back (rest₂ n ds)) →
      Pays (fr₂ D) (pi9 P) (fun s t => Seat.enter (·.gU) (·.firstMask) s = .ok t)
        (fun s t s' => Seat.leave s t = .ok s') (held (B9 P))
        (on9 X N P D tab enc rad off₂)
        (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) n base ds back
        (rest₂ n ds) := by
  subst hDD
  subst hn
  exact pays_29_name X N P _ tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
    hX hL hN hp hw hD₀ DK hD₀ hDK hoffN 9 rfl H2K.Member.rKUFull _
    (K12PlaceAtName.lo_six hZ hP hm hL X N hp hasks) _ rdN oNo mem rd hrd ho0 ho3 hmem0 hmem3 hrow
    fun base dB dt hl =>
      { pins := K12PlaceAtName.pins₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
          hX hp hw hDK q₁ q₂ q₃ 9 _ hl
        place := (owed base dB dt hl).place
        joh := K12PlaceAtName.joh_29 hZ hP hm hL X N hp
        batOne := K12PlaceAtName.batOne_29 X N P hp
        labels := (owed base dB dt hl).labels
        cap := (owed base dB dt hl).cap
        fit0 := K12PlaceAtName.fit0_29 hZ hP hm hL X N hp
        fit3 := K12PlaceAtName.fit3_29 hZ hP hm hL X N hp
        ft := K12PlaceAtName.ft_29 hL X N hp
        stageZ := K12PlaceAtName.stageZ_29 hZ hP hm hL X N hp }

/-- A look-up at an equal index. (A «rw» does not find the index where the list's type is written in
another, equal, way.) -/
theorem get_at {α : Type _} (l : List α) {i j : ℕ} (e : i = j) {x : α} (h : l[i]? = some x) :
    l[j]? = some x := e ▸ h

/-- **`Pays` AT ROW 2.9 WITH NOTHING OWED**: `pays_29_seat` with hrow AND `Owed29P` PAID by
`place_29` (the stretch is dB :: dt · AtPlace · the labels · the cap) and `row_cut₂`
(nothing is put behind). BINDERS: the seat's own (hZ hP hm hX hp hw · DK hD₀ hDK · hL · hN · hasks)
· hDD · hoffN ·
the
chains' heads q₁ q₂ q₃ · n hn · hcap («the row's errors are the cap at 128»: rfl at capRest) · the
filler's nine. FIRST LIMIT: NO EXAMPLE SHOWS THAT THESE CAN BE MET TOGETHER; it stands on every file
beneath it.
-/
theorem pays_29_full {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : OnBytes.Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) (n : ℕ)
    (hn : n = 9) (rdN : ℕ → ℕ) (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hcap : ∀ ds, (rest₂ n ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (B9 P)) base ds back (rest₂ n ds)) →
      Pays (fr₂ D) (pi9 P) (fun s t => Seat.enter (·.gU) (·.firstMask) s = .ok t)
        (fun s t s' => Seat.leave s t = .ok s') (held (B9 P))
        (on9 X N P D tab enc rad off₂)
        (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) n base ds back
        (rest₂ n ds) := by
  subst hDD
  subst hn
  have hlen : 9 = (H2K.JointK.keySharedPre X.chains P).length :=
    ((H2K.JointK.keySharedPre_length X.chains P).trans
      (by rw [show (_root_.Desc.K14.blocksOr
        (Key.sharedPar X.chains (Key.beforeSharedPoint P))).length = 8 from
          StepSide2.table_eight X N P hp])).symm
  have P29 := K12PlaceAtName.place_29 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
    hL hp hD₀ hasks q₂ 9 hlen
  obtain ⟨b', post', eb⟩ := H2K.JointK.key_shared_behind X.chains P
  have hfl : (Fk X N P).shared.blocksInOrder =
      H2K.JointK.keySharedPre X.chains P ++ H2K.JointK.keyGu P :: b' :: post' := by
    rw [← eb]
    exact H2K.JointK.key_shared_flat X N P
  exact pays_29_seat X N P _ tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm
    hX hL hN hp hw DK rfl hD₀ hDK hasks hoffN q₁ q₂ q₃ 9 rfl rdN oNo mem rd hrd ho0 ho3 hmem0 hmem3
    (fun base ds back hl => by
      obtain ⟨dB, dt, e, _⟩ := P29 _ hl
      exact ⟨dB, dt, e, (K12PlaceAtName.row_cut₂ (Fk X N P) _ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd (H2K.JointK.keySharedPre X.chains P) (H2K.JointK.keyGu P) b' post'
        (q₂.symm.trans hfl) _ (get_at _ hlen hl)).2.1⟩)
    (fun base dB dt hl => by
      obtain ⟨dB', dt', e, _, hA, hLb, hC⟩ := P29 _ hl
      obtain ⟨rfl, rfl⟩ := List.cons.inj e
      exact ⟨hA, hLb, by rw [hcap]; exact hC⟩)

/-- **THE TABLES' FIELD's OWN FORM AT THE ROW, WITH NOTHING OWED**: `keepsAt_U` (K12AtField.lean)
over `pays_29_full`: KeepsAt at `on9` (the invariant, and at border 9 the history). The join of
`on9` with the tables' On₂′ is other files' to show. -/
theorem keeps_29_full {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : OnBytes.Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (hoffN : ∀ z, off₂ z = LPFD.off₂N z) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) (n : ℕ)
    (hidx : n = 1 + ((K12SeatsAt.tableBlocks X P).length + 0)) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ) (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x u part i, rd x u part i = tabP csKey (x.1.l.get x.2).1 u part i)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hcap : ∀ ds, (rest₂ n ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    LPFD.KeepsAt (on9 X N P D tab enc rad off₂)
      (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad)
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂) n := by
  subst hidx
  exact K12AtField.keepsAt_U X N P D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
    (on9 X N P D tab enc rad off₂)
    (Cl₂ X N P D (LPFD.baseAt X decN recBack) atSix (readAt tab) enc rad) q₂
    (pays_29_full X N P D tab enc rad off₂ c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX
      hL hN hp hw DK hDD hD₀ hDK hasks hoffN q₁ q₂ q₃ _ (by rw [StepSide2.table_eight X N P hp]) rdN
      oNo mem rd hrd ho0 ho3 hmem0 hmem3 hcap)

/-- **`Owed29` ITSELF, PAID, IN THE ∀-FORM THAT THE LINE AT THE NAME CALLS**:
at whatever the row's
look-up gives: at r := rKUFull · lo := 6 · num := the file's numbering of the shared chain's trees.
By K12PlaceAtName.lean alone (`place_29` · `pins₂` · `joh_29` · `batOne_29` ·
`fit0_29` | `fit3_29` · `ft_29` · `stageZ_29` · `lo_six`). hcap: rfl at capRest. -/
theorem owed_29 {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (DK : WholeD) (hDD : D = DK.at OnBytes.Slice.frS.P.T.a)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
    (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
    {X₀ : OnBytes.Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hcap : ∀ ds, (rest₂ 9 ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc (Key.descriptionFromSource X N P) (piecesAt (ckP .two) (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
                           rest₂ rest₃ dW wEnd)).l₂)[9]? =
        some (pieceOf (held (B9 P)) base (dB :: dt) [] (rest₂ 9 (dB :: dt))) →
      Owed29 P D H2K.Member.rKUFull 6 (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1) base dB dt
        (rest₂ 9 (dB :: dt)) := by
  subst hDD
  intro base dB dt hl
  have hlen : 9 = (H2K.JointK.keySharedPre X.chains P).length :=
    ((H2K.JointK.keySharedPre_length X.chains P).trans
      (by rw [show (_root_.Desc.K14.blocksOr
        (Key.sharedPar X.chains (Key.beforeSharedPoint P))).length = 8 from
          StepSide2.table_eight X N P hp])).symm
  obtain ⟨dB', dt', e, _, hA, hLb, hC⟩ := K12PlaceAtName.place_29 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁
    rest₂ rest₃ dW wEnd hZ hP hm hL hp hD₀ hasks q₂ 9 hlen _ hl
  obtain ⟨rfl, rfl⟩ := List.cons.inj e
  rw [K12PlaceAtName.lo_six hZ hP hm hL X N hp hasks] at hLb
  exact
    { pins := K12PlaceAtName.pins₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX
        hp hw hDK q₁ q₂ q₃ 9 _ hl
      place := hA
      joh := K12PlaceAtName.joh_29 hZ hP hm hL X N hp
      batOne := K12PlaceAtName.batOne_29 X N P hp
      labels := hLb
      cap := by rw [hcap]; exact hC
      fit0 := K12PlaceAtName.fit0_29 hZ hP hm hL X N hp
      fit3 := K12PlaceAtName.fit3_29 hZ hP hm hL X N hp
      ft := K12PlaceAtName.ft_29 hL X N hp
      stageZ := K12PlaceAtName.stageZ_29 hZ hP hm hL X N hp }

end Johnson.RunOne.Law.K12Pays29Name

#print axioms Johnson.RunOne.Law.K12Pays29Name.pays_29_name
#print axioms Johnson.RunOne.Law.K12Pays29Name.keeps_29_name
#print axioms Johnson.RunOne.Law.K12Pays29Name.pays_29_seat
#print axioms Johnson.RunOne.Law.K12Pays29Name.pays_29_full
#print axioms Johnson.RunOne.Law.K12Pays29Name.keeps_29_full
#print axioms Johnson.RunOne.Law.K12Pays29Name.owed_29
