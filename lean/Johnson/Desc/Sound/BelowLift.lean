-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BelowLift.lean: A SEAT'S BLOCK AT A DESCRIPTION: the description's own block,
lifted to the pair of what was handed to the chain and the chain's own record; and a member of
`KeyCoreAtDesc`'s premises (Johnson/Desc/Sound/KeyAtDesc.lean).

The setting. `OfDesc` (Johnson/Desc/Sound/DescThree.lean) asks that the pieces hold the blocks
`(below b₀).lift Prod.snd …`: the test below the prime inside, the lifting outside. A row of seats
(`SL.pieces`, Johnson/Desc/Sound/KeyDecides.lean) makes pieces that hold `below b`: the test
outside. At b := b₀ lifted the two meet only by an equation of blocks.

What is said.
  `below_lift`: `below (b₀.lift get set) = (below b₀).lift get set`.
  `liftP`: a block typed at the chain's own record S₀, as a block at P × S₀. `decideLaw_lift`: THE
    ONE LAW OF A LIFTED BLOCK, FROM A LAW IN THE WORDS OF THE KIND'S OWN BLOCK b₀: at every p : P:
    if `b₀.decide` returns s', the next invariant holds of ((p, s'), the oracles left), and the
    typed verifier puts out the reading of it.
  `chainEnd_lift`: a chain's last block, lifted, IS the chain's last block at the pair, its clauses
    read at the second part.
  `DescToy`: a description of a key file over `Toy.kc`: each chain has a quiet first block and one
    block more, its last: the first chain's is the chains' end's own text, sealed; the shared
    chain's the same, not sealed; the second chain's says yes just where the record's answer is
    `true`. `DescToy.ofDesc`, `DescToy.toy_keyCore`: `OfDesc` AND
    THE THREE EQUATIONS OF PIECES HOLD TOGETHER, with every other premise of `KeyCoreAtDesc`: so
    `KeyCore` at `F.run` there. `DescToy.says_yes`, `says_no`: `F.run` says yes at the record inside
    the language and no at the other.

Limits. The toy has no written round but the seal that is put back, no error and no tree.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyAtDesc
import Johnson.Desc.Sound.KeyJoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.ChainEnd
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString extNone)

variable {S₀ Cl : Type}

/-- **The test below the prime and the lifting may change places.** -/
theorem below_lift {T : Type} (get : T → S₀) (set : T → S₀ → T) (b : Block S₀ Cl) :
    below (b.lift get set) = (below b).lift get set := by
  have hd : (below (b.lift get set)).decide = ((below b).lift get set).decide := by
    funext t rs gs
    show (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then
        (b.decide (get t) rs gs).map (set t) else .error "a word is not below the prime") =
      (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide (get t) rs gs
        else .error "a word is not below the prime").map (set t)
    split <;> rfl
  calc below (b.lift get set)
      = { b.lift get set with decide := (below (b.lift get set)).decide } := rfl
    _ = { b.lift get set with decide := ((below b).lift get set).decide } := by rw [hd]
    _ = (below b).lift get set := rfl

/-- A block typed at the chain's own record, as a block at the pair of what was handed to the chain
and that record. -/
abbrev liftP (P : Type) (b : Block S₀ Cl) : Block (P × S₀) Cl :=
  b.lift Prod.snd fun t s => (t.1, s)

/-- **The one law of a lifted block, from a law in the words of the kind's own block.** -/
theorem decideLaw_lift {P : Type} {F : Frame} (b : Block S₀ Cl) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) {A B : JK} (k : BK A B) (M : Maps ds k.R.red.shape)
    (rdA : (P × S₀) × F.E.Str → A.X × A.E.Str) (rdB : (P × S₀) × F.E.Str → B.X × B.E.Str)
    (iA iB : (P × S₀) × F.E.Str → Prop)
    (h : ∀ (p : P) (s s' : S₀) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds)),
      A.on (rdA ((p, s), y)) → iA ((p, s), y) →
      sTests (ckP .two) (stg F base ds) y τ = true →
      viewWordsBelowPrime (sView (ckP .two) (stg F base ds) y τ) = true →
      Shown F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened →
      b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
        (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
          (sView (ckP .two) (stg F base ds) y τ).opened) = .ok s' →
      iB ((p, s'), (y.1, sLeft (ckP .two) (stg F base ds) y τ)) ∧
        k.R.red.out (rdA ((p, s), y)) (M.view τ) =
          some (rdB ((p, s'), (y.1, sLeft (ckP .two) (stg F base ds) y τ)))) :
    DecideLaw (liftP P b) base ds back k M rdA rdB iA iB := by
  rintro ⟨p, s⟩ t' y τ ha hi h1 hw h2 h3
  have h3' : (b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened)).map (fun s' => (p, s')) = .ok t' := h3
  cases hd : b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened) with
  | error e =>
    rw [hd] at h3'
    cases h3'
  | ok s' =>
    rw [hd] at h3'
    have e : (Except.ok (p, s') : Except String (P × S₀)) = .ok t' := h3'
    cases e
    exact h p s s' y τ ha hi h1 hw h2 hd

/-- **A chain's last block, lifted, is the chain's last block at the pair.** -/
theorem chainEnd_lift (P : Type) (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S₀ → Clauses) :
    liftP P (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks) =
      ChainEnd.chainEnd chain piece sealed inFront fun t : P × S₀ => asks t.2 := by
  have hd : (liftP P (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks)).decide =
      (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront
        fun t : P × S₀ => asks t.2).decide := by
    funext t rs gs
    show ((refuse (asks t.2)).map fun _ => t.2).map (fun s => (t.1, s)) =
      (refuse (asks t.2)).map fun _ => t
    cases refuse (asks t.2) <;> rfl
  calc liftP P (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks)
      = { ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront (fun t : P × S₀ => asks t.2) with
          decide := (liftP P (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront
            asks)).decide } := rfl
    _ = { ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront (fun t : P × S₀ => asks t.2) with
          decide := (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront
            fun t : P × S₀ => asks t.2).decide } := by rw [hd]
    _ = ChainEnd.chainEnd chain piece sealed inFront fun t : P × S₀ => asks t.2 := rfl

/-! ## A member of `KeyCoreAtDesc`'s premises -/

namespace DescToy
open ListsToy (Rc kTest kTest_good tD)

/-- The second chain's one block: yes just where the record's answer is `true`. -/
def testB : Block Rc Unit :=
  roundlessBlock "test" 3 none 1 fun s => if s.2 then .ok s else .error "no"

/-- A chain's first block: quiet; it passes every record on. -/
def frontB (name : String) (chain : Nat) : Block Rc Unit := roundlessBlock name chain none 0 .ok

/-- **The toy's description.** The public part is the instance; each chain's own record is the
instance. Each chain has a quiet first block and one block more, its last. -/
def F : FileDescription Rc where
  S₁ := Rc
  S₂ := Rc
  S₃ := Rc
  Cl := Unit
  plans := ([⟨{ name := "SEAL" }, [], []⟩], [], [])
  tableDepth := 0
  fileOk := true
  okStart := fun _ => true
  XiPub := Rc
  pub := id
  start₁ := id
  start₂ := id
  start₃ := fun p _ _ => .ok p
  wanted := []
  owed := []
  first := ⟨frontB "front 1" 1, [], [], [], ChainEnd.chainEnd 1 1 true [] fun _ => []⟩
  shared := ⟨frontB "front 2" 2, [], [], [], ChainEnd.chainEnd 2 1 false [] fun _ => []⟩
  second := ⟨frontB "front 3" 3, [], [], [], testB⟩
  fin := fun _ _ _ _ => true

/-- A block as `Chain.blocksInOrder` lays it. -/
abbrev bareOf (b : Block Rc Unit) : Block Rc Unit := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- The three flat lists' two blocks each. -/
abbrev q₁ : Block Rc Unit := bareOf (frontB "front 1" 1)
abbrev q₂ : Block Rc Unit := bareOf (frontB "front 2" 2)
abbrev q₃ : Block Rc Unit := bareOf (frontB "front 3" 3)
abbrev b₁ : Block Rc Unit := bareOf (ChainEnd.chainEnd 1 1 true [] fun _ => [])
abbrev b₂ : Block Rc Unit := bareOf (ChainEnd.chainEnd 2 1 false [] fun _ => [])
abbrev b₃ : Block Rc Unit := bareOf testB

abbrev Fr (k : ℕ → ℕ) (ft : ℕ) : Frame := frameAt (tD.at 0) [] k ft

/-- The readings: the instance out of the first part; the stored table. -/
def rd₁ (a : (Rc × Rc) × (Fr id 0).E.Str) : Rc × Toy.kc.conf.E0.Str := (a.1.1, a.2.1)
def rd₂ (a : ((Rc × Rc) × Rc) × (Fr id 0).E.Str) : Rc × Toy.kc.conf.E0.Str := (a.1.1.1, a.2.1)
def rd₃ (a : ((Rc × Rc × Rc) × Rc) × (Fr id F.lastChainFirstTreeNumber).E.Str) : Rc × Toy.kc.conf.E0.Str :=
  (a.1.1.1, a.2.1)
def rdE (_ : ((Rc × Rc × Rc) × Rc) × (Fr id F.lastChainFirstTreeNumber).E.Str) : Unit × extNone.Str := ((), ())

/-- The third chain's invariant: the chain's own record is the instance. -/
def inv₃ (a : ((Rc × Rc × Rc) × Rc) × (Fr id F.lastChainFirstTreeNumber).E.Str) : Prop := a.1.2 = a.1.1.1

def L₁ : SL (Rc × Rc) Unit (Fr id 0) (jWf Toy.kc.conf) (jWf Toy.kc.conf) :=
  .cons rd₁ (fun _ => True) (liftP Rc q₁) 0 [] [] (BK.pass _) .nil
    (.cons rd₁ (fun _ => True) (liftP Rc b₁) 0 [] [sealRound] (BK.pass _) .nil
      (.nil rd₁ fun _ => True))
def L₂ : SL ((Rc × Rc) × Rc) Unit (Fr id 0) (jWf Toy.kc.conf) (jWf Toy.kc.conf) :=
  .cons rd₂ (fun _ => True) (liftP (Rc × Rc) q₂) 0 [] [] (BK.pass _) .nil
    (.cons rd₂ (fun _ => True) (liftP (Rc × Rc) b₂) 0 [] [] (BK.pass _) .nil
      (.nil rd₂ fun _ => True))
def L₃ : SL ((Rc × Rc × Rc) × Rc) Unit (Fr id F.lastChainFirstTreeNumber) (jWf Toy.kc.conf) jEnd :=
  .cons rd₃ inv₃ (liftP (Rc × Rc × Rc) q₃) 0 [] [] (BK.pass _) .nil
    (.cons rd₃ inv₃ (liftP (Rc × Rc × Rc) b₃) 0 [] [] kTest .nil (.nil rdE fun _ => True))

/-- The three rows of pieces: the seats' own. -/
def T : ThreeAt (ckP .two) (tD.at 0) [] F Unit Unit Unit where
  ft₁ := 0
  ft₂ := 0
  ft₃ := F.lastChainFirstTreeNumber
  p₁ := seatPiece Unit (liftP Rc q₁) 0 [] [] (BK.pass (jWf Toy.kc.conf)) .nil
  l₁ := [seatPiece Unit (liftP Rc b₁) 0 [] [sealRound] (BK.pass (jWf Toy.kc.conf)) .nil]
  p₂ := seatPiece Unit (liftP (Rc × Rc) q₂) 0 [] [] (BK.pass (jWf Toy.kc.conf)) .nil
  l₂ := [seatPiece Unit (liftP (Rc × Rc) b₂) 0 [] [] (BK.pass (jWf Toy.kc.conf)) .nil]
  p₃ := seatPiece Unit (liftP (Rc × Rc × Rc) q₃) 0 [] [] (BK.pass (jWf Toy.kc.conf)) .nil
  l₃ := [seatPiece Unit (liftP (Rc × Rc × Rc) b₃) 0 [] [] kTest .nil]
  n₁ := "first"
  n₂ := "shared"
  n₃ := "second"
  in₁ := fun x => (x, x)
  out₁ := fun _ _ => ()
  in₂ := fun _ => ((((), true), ((), true)), ((), true))
  out₂ := fun _ _ => ()
  in₃ := fun _ => none
  fin := fun _ _ => true
  d := ()
  wEnd := ()

/-- **The pieces hold the description's own blocks**: by `below_lift`. -/
theorem ofDesc : OfDesc F T where
  ft₁ := rfl
  ft₂ := rfl
  ft₃ := rfl
  b₁ := congrArg₂ (fun x y => [x, y]) (below_lift _ _ q₁) (below_lift _ _ b₁)
  b₂ := congrArg₂ (fun x y => [x, y]) (below_lift _ _ q₂) (below_lift _ _ b₂)
  b₃ := congrArg₂ (fun x y => [x, y]) (below_lift _ _ q₃) (below_lift _ _ b₃)
  back₁ := rfl
  back₂ := rfl
  back₃ := rfl

theorem law₁ : L₁.Laws :=
  ⟨⟨BK.pass_good _, ⟨()⟩, trivial, rfl, decideLaw_lift q₁ 0 [] [] _ _ _ _ _ _
    fun p s s' y τ _ _ _ _ _ h => by
      have h' : (Except.ok s : Except String Rc) = .ok s' := h
      cases h'
      exact ⟨trivial, rfl⟩⟩,
   ⟨BK.pass_good _, ⟨()⟩, trivial, rfl, decideLaw_lift b₁ 0 [] [sealRound] _ _ _ _ _ _
    fun p s s' y τ _ _ _ _ _ h => by
      have h' : (Except.ok s : Except String Rc) = .ok s' := h
      cases h'
      exact ⟨trivial, rfl⟩⟩, trivial⟩

theorem law₂ : L₂.Laws :=
  ⟨⟨BK.pass_good _, ⟨()⟩, trivial, rfl, decideLaw_lift q₂ 0 [] [] _ _ _ _ _ _
    fun p s s' y τ _ _ _ _ _ h => by
      have h' : (Except.ok s : Except String Rc) = .ok s' := h
      cases h'
      exact ⟨trivial, rfl⟩⟩,
   ⟨BK.pass_good _, ⟨()⟩, trivial, rfl, decideLaw_lift b₂ 0 [] [] _ _ _ _ _ _
    fun p s s' y τ _ _ _ _ _ h => by
      have h' : (Except.ok s : Except String Rc) = .ok s' := h
      cases h'
      exact ⟨trivial, rfl⟩⟩, trivial⟩

theorem law₃ : L₃.Laws :=
  ⟨⟨BK.pass_good _, ⟨()⟩, trivial, rfl, decideLaw_lift q₃ 0 [] [] _ _ _ _ _ _
    fun p s s' y τ _ hi _ _ _ h => by
      have h' : (Except.ok s : Except String Rc) = .ok s' := h
      cases h'
      exact ⟨hi, rfl⟩⟩,
   ⟨kTest_good, ⟨()⟩, trivial, rfl, decideLaw_lift b₃ 0 [] [] _ _ _ _ _ _
    fun p s s' y τ _ hi _ _ _ h => by
      have hi' : s = p.1 := hi
      obtain ⟨u, b⟩ := s
      cases b with
      | false => cases h
      | true =>
        refine ⟨trivial, ?_⟩
        show ((if p.1.2 then some () else none).map fun xo => (xo, ())) = some ((), ())
        rw [← hi']
        rfl⟩, trivial⟩

theorem quietTiled' {S : Type} {Fm : Frame} (b : Block S Unit) (back : List Fmt.RoundView)
    (hb : back.length = b.rounds.length)
    (hr : ∀ ds, ((b.reads Fm.ft ds).flatMap id).length = 0) {A B : JK} (k : BK A B)
    (M : Maps [] k.R.red.shape) : Tiled (seatPiece (F := Fm) Unit b 0 [] back k M) [] :=
  ⟨⟨by show 0 + back.length = b.rounds.length; omega, fun _ _ => hr _⟩,
    ⟨fun n sh h => (by cases h), fun d hd => (by cases hd)⟩⟩

theorem fits : (atDesc F T).Fits :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨(quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil).1,
      (quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil).2, rfl, rfl,
      quietTiled' _ _ rfl (fun ds => by cases ds <;> rfl) (BK.pass (jWf Toy.kc.conf)) .nil⟩,
    ⟨(quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil).1,
      (quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil).2, rfl, rfl,
      quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil⟩,
    ⟨(quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil).1,
      (quietTiled' _ _ rfl (fun _ => rfl) (BK.pass (jWf Toy.kc.conf)) .nil).2, rfl, rfl,
      quietTiled' _ _ rfl (fun _ => rfl) kTest .nil⟩⟩

/-- **The rule at the toy's description**: every premise of `KeyCoreAtDesc` is met. -/
theorem toy_keyCore (TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3)
    (silK : Rc → TF → TJ → T3 → Bool) (εs : ℝ≥0∞) :
    KeyCore Toy.kc tD tF tJ t3 silK F.run 1 εs :=
  keyCoreAtDesc 0 Toy.kc tD TF TJ T3 tF tJ t3 silK [] Unit Unit Unit F T (jWf Toy.kc.conf)
    (jWf Toy.kc.conf) jEnd L₁ L₂ L₃ εs ofDesc rfl rfl rfl fits law₁ law₂ law₃
    (fun _ _ => ⟨rfl, trivial⟩) (fun _ => ⟨rfl, fun _ => trivial⟩)
    (fun b s h => by
      have h' : (Except.ok b.1.1.1 : Except String Rc) = .ok s := h
      cases h'
      exact ⟨rfl, fun _ => rfl⟩)
    (fun _ _ _ => ⟨(), trivial⟩) ListsToy.rowFit ⟨trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩

/-- The description's own decision says yes at the record inside the language. -/
theorem says_yes : F.run ((), true) ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ = true := by decide

/-- It says no at the other. -/
theorem says_no : F.run ((), false) ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ = false := by decide

end DescToy

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.DescToy.ofDesc
#print axioms VerifiableInference.Desc.Sound.DescToy.toy_keyCore
#print axioms VerifiableInference.Desc.Sound.DescToy.says_yes
#print axioms VerifiableInference.Desc.Sound.DescToy.says_no
#print axioms VerifiableInference.Desc.Sound.below_lift
#print axioms VerifiableInference.Desc.Sound.decideLaw_lift
#print axioms VerifiableInference.Desc.Sound.chainEnd_lift
