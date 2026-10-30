-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PassLaw.lean: THE ONE LAW OF A BLOCK (`DecideLaw`,
Johnson/Desc/Sound/KeyDecides.lean) MET BY A REAL BLOCK: the last block of a chain, in its file's
own text; and a toy that meets every premise of `KeySoundOfDecides` with a verifier that accepts.

What is said.
  `passLaw`: every block whose `decide` hands the record on meets the law at the typed block that
    hands its statement on (`KObj.BK.pass`), all its rounds skipped (`Maps.skips`), at every joint
    and every reading and invariant that read no tree from the block's place on.
  `chainEnd_law`: so does `ChainEnd.chainEnd` (Johnson/Desc/ChainEnd.lean). `chainEnd_law_asks`:
    and behind it the invariant holds besides that the record has passed the chain's own clauses.
    `endSeat`: a chain's last block laid at the end of a row (`SL`); `endSeat_laws`, `endSeat_held`:
    all that the rule asks of that seat holds, at every εs: a chain's end costs nothing.
  `DecidesToy`: the toy of Johnson/Desc/Sound/TypedListsToy.lean at this rule: `toy_keySound`;
    `says_yes`, `says_no`.

Limits. The toy has no round, no error and no tree.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyDecides
import Johnson.Desc.Sound.ChainEndTie
import Johnson.Desc.Sound.TypedListsToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open VerifiableInference.Desc.ChainEnd
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString extNone)

variable {S Cl : Type} {F : Frame}

/-- **A block whose `decide` hands the record on meets the law at the typed block that hands its
statement on.** -/
theorem passLaw (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop)
    (hnd : (F.all.map (·.no)).Nodup) (hrd : ReadsBelow base rd) (hinv : ReadsBelow base inv)
    (hb : ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s) :
    DecideLaw b base ds back (BK.pass A) (Maps.skips ds) rd rd inv inv := by
  intro s s' y τ _ hi _ _ _ h
  obtain rfl : s' = s := hb _ _ _ _ h
  have e : rd (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) = rd (s', y) :=
    hrd s' _ _ rfl fun q hq => sLeft_old hnd ds base y τ q hq
  have e' : inv (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) = inv (s', y) :=
    hinv s' _ _ rfl fun q hq => sLeft_old hnd ds base y τ q hq
  rw [e, e']
  exact ⟨hi, rfl⟩

/-- **A chain's last block meets the law.** -/
theorem chainEnd_law (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop)
    (hnd : (F.all.map (·.no)).Nodup) (hrd : ReadsBelow base rd) (hinv : ReadsBelow base inv) :
    DecideLaw (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks) base ds back
      (BK.pass A) (Maps.skips ds) rd rd inv inv :=
  passLaw _ base ds back A rd inv hnd hrd hinv fun s rs gs s' h =>
    ((chainEnd_decide_iff chain piece sealed inFront asks s s' rs gs).1 h).1

/-- **What a chain's last block buys**: behind it the carried record has passed every one of the
chain's own clauses: an invariant that later seats, the seam and the last premise of the rule can
lean on. -/
theorem chainEnd_law_asks (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop)
    (hnd : (F.all.map (·.no)).Nodup) (hrd : ReadsBelow base rd) (hinv : ReadsBelow base inv) :
    DecideLaw (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks) base ds back
      (BK.pass A) (Maps.skips ds) rd rd inv (fun a => inv a ∧ ∀ c ∈ asks a.1, c.2 = true) := by
  intro s s' y τ ha hi h1 hw h2 h
  obtain ⟨rfl, hc⟩ := (chainEnd_decide_iff chain piece sealed inFront asks s s' _ _).1 h
  obtain ⟨e1, e2⟩ := chainEnd_law chain piece sealed inFront asks base ds back A rd inv hnd hrd
    hinv s' s' y τ ha hi h1 hw h2 h
  exact ⟨⟨e1, hc⟩, e2⟩

/-- A chain's last block, laid as the last seat of a row. -/
def endSeat (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound) (asks : S → Clauses)
    (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop) : SL S Cl F A A :=
  .cons rd inv (ChainEnd.chainEnd chain piece sealed inFront asks) base ds back (BK.pass A)
    (Maps.skips ds) (.nil rd inv)

theorem endSeat_laws (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop) (hW : Nonempty A.W)
    (hnd : (F.all.map (·.no)).Nodup) (hrd : ReadsBelow base rd) (hinv : ReadsBelow base inv)
    (hback : viewWordsBelowPrime ⟨back, []⟩ = true) :
    (endSeat (Cl := Cl) chain piece sealed inFront asks base ds back A rd inv).Laws :=
  ⟨⟨BK.pass_good A, hW, Maps.ok_skips ds, hback,
    chainEnd_law chain piece sealed inFront asks base ds back A rd inv hnd hrd hinv⟩, trivial⟩

theorem endSeat_held (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop) (εs : ℝ≥0∞) :
    (endSeat (Cl := Cl) chain piece sealed inFront asks base ds back A rd inv).Held εs :=
  ⟨Maps.held_skips εs ds, trivial⟩

/-! ## The toy -/

namespace DecidesToy
open ListsToy

abbrev Fr (k : ℕ → ℕ) : Frame := frameAt (tD.at 0) [] k 0

def L₁ : SL Rc Unit (Fr id) (jWf Toy.kc.conf) (jWf Toy.kc.conf) :=
  .cons rdW (fun _ => True) passB 0 [] [] (BK.pass _) .nil (.nil rdW fun _ => True)
def L₃ : SL Rc Unit (Fr id) (jWf Toy.kc.conf) jEnd :=
  .cons rdW (fun _ => True) testB 0 [] [] kTest .nil (.nil rdE fun _ => True)

/-- The toy's three chains: the pieces are the rows' own. -/
def T : Three (ckP .two) (tD.at 0) [] Rc Rc Rc Rc Rc Rc Unit Unit :=
  { ListsToy.T with
    p₁ := seatPiece Unit passB 0 [] [] (BK.pass (jWf Toy.kc.conf)) .nil
    p₂ := seatPiece Unit passB 0 [] [] (BK.pass (jWf Toy.kc.conf)) .nil
    p₃ := seatPiece Unit testB 0 [] [] kTest .nil }

theorem law₁ : L₁.Laws :=
  ⟨⟨BK.pass_good _, ⟨()⟩, trivial, rfl, fun s s' y τ _ _ _ _ _ h => by
    have h' : (Except.ok s : Except String Rc) = .ok s' := h
    cases h'
    exact ⟨trivial, rfl⟩⟩, trivial⟩

theorem law₃ : L₃.Laws :=
  ⟨⟨kTest_good, ⟨()⟩, trivial, rfl, fun s s' y τ _ _ _ _ _ h => by
    obtain ⟨u, b⟩ := s
    cases b with
    | false => cases h
    | true => exact ⟨trivial, rfl⟩⟩, trivial⟩

theorem fits : T.Fits :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, ListsToy.quietTiled _ rfl _, ListsToy.quietTiled _ rfl _,
    ListsToy.quietTiled _ rfl _⟩

theorem says_yes : runRow T.run₁ T.run₂ T.run₃ ((), true) ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ = true := rfl
theorem says_no : runRow T.run₁ T.run₂ T.run₃ ((), false) ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ = false := rfl

/-- **The rule at the toy**: all its premises are met, at every wire whose key file's request tree
has one leaf. -/
theorem toy_keySound (DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Rc → TFk → TJk → T3k → Bool)
    (silP : Toy.kc.conf.X × Rc → TFp → TJp → T3p → Bool)
    (runP : Toy.kc.conf.X × Rc → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Rc 0) (N : ℕ) (early : Toy.kc.conf.X → Toy.kc.conf.X) (late : Option ℕ)
    (P : (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK (runRow T.run₁ T.run₂ T.run₃) silP
      runP eL N early late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK
                                      (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK
                                       (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (hdep : Tl.W.depthReqT = 0) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK
                                                               (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P Tl U) :=
  keySoundOfDecides 0 Toy.kc tD DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL
    N early late [] Rc Rc Rc Rc Rc Unit Unit T (jWf Toy.kc.conf) (jWf Toy.kc.conf) jEnd L₁ L₁ L₃ P
    Tl U rfl rfl rfl fits law₁ law₁ law₃ (fun _ _ => ⟨rfl, trivial⟩)
    (fun _ _ => ⟨rfl, fun _ => trivial⟩)
    (fun _ _ _ h => by
      obtain rfl := Option.some.inj h
      exact ⟨rfl, fun _ => trivial⟩)
    (fun _ _ _ _ _ => ⟨(), trivial⟩)
    ListsToy.rowFit hdep ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩

end DecidesToy

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.passLaw
#print axioms VerifiableInference.Desc.Sound.chainEnd_law
#print axioms VerifiableInference.Desc.Sound.chainEnd_law_asks
#print axioms VerifiableInference.Desc.Sound.endSeat_laws
#print axioms VerifiableInference.Desc.Sound.endSeat_held
#print axioms VerifiableInference.Desc.Sound.DecidesToy.says_yes
#print axioms VerifiableInference.Desc.Sound.DecidesToy.says_no
#print axioms VerifiableInference.Desc.Sound.DecidesToy.toy_keySound
