-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeAtWider.lean: THE LEMMA AT LETTERS ON "THE HONEST SIDE IS ACCEPTED"
(completeOn_home_join, Johnson/Goal/Conditions/HomeComplete.lean) CALLED AT A WRITTEN MEMBER OF
theWider (Johnson/Goal/Conditions/WiderAtThe.lean): CompleteOn of the goals' own system at that
member, on the domain CanServe, at a number α, UNDER NAMED PREMISES.

THE CIRCLE, AND HOW IT IS CUT. The lemma's letters H are seated at an argument system and a told
record. At a member of theWider both are built of K; and K's prover is to be H's prover, which names
the told record. Here the told record is written WITHOUT THE LETTER K (homeT); the prover's program
is written
over it, at bare types (pfOf); K is homeCoins at that program
(Johnson/Goal/Conditions/WiderHome.lean), its coins listed by digits (homeK); and the told record of
every member IS homeT at the member's own number of coins (T_wider: by unfolding).

THE NUMBER OF COINS b AND THE GENERATOR gen ARE LETTERS up to the last theorem. At the closed number
(the product of the two lists' lengths) Lean's kernel ends in "deep recursion detected" wherever it
has to see that the input at that number and `R₀ Z` have one type of pads (the warning in the head
of Johnson/Goal/Conditions/WideDigits.lean). So every passage between the two inputs
is made at a letter b (backB, padB, fillB), and the closed b and gen come in by one application.

Main names.
  homeR b, homeT b   the compiler's input and the told record at b: no letter K.
  T_wider   the told record of every member of theWider is homeT at the member's number.
  part_homeT   ONE READING: the told part of the public reading's value at a hash function is that
    function's answer at configString Z: the digest that the coins' algorithm and verify()'s parser
    ask for.
  HomeArgs b   ALL THAT IS NOT CHOSEN HERE: strategies, caps, what the drawn numbers stand for, the
    prover's draw, the instance of a request, the carrier over the hash function, the printer, the
    sets outside which the accept laws hold, five numbers.
  pfOf, homeK, member, homeH   the prover's program; the honest side's letters; the member; the
    lemma's letters at it.
  sample_member, prove_member   THE LEMMA's FIELDS sample AND prove. The first by
    unfolding. The second in three
    steps (prove_record, Johnson/Goal/Conditions/WiderComplete.lean; prove_homeK; pd_member): as one
    "rfl" it ran into Lean's limit; pd_member is given 1,600,000 heartbeats, the functions that
    recurse over a program's tree held shut.
  pub_member, salts_member, commit_member   the lemma's pubNoCoin, pubAsks, spare; salts; commit:
    the last under hgen: the generator's number is that of the pair (the pads that ρ names, the
    salts that bear c).
  completeOn_member_of   the lemma called at the member, b and gen letters, commit a premise.
  committerCoinCountLessOne, namedGen   the closed number; the generator with that number: it names no letter K.
  completeOn_member   THE STATEMENT.

WHAT IS PROVED HERE of the lemma's premises: sample (by unfolding), prove (three steps) · pubNoCoin,
pubAsks, spare (the laws that binding takes as hypotheses: bindLaws_wider) · commit, salts (under
bytes) · law (law_member: lawFit_home, Johnson/Prover/At/HomeAt.lean). JoinRest's field wires is
proved by wires_member, for whoever builds JoinRest.
WHAT STAYS A PREMISE, BY NAME: bytes (the randomness holds as many bytes for each leaf as the plan's
salt has) · small · number · JoinRest (Johnson/Prover/Home/Letters.lean: JoinFits less commit and
salts): carry_det, wires, draw, acc, printed.

Limits. AT NO HONEST STRATEGY ARE THE PREMISES SHOWN TO BE MET TOGETHER AT THIS MEMBER: AT IDLE
LETTERS ALONE, AT A NUMBER THAT IS AT LEAST 3, WHERE THE STATEMENT BOUNDS NOTHING
(Johnson/Goal/Conditions/HomeIdle.lean, under its three clauses on the files (proved at the two
named sets' written copies: lastFits_idle_named, AtFullSide/Home/HomeAtNamed.lean), through
HomeLast.lean
and HomeEnd.lean): no strategy and no draw is written here; the printer is an argument here
(Johnson/Goal/Conditions/HomeEnd.lean lays one).
JoinRest's field "printed" ends in the verifier's yes: what is public on the files, the request,
what a printer asks of the strategies, and the run values live behind it. α is a letter. No budget
on the honest side's queries: this is not the goals' G3'pol, which also asks CompleteFor at every
output that can be served and meets the policy. This file proves none of the goals: it
proves CompleteOn, the goals' own definition, at a stand-in and under named premises
(completeOn_member), and DEFINES homeR, member and namedGen, in which results of this and of other
files conclude. WiderAtThe.lean's limits travel whole.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WiderHome
import Johnson.Goal.Conditions.WiderComplete
import Johnson.Goal.Conditions.HomeComplete
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields
import Johnson.Prover.At.HomeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.Prover (Strats Draw Raw Bads HomeLetters proveForm JoinRest LawFit SetsSmall alphaAll)
open TypedOracleCompiler.Compile.Batch (typedOracleFamily)
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier committerAtFixedCoins IsOther)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-! ## What names no letter K: at a number of coins b that is a letter -/

/-- The compiler's input at the number of coins b. TWO WRITTEN CONSTANTS stand in it: allZeroDigest (the
all-false digest) and the empty list []: public place-holders. -/
abbrev homeR (b : PublicFiles → ℕ) (Z : PublicFiles) : InnerCompilerInput := (flashProveDescription.reBound b).input Z allZeroDigest []

/-- **The told record at b: IT NAMES NO LETTER K**: its text names the written value
placeHolderCoins. -/
def homeT (b : PublicFiles → ℕ) (Z : PublicFiles) : LayoutsByPublicReading (homeR b Z) :=
  ((theTerms placeHolderCoins).T Z).reBound (b Z)

/-- **The told record of every member of theWider is that one, at the member's own number.** -/
theorem T_wider (K : TheCoins) (W : WiderCoins K) (Z : PublicFiles) :
    (theWiderTerms K W).T Z = homeT W.bound Z := rfl

/-- **One reading**: the told part of the public reading's value is the hash function's answer at
configString Z. -/
theorem part_homeT (b : PublicFiles → ℕ) (Z : PublicFiles) (hash : Hash) :
    (homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash)) = hash (configString Z) := by
  have h := reads_descriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀)
    allZeroDigest [] Z hash
  show (layoutsByPublicReadingAtDescriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀)
      allZeroDigest [] Z).part ((layoutsByPublicReadingAtDescriptionOfFields (dataAtFiles flashProveData)
                (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) allZeroDigest [] Z).Pub.det
                  fun _ => hash) = _
  rw [← h]
  unfold VerifierAndGoals.Fit.readBoth
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
  rfl

/-- The weights' matrix, the pads and the filling, read at the input at b: the passage from
`R₀ Z` is made here, b a letter (the warning on Lean's kernel in the head of WideDigits.lean). -/
def backB (b : PublicFiles → ℕ) (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    (homeR b Z).Index := backThe Z s w

def padB (b : PublicFiles → ℕ) (Z : PublicFiles) (r : (R₀ Z).protocol.EncodingRandomness) : (homeR b Z).protocol.EncodingRandomness := r

def fillB (b : PublicFiles → ℕ) (Z : PublicFiles) : (homeR b Z).LeafBody := placeHolderCoins.b₀ Z

/-! ## The arguments, the program, the member, the letters -/

/-- **All that is not chosen here.** -/
structure HomeArgs (b : PublicFiles → ℕ) (Rand : Type) (B N : ℕ) where
  /-- the type of the interactive provers' own coins: it may hang on the files -/
  Kap : PublicFiles → Type
  st : (Z : PublicFiles) → Strats (homeR b Z).protocol (Kap Z)
  capT : PublicFiles → ℕ → ℕ
  capL : PublicFiles → ℕ → ℕ
  capB : PublicFiles → ℕ → ℕ
  /-- what the sampler's number stands for -/
  ρOf : Fin (B + 1) → Rand
  /-- which pads, and which bytes for each leaf, the randomness names -/
  ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1)
  sb : Rand → ℕ → ByteArray
  /-- the prover's draw, off the public reading, the randomness and the prover's number -/
  drawOf : (Z : PublicFiles) → (homeT b Z).D → Rand → Fin (N + 1) →
    Draw 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits (Kap Z)
  xOf : (Z : PublicFiles) → List Token → List Token → (homeR b Z).Instance
  carry : (Z : PublicFiles) → (d : (homeT b Z).D) →
    OComp (typedOracleFamily 256 (homeR b Z).queryLayout.K
        (typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits))
      (Raw 256 (homeR b Z).protocol (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits) →
    OComp (rom 256) (Raw 256 (homeR b Z).protocol (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  /-- the printer: it sees the prover's number, and so the draw -/
  print : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → Fin (N + 1) → (homeT b Z).D →
    Raw 256 (homeR b Z).protocol (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits → FormBytes
  Bs : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ModelWeights s → List Token → List Token →
    Fin (B + 1) → Fin (N + 1) → (homeT b Z).D → Bads (homeR b Z).protocol
  ζ₁ : ℝ≥0∞
  ζ₂ : ℝ≥0∞
  δT : ℝ≥0∞
  δL : ℝ≥0∞
  δB : ℝ≥0∞

variable {b : PublicFiles → ℕ} {Rand : Type} {B N : ℕ} (A : HomeArgs b Rand B N)

/-- **The prover's program** at the randomness ρ and the prover's number a: over homeT: no letter K.
The one ρ is handed to A.ra, A.sb, A.drawOf and A.print. -/
def pfOf (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : Rand)
    (p o : List Token) (a : Fin (N + 1)) : Rom.OComp (rom 256) FormBytes :=
  proveForm (homeT b Z) (fillB b Z) (A.st Z) (A.capT Z) (A.capL Z) (A.capB Z) (A.carry Z)
    (fun d => (backB b Z s w, padB b Z ((riDigits Z).e (A.ra Z ρ)),
      saltsAt ((homeT b Z).part d) (A.sb ρ)))
    (A.xOf Z p o) (fun d => A.drawOf Z d ρ a) (A.print Z s w ρ p o a)

/-- The honest side's letters: homeCoins at that program, the coins listed by digits. -/
def homeK : TheCoins := (homeCoins Rand A.ρOf (pfOf A)).digits

variable (gen : (Z : PublicFiles) → Rand → Digest → Digest → Fin (b Z + 1))

/-- **The member**, at a generator that is a letter. -/
def member : SecondHashFunctionType → Description := theWider (homeK A) ⟨b, gen⟩

/-- **The lemma's letters at the member.** -/
def homeH (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    HomeLetters (systemOfRecord (atSecondHashFunction (member A gen)) Z s) (homeT b Z) where
  Kap := A.Kap Z
  b₀ := fillB b Z
  st := A.st Z
  capT := A.capT Z
  capL := A.capL Z
  capB := A.capB Z
  B := B
  N := N
  ρOf := A.ρOf
  back := backB b Z s
  r₁ := fun ρ => padB b Z ((riDigits Z).e (A.ra Z ρ))
  s₁ := fun d ρ => saltsAt ((homeT b Z).part d) (A.sb ρ)
  drawOf := A.drawOf Z
  xOf := A.xOf Z
  carry := A.carry Z
  print := A.print Z s
  Bs := A.Bs Z s
  ζ₁ := A.ζ₁
  ζ₂ := A.ζ₂
  δT := A.δT
  δL := A.δL
  δB := A.δB

/-- **The sampler's form**: by unfolding. -/
theorem sample_member (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    (systemOfRecord (atSecondHashFunction (member A gen)) Z s).sampleCommitmentRandomness =
      .sample B fun t => .done (A.ρOf t) := rfl

section
/- Lean compares these by their names: they recurse over a program's tree. -/
attribute [local irreducible] deterministicOf Rom.ofRom OnBytes.Prover.proveForm
  DeterministicAlgorithm.toRandomized

/-- K's prover, unfolded. -/
theorem prove_homeK (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : Rand)
    (p o : List Token) :
    (homeK A).prove Z s w ρ p o =
      .sample N fun a => (deterministicOf (ofRom (pfOf A Z s w ρ p o a))).toRandomized := rfl

set_option maxHeartbeats 1600000 in
/-- The lemma's prover behind its coins is the program pfOf. -/
theorem pd_member (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : Rand)
    (p o : List Token) (a : Fin (N + 1)) :
    (homeH A gen Z s).pd w ρ p o a = deterministicOf (ofRom (pfOf A Z s w ρ p o a)) := by
  unfold HomeLetters.pd pfOf
  rfl

/-- **The prover's form** (the lemma's field prove). -/
theorem prove_member (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : Rand)
    (p o : List Token) :
    (systemOfRecord (atSecondHashFunction (member A gen)) Z s).prove w ρ p o =
      .sample N fun a => ((homeH A gen Z s).pd w ρ p o a).toRandomized :=
  (congrFun (congrFun (congrFun (congrFun (prove_record (homeK A) ⟨b, gen⟩ Z s) w) ρ) p) o).trans
    ((prove_homeK A Z s w ρ p o).trans (congrArg (RandomizedAlgorithm.sample N)
      (funext fun a => congrArg DeterministicAlgorithm.toRandomized
        (pd_member A gen Z s w ρ p o a).symm)))

end

/-! ## The statement at letters b, gen: the commitment's value a premise -/

section
/- From here on Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

variable {pp : Inst.Model.ScalesAndPolicy} (Z : PublicFiles)

local notation "Hm" => homeH A gen Z (settingsOfRead pp)
local notation "Sm" => systemOfRecord (atSecondHashFunction (member A gen)) Z (settingsOfRead pp)

/-- The three laws on the public reading, at homeT: the laws that binding takes as hypotheses. -/
theorem pub_member (hr : readFiles Z = .ok pp) :
    (homeT b Z).Pub.NoCoin ∧ ((homeT b Z).Pub.AsksIn fun _ x => (homeT b Z).Pt x) ∧
      ∀ d x, (homeT b Z).Pt x → IsOther ((homeT b Z).m d) x :=
  ⟨(bindLaws_wider placeHolderCoins ⟨b, fun _ _ _ _ => 0⟩ Z pp hr).noCoin,
    (bindLaws_wider placeHolderCoins ⟨b, fun _ _ _ _ => 0⟩ Z pp hr).asks,
    (bindLaws_wider placeHolderCoins ⟨b, fun _ _ _ _ => 0⟩ Z pp hr).spare⟩

/-- The lemma's premise "law", at homeT: no premise (lawFit_home, Johnson/Prover/At/HomeAt.lean). -/
theorem law_member (d : (homeT b Z).D) (capT capL capB : ℕ → ℕ) :
    LawFit (homeR b Z).queryLayout ((homeT b Z).Sd d) capT capL capB := lawFit_home b Z d capT capL capB

/-- JoinRest's field "wires", at homeT: no premise (wiresFit_home, the same file). -/
theorem wires_member (d : (homeT b Z).D) :
    OnBytes.Prover.WiresFit (homeR b Z).queryLayout ((homeT b Z).cA d) := wiresFit_home b Z d

/-- The salts' lengths: the lemma's field "salts". -/
theorem salts_member (bytes : ∀ ρ j, (A.sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G) :
    ∀ d ρ j, j < (homeR b Z).protocol.wordLength → ((Hm).s₁ d ρ j).length = (homeR b Z).compilerParameters.sMT :=
  fun _ ρ j _ => (length_salt _ _ j _ (bytes ρ j)).trans (sMT_R₀ Z).symm

/-- **The value of the member's commitment** (the lemma's field "commit"), b and gen letters: if the
generator's number is that of the pair (the pads that ρ names, the salts that bear c). -/
theorem commit_member (hr : readFiles Z = .ok pp)
    (bytes : ∀ ρ j, (A.sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G)
    (hgen : ∀ ρ c I, (gen Z ρ c I).val = (A.ra Z ρ).val + ((riDigits Z).n + 1) *
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt c (A.sb ρ))).val)
    (w : ModelWeights (settingsOfRead pp)) (ρ : Rand) (hash : Hash) :
    ((Sm).commit w ρ).evaluate hash =
      ZKCP.digestUnder hash (homeT b Z).encT
        ((homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash)),
          ((committerAtFixedCoins (homeR b Z).queryLayout ((homeT b Z).Sd ((homeT b Z).Pub.det (_root_.Run.famOne hash)))
            (Hm).b₀ ((Hm).back w) ((Hm).r₁ ρ)
            ((Hm).s₁ ((homeT b Z).Pub.det (_root_.Run.famOne hash)) ρ)).det
            (readBlocks ((homeT b Z).m ((homeT b Z).Pub.det (_root_.Run.famOne hash)))
              (_root_.Run.famOne hash))).1) := by
  have laws := bindLaws_wider (homeK A) ⟨b, gen⟩ Z pp hr
  have h1 := commit_wider_reach (homeK A) ⟨b, gen⟩ OnBytes.secondHashFunction Z pp hr w ρ hash (A.ra Z ρ)
    (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt (hash (configString Z)) (A.sb ρ))) (hgen ρ _ _)
  have h2 := fixedCommit_salts laws w (((theWiderTerms (homeK A) ⟨b, gen⟩).ri Z).e (A.ra Z ρ))
    (((theWiderTerms (homeK A) ⟨b, gen⟩).sl Z).e
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt (hash (configString Z)) (A.sb ρ))))
    (saltsAt (hash (configString Z)) (A.sb ρ))
    (e_idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt (hash (configString Z)) (A.sb ρ)) fun j _ =>
      (length_salt _ _ j _ (bytes ρ j)).trans (sMT_R₀ Z).symm)
  have h3 := fixedCommit_value laws w (((theWiderTerms (homeK A) ⟨b, gen⟩).ri Z).e (A.ra Z ρ))
    (saltsAt (hash (configString Z)) (A.sb ρ)) hash
  have e : (Hm).s₁ ((homeT b Z).Pub.det (_root_.Run.famOne hash)) ρ =
      saltsAt (hash (configString Z)) (A.sb ρ) := by
    show saltsAt ((homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash))) (A.sb ρ) = _
    rw [part_homeT]
  rw [e]
  exact h1.trans ((congrArg (fun c => c.evaluate hash) h2).trans h3)

/-- **CompleteOn at the member, b and gen letters**: "commit", the value of the member's commitment,
is a premise here; it is proved below, at the generator that names the salts, by a call of
`commit_member` (above; its premises `readFiles`, `bytes`, `hgen`; at that generator `hgen` is rfl).
The premises are read at the lemma's letters homeH, whose fields are A's by unfolding. -/
theorem completeOn_member_of (hr : readFiles Z = .ok pp) (α : ℝ≥0∞)
    (bytes : ∀ ρ j, (A.sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G)
    (commit : ∀ w ρ hash, ((Sm).commit w ρ).evaluate hash =
      ZKCP.digestUnder hash (homeT b Z).encT
        ((homeT b Z).part ((homeT b Z).Pub.det (_root_.Run.famOne hash)),
          ((committerAtFixedCoins (homeR b Z).queryLayout ((homeT b Z).Sd ((homeT b Z).Pub.det (_root_.Run.famOne hash)))
            (Hm).b₀ ((Hm).back w) ((Hm).r₁ ρ)
            ((Hm).s₁ ((homeT b Z).Pub.det (_root_.Run.famOne hash)) ρ)).det
            (readBlocks ((homeT b Z).m ((homeT b Z).Pub.det (_root_.Run.famOne hash)))
              (_root_.Run.famOne hash))).1))
    (small : ∀ w p o, CanServe (settingsOfRead pp) w p o → (Sm).IsModelOutput w p o → ∀ t a d,
      SetsSmall (homeR b Z).queryLayout ((homeT b Z).Sd d) ((Hm).Bs w p o t a d) (Hm).ζ₁ (Hm).ζ₂ (Hm).δT
        (Hm).δL (Hm).δB)
    (number : alphaAll (homeR b Z).queryLayout (Hm).capT (Hm).capL (Hm).capB (Hm).ζ₁ (Hm).ζ₂ (Hm).δT (Hm).δL
      (Hm).δB ≤ α)
    (J : JoinRest (Hm) (CanServe (settingsOfRead pp))) :
    CompleteOn (Sm) (CanServe (settingsOfRead pp)) α :=
  OnBytes.Prover.completeOn_home_join (Hm) (CanServe (settingsOfRead pp)) α
    (sample_member A gen Z _) (prove_member A gen Z _) (fun d => law_member Z d _ _ _)
    (pub_member Z hr).1
    (pub_member Z hr).2.1 (pub_member Z hr).2.2 small number
    (J.join (salts_member A gen Z bytes) commit)

end

/-! ## At the closed number of coins and the generator that names the salts -/

/-- The number of the committer's coins at the digits' two lists, less one. -/
def committerCoinCountLessOne (Z : PublicFiles) : ℕ :=
  ((riDigits Z).n + 1) * ((saltsDigits (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT).n + 1) - 1

/-- **The generator**: the number of the pair (the pads that ρ names, the salts that bear c): it
names no letter K. -/
def namedGen {Rand : Type} (ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1))
    (sb : Rand → ℕ → ByteArray) (Z : PublicFiles) (ρ : Rand) (c _I : Digest) : Fin (committerCoinCountLessOne Z + 1) :=
  ⟨(ra Z ρ).val + ((riDigits Z).n + 1) *
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt c (sb ρ))).val, by
    have h := (reach_pair (riDigits Z).n (saltsDigits (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT).n (ra Z ρ).val
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt c (sb ρ))).val (ra Z ρ).isLt
      (idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt c (sb ρ))).isLt).2.2
    unfold committerCoinCountLessOne
    omega⟩

/-- **THE STATEMENT: CompleteOn at the written member.** -/
theorem completeOn_member {Rand : Type} {B N : ℕ} (A : HomeArgs committerCoinCountLessOne Rand B N)
    {pp : Inst.Model.ScalesAndPolicy} (Z : PublicFiles) (hr : readFiles Z = .ok pp) (α : ℝ≥0∞)
    (bytes : ∀ ρ j, (A.sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G)
    (small : ∀ w p o, CanServe (settingsOfRead pp) w p o →
      (systemOfRecord (atSecondHashFunction (member A (namedGen A.ra A.sb))) Z
        (settingsOfRead pp)).IsModelOutput w p o → ∀ t a d,
      SetsSmall (homeR committerCoinCountLessOne Z).queryLayout ((homeT committerCoinCountLessOne Z).Sd d)
        ((homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).Bs w p o t a d)
        (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).ζ₁
        (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).ζ₂
        (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).δT
        (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).δL
        (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).δB)
    (number : alphaAll (homeR committerCoinCountLessOne Z).queryLayout
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).capT
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).capL
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).capB
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).ζ₁
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).ζ₂
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).δT
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).δL
      (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp)).δB ≤ α)
    (J : JoinRest (homeH A (namedGen A.ra A.sb) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp))) :
    CompleteOn (systemOfRecord (atSecondHashFunction (member A (namedGen A.ra A.sb))) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp)) α :=
  completeOn_member_of A (namedGen A.ra A.sb) Z hr α bytes
    (commit_member A (namedGen A.ra A.sb) Z hr bytes fun _ _ _ => rfl) small number J

end FlashProve

#print axioms FlashProve.pub_member
#print axioms FlashProve.law_member
#print axioms FlashProve.wires_member
#print axioms FlashProve.salts_member
#print axioms FlashProve.commit_member
#print axioms FlashProve.completeOn_member
#print axioms FlashProve.completeOn_member_of
#print axioms FlashProve.T_wider
#print axioms FlashProve.sample_member
#print axioms FlashProve.part_homeT
#print axioms FlashProve.prove_homeK
#print axioms FlashProve.pd_member
#print axioms FlashProve.prove_member
