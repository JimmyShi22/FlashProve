-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingLaw.lean: THE READING's LAW, ITS COUNTING HALF: a whole file's written
transcript (rounds whose verifier messages are hash blocks with bits of work) is read as a typed
transcript (rounds whose verifier messages are field elements, positions, pairs of bits), and the
price of that reading is stated in one bound: the sampler's bias, the work and the number of slots.

Why. Soundness is proved of typed blocks. A file as data (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean) has
written rounds, and its decision sees three views. A law "the kind's yes gives the proved block's
yes" needs one typed transcript to speak of, and one price for passing from hash blocks to typed
values. Both are STATED here once, for all kinds; NEITHER IS PAID AT ANY DATA.

What is gathered and what is new. MOST OF THIS FILE IS A GATHERING. Gathered: `Maps`, `Maps.view`,
`Maps.fits`, `Maps.below_err` (OnBytes/Flat/CarrySMaps.lean), `wholeMap`, `wholeView`, `fits_whole`,
`tr_whole_of_out` (Johnson/Flat/CarrySWhole.lean), `below_file_shared`
(OnBytes/Flat/CarrySFileN.lean). New: `Maps.times_err`; the clauses as one statement;
`Maps.fits_behind`; the premise for N slots in the form of `Maps.Held`; four equations by unfolding,
named.

Definitions, statements and proofs.
  `Maps.times_err`: N times the written counts are the written counts of N times the typed ones.
  `Maps.rvT_cons`, `Maps.view_step`, `Maps.view_skip`, `viewOf_rounds`: a written round's two faces.
    A view's round shows the plain part of the prover's message and `drawnOf` (Run/PlanDraws.lean)
    of the typed values `valsOf (toRD d) c`; the image's round holds (M.fm m, M.g (valsOf (toRD d)
    c)): THE SAME TYPED VALUES. The rounds of the views that `reductionOfWholeFile` hands to the run are these.
  `ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N`: six fields.
    image: where the file's verifier says yes at τ (at any test of the silent rounds and any run), τ
      has an image along `wholeMap`, and it is `wholeView τ`. Of that yes the three chains' tests of
      work alone are spent: UNDER pass.
    fits: the written counts `wholeErr` bear the typed counts: at most `(bsRound ..).w` written
      verifier messages that pass go to one typed value: THE BIAS.
    below: the written counts, the shared rounds' taken N times, are shares of at most εs.
    chain₁, chain₂, chain₃: fits and below chain by chain, the shared chain's typed counts taken N
      times. `Maps.fits_behind`: the same behind a silent round.
  `readingLaw_of`: the law, from six premises: `Maps.OK` of the three lists of maps (each g one to
    one; positions of at most 64 bits); `Maps.Held εs` of the first and the last chain's typed
    counts, and of N TIMES the shared chain's. `Held` asks at each round that is read: the typed
    count is a share of at most c of the round's typed values, and (1 + 2^-128)^b · c / 2^work ≤ εs,
    b the round's number of hash blocks: THE BIAS, THE WORK AND THE N SLOTS IN ONE BOUND.
  `readingLaw_skips`: at maps that skip every round the law holds at εs = 0.
  `ReadingLaw.sound`: how it is spent: with the law between the two decisions (`RunMeets`,
    Johnson/Flat/WholeRun.lean), the translation of the languages and the typed protocol's
    soundness, the file's protocol is sound round by round at counts that are shares of at most εs.
Control of `RunMeets` at a round with proof of work: Johnson/Flat/WholeRunToy.lean; this law: none.

What kind of bound it is. ONE-SIDED: the share of the written verifier messages of a round that pass
the test of work AND are read into a given set of e typed values is at most εs. It bounds "passes
and is bad", not "is bad, given that it passes". It is no statement on the distribution of the typed
values: no lower bound, no closeness: "a reading is a draw" would say more than is shown. Soundness
needs no more.

Limits. NO MAP IS MADE HERE, at any data: M₁, M₂, M₃, the typed counts, εs and N are letters: ALL
THE WEIGHT LIES IN THE SIX PREMISES AND IN `RunMeets`. At maps that skip every round the law is free
(`readingLaw_skips`). THERE IS NO READING OF A VIEW HERE: the reading is a function of a written
transcript τ; a view stands beside it. That serves where the decision is handed the views of some τ:
so it is in `reductionOfWholeFile`, of which the key file's and the proof file's protocols of the soundness
theorems' three files are made (`filesOf`, Johnson/EntryRec/AtFiles.lean: by reading). Of a view
that another reader makes out of a file's bytes nothing is said: that what runs is that verifier is
a law of its own, owed elsewhere, and not proved yet. A view does not fix the image: it shows the
plain part of m without the nonce, and the columns that were opened, not m's oracles; and `drawnOf`
is not one to one at a round that draws matrix entries: a typed value holds a pair of bits for each
entry, and two pairs give the entry 0 (`trit`, Run/DrawTie.lean); since `Maps.OK` asks that g be one
to one, the typed round must hold the pairs too. At draws of other kinds nothing is shown either
way. Nothing is stated on what a view's `opened` says of the image's oracles. NOT STRICT: of the
nine tests in the file's verifier's yes the law spends three; that no draw is cut short (`fullOf`),
what is carried (`carriesOf`), the silent rounds' test and the run are not read; nothing here knows
whether a word is written canonically. Each map reads its own round alone, and no statement
(OnBytes/Flat/CarrySMaps.lean's own limit). A skipped round is in no image: what a decision tests
there is mirrored by no typed test. N is the coarse count: every shared round pays N
(OnBytes/Flat/CarrySFileN.lean's own limit). `ReadingLaw.sound` HAS THE FORM OF THE KEY FILE's
HYPOTHESIS (`CompilerSoundnessConditionStatements.keySound`, Johnson/Top/InnerCompiledVerifier.lean, at N := 2 ^ depthReqT) and of the entry
file's. THE PROOF FILE's (`CompilerSoundnessConditionStatements.proofSound`) asks knowledge soundness in the form for batches,
with a witness map: `ReadingLaw.sound` does not feed it. The library's road to it goes by the three
chains (`linksBack_knowsJ`, OnBytes/TypedOracleCompiler/Joined/LinksBack.lean; `proofSound_at_links`,
OnBytes/TypedOracleCompiler/Joined/MidLinks.lean): of that road's premises the clauses chain₁, chain₂, chain₃ with
`Maps.fits_behind` are meant to pay f₁, f₂, f₃ and the bounds on the written counts, where the
second chain's typed link has the counts `Err.times N δ₂`; THAT CALL IS NOT MADE HERE, and the
road's other premises (the typed clauses of the three chains, the keys, what is handed on) are not
touched. In `RunMeets` the typed decision acc' is meant to be a composition of the library's proved
blocks, not a second text of the protocol; here it is a letter. Nothing on an honest prover or on
hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WholeRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice

namespace Maps

/-- N times the written counts are the written counts of N times the typed ones. -/
theorem times_err (N : ℕ) : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (ε : Err s'),
    Err.times N (M.err ε) = M.err (Err.times N ε)
  | _, _, .nil, _ => rfl
  | _, _, .step (d := d) _ rest, (e, ε) => by
      show (N * (e * (bsRound .two d.entry d.kind).w), Err.times N (rest.err ε)) =
        (N * e * (bsRound .two d.entry d.kind).w, rest.err (Err.times N ε))
      rw [Nat.mul_assoc, times_err N rest ε]
  | _, _, .skip _ rest, ε => by
      show (N * 0, Err.times N (rest.err ε)) = (0, rest.err (Err.times N ε))
      rw [Nat.mul_zero, times_err N rest ε]

/-- The maps of a chain behind a round that no typed protocol has (the front round, the joining
round, the seam): that round is skipped and bears the count 0. In this form a chain's maps are
handed to the road by links (`linksBack_knowsJ`, OnBytes/TypedOracleCompiler/Joined/LinksBack.lean: f₁, f₂, f₃). -/
theorem fits_behind {r : Round} {ds : List RDT} {s' : Shape} (M : Maps ds s') (ok : M.OK)
    (δ : Err s') :
    (CarryS.skip (r := r) fun _ _ => M.carry).Fits δ
      ((0, M.err δ) : Err (r :: uLT (ckP .two) ds)) :=
  fun _ _ => M.fits ok δ

/-- **A written round's two faces, the first: what a view shows of it.** The plain part of the
prover's message, without the nonce; and the untyped view of the typed values `valsOf (toRD d) c`
that the format's sampler makes of the verifier's message c. -/
theorem rvT_cons (d : RDT) (ds : List RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (τ : Tr (uLT (ckP .two) ds)) :
    rvT (ckP .two) (d :: ds) (m, c, τ) =
      ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
        drawnOf .two d.entry d.kind (valsOf (toRD d) c)⟩ :: rvT (ckP .two) ds τ := rfl

/-- **The second: what the image holds of it.** The same typed values, under g. -/
theorem view_step {d : RDT} {r' : Round} {ds : List RDT} {s' : Shape} (M : RMap d r')
    (rest : Maps ds s') (m : (wT d).Msg) (c : (wT d).Chal) (τ : Tr (uLT (ckP .two) ds)) :
    (Maps.step M rest).view (m, c, τ) = (M.fm m, M.g (valsOf (toRD d) c), rest.view τ) := rfl

/-- A skipped round is in no image. -/
theorem view_skip (d : RDT) {ds : List RDT} {s' : Shape} (rest : Maps ds s') (m : (wT d).Msg)
    (c : (wT d).Chal) (τ : Tr (uLT (ckP .two) ds)) :
    (Maps.skip d rest).view (m, c, τ) = rest.view τ := rfl

end Maps

section
variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {s₁' s₂' s₃' : Shape}
  (M₁ : Maps D.ds₁ s₁') (M₂ : Maps D.ds₂ s₂') (M₃ : Maps D.ds₃ s₃')
  (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃') (εs : ℝ≥0∞) (N : ℕ)

/-- The rounds of a view that `reductionOfWholeFile` hands to the run are the list that it is made of: for the
three chains `rvT (ckP .two) D.dsᵢ τᵢ` (OnBytes/Maker/Whole.lean, `reductionOfWholeFile`, the field `out`). -/
theorem viewOf_rounds (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Tr (uLT (ckP .two) D.ds₁))
    (τ₂ : Tr (uLT (ckP .two) D.ds₂)) (τ₃ : Tr (uLT (ckP .two) D.ds₃)) (rs : List RV) (key : ℕ → ℕ)
    (ws : List Want) :
    (OnBytes.Maker.viewOf (ckP .two) D y τ₁ τ₂ τ₃ rs key ws).rounds = rs := rfl

/-- **The reading's law.** -/
structure ReadingLaw : Prop where
  /-- under the file's verifier's yes, which holds the tests of work, the image is `wholeView` -/
  image : ∀ {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh),
    (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).out x y τ = some () →
      (wholeMap D tF tJ t3 M₁ M₂ M₃).tr τ = some (wholeView D tF tJ t3 M₁ M₂ M₃ τ)
  /-- the sampler's bias: the written counts bear the typed ones -/
  fits : (wholeMap D tF tJ t3 M₁ M₂ M₃).Fits (Err.app δ₁ (Err.app δ₂ δ₃))
    (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃)
  /-- the bias, the work and the N slots in one bound -/
  below : Err.Below (Err.timesShared N (chainsOf (ckP .two) D tF tJ t3).ann
    (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃)) εs
  /-- the same chain by chain, the shared chain's typed counts taken N times: the form for a road
  that goes by the three chains -/
  chain₁ : M₁.carry.Fits δ₁ (M₁.err δ₁) ∧ Err.Below (M₁.err δ₁) εs
  chain₂ : M₂.carry.Fits (Err.times N δ₂) (M₂.err (Err.times N δ₂)) ∧
    Err.Below (M₂.err (Err.times N δ₂)) εs
  chain₃ : M₃.carry.Fits δ₃ (M₃.err δ₃) ∧ Err.Below (M₃.err δ₃) εs

variable {M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N}

/-- **The reading's law holds**, from `Maps.OK` of the three lists of maps and `Maps.Held εs` of the
first chain's typed counts, of N times the shared chain's, and of the last chain's. -/
theorem readingLaw_of (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (held₁ : M₁.Held εs δ₁)
    (held₂ : M₂.Held εs (Err.times N δ₂)) (held₃ : M₃.Held εs δ₃) :
    ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N where
  image := fun silent run x y τ h => tr_whole_of_out D tF tJ t3 M₁ M₂ M₃ silent run x y τ h
  fits := fits_whole D tF tJ t3 ok₁ ok₂ ok₃ δ₁ δ₂ δ₃
  below := below_file_shared (chainsOf_laws (ckP .two) D tF tJ t3) N (M₁.below_err ok₁ δ₁ held₁)
    (by rw [Maps.times_err]; exact M₂.below_err ok₂ _ held₂) (M₃.below_err ok₃ δ₃ held₃)
  chain₁ := ⟨M₁.fits ok₁ δ₁, M₁.below_err ok₁ δ₁ held₁⟩
  chain₂ := ⟨M₂.fits ok₂ _, M₂.below_err ok₂ _ held₂⟩
  chain₃ := ⟨M₃.fits ok₃ δ₃, M₃.below_err ok₃ δ₃ held₃⟩

/-- **At maps that skip every round the law holds at εs = 0, at every N**: it says nothing until
rounds are read. -/
theorem readingLaw_skips (N : ℕ) :
    ReadingLaw D tF tJ t3 (Maps.skips D.ds₁) (Maps.skips D.ds₂) (Maps.skips D.ds₃) () () () 0 N :=
  readingLaw_of D tF tJ t3 (Maps.ok_skips _) (Maps.ok_skips _) (Maps.ok_skips _)
    (Maps.held_skips _ _) (Maps.held_skips _ _) (Maps.held_skips _ _)

/-- **How it is spent**: with the law between the two decisions (`meets`), the translation of the
languages (`lang`) and the typed protocol's soundness (`sound`), the file's protocol is sound round
by round at the written counts, which, the shared rounds' taken N times, are shares of at most
εs. -/
theorem ReadingLaw.sound (R : ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N) {Xi X' : Type}
    {E' : ExtSpec} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (fx : Xi → X') (fy : (oneExternalString (2 ^ D.a) SgX).Str → E'.Str)
    (acc' : X' → E'.Str → Tr (s₁' ++ (s₂' ++ s₃')) → Bool)
    (meets : RunMeets D tF tJ t3 M₁ M₂ M₃ silent run fx fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (L : Xi → (oneExternalString (2 ^ D.a) SgX).Str → Prop) (L' : X' → E'.Str → Prop)
    (lang : ∀ x y, L' (fx x) (fy y) → L x y)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃))) :
    (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof.Sound L
        (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃) ∧
      Err.Below (Err.timesShared N (chainsOf (ckP .two) D tF tJ t3).ann
        (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃)) εs :=
  ⟨sound_carryS (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof
      (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E')
      (fun _ _ => wholeMap D tF tJ t3 M₁ M₂ M₃) (Err.app δ₁ (Err.app δ₂ δ₃))
      (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃) (fun _ _ => R.fits) fx fy L L' lang
      (wholeRun_yes D tF tJ t3 M₁ M₂ M₃ silent run fx fy acc' meets) sound,
    R.below⟩

end

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.times_err
#print axioms OnBytes.Flat.readingLaw_of
#print axioms OnBytes.Flat.ReadingLaw.sound
