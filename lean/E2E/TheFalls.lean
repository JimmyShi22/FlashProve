-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheFalls.lean: THE LISTS OF FALLS OF THE REQUEST's PROOF, AS ONE VALUE, AND G AT THAT VALUE. A
fall (Fall, Honest/Side.lean) is a test for a set of challenges at which a member of a chain may refuse
an honest run. Acceptance is asked only where no fall of the chain speaks, and the measure of the
set at which one speaks is part of the completeness error. So the lists are part of the statement:
an empty list asks acceptance everywhere, and a list that is too wide costs measure.

  roundsBeforeK4         how many rounds stand in front of K4's first, at each of its segments
  FallSlots              for each kind of sub-protocol, what it adds to each chain's list
  FallSlots.nothing      the slots with nothing in them. That value is a claim, not a default: the
                         statement of acceptance at it fails if a member refuses anywhere else
  theFalls₁ ₂ ₃          the lists
  theFalls_nothing       at that value: the first chain's list of the full size, and two empty lists
  theFalls₁_length       at that value the first list has its 87 records
  k4Fall_mem             K4's fall stands in the list at each of the twelve segments
  Speaks, speaks_of_mem  what acceptance asks of a kind whose step needs a test silent: that the
                         chain's falls speak wherever that test does; a fall of the list at the
                         member's place whose test does so is enough
  silent_of_mem          the same the other way: silence of the list is silence of each record
  k8Front_silent         the case of the smallness test: a column of weight 0
  oneElement, atKit, lookupElement, headElement   a stated share as a chance at the challenges as
                         they are drawn: its numerator times a written factor
  theMarks, markPrice, theMarksPrice   what the marks cost: a mark is an event at which the verifier
                         refuses nothing and on whose silence the bounds of falls rest
  fallsPrice, theFallsNumber   the three lists and the marks at that kit: ONE NUMBER, read off the
                         lists, with no free letter
  onlineSides            G at the return of the maker
  onlineSides_prover     where the rows are the prover's, G.prover H = H
  onlineSides_falls      the sides hold the three lists
  provG_lists            the run's prover has the return's three lists
  ground_of_head         the return's ground is the base's, from which the list's look-ups read
  FallsMeasured          the statement that the completeness error reads: at each fixed coin, at
                         the inputs of
                         the relation, the set at which the run meets a fall has measure at most
                         theFallsNumber
  fallsRoom, FallsWithinRoom   the falls' room in the error, 2⁻¹⁰⁰, and that the number lies in it
  FallsPaid              the two together, at one number and at the sides that completeness spends:
                         one road to what follows
  theSlots, TheFallsArePaid   the slots at the term, and the one closed statement there: the
                         measure at the room
  fallSmall_mono, fallsMeasured_room   so the measure is at most the room

Limits.
  * FallsMeasured, FallsWithinRoom and FallsPaid are definitions of statements. None is proved here.
    Each may be false. A law that bounds the set by a sum of prices over members ends in FallsMeasured only
    through fallSmall_mono, at a proof that this sum is at most theFallsNumber. No such proof exists
    yet.
  * A stated share is a number that no test reads. That a share at the kit bounds its fall is what
    FallsMeasured says, all together. Some shares hold the factor already, so the number is a hair
    above what it need be. A kind whose event reads a round of several elements needs a larger
    factor, as the lookups do.
  * The first list drops a record in silence where a look-up does not return. theFalls₁_length is
    the check, under the premise that it names.
  * The draws on which K9's count rests are marks, counted apart: so the second half of the share of
    K9's fall is 0 of 1, and the share alone is not that fall's chance.
  * The files on which this file stands that are no part of the library are named by its imports.
  * This file states no property of a protocol, and proves nothing about completeness, soundness or
    zero knowledge.
-/
import E2E.TheSides
import E2E.TheRooms
import E2E.TheHonestProver
import E2E.RoadHonDebts
import Johnson.Desc.ProofFile.Honest.Law.FallsFull
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld
import Johnson.P1K8R.Part1MarksCode
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksList
import Johnson.Desc.ProofFile.Honest.K4.Law.K4MarksWide
import Johnson.Desc.ProofFile.Honest.K5.MarksList
import Johnson.Desc.ProofFile.Honest.K6.K6Marks
import Johnson.Desc.ProofFile.Honest.K8.FrontFallList

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.TheFalls
open ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T TS)

/-! ## 1 The lists -/

/-- Every kind's name, the frame's among them. -/
def allKinds : List KindName :=
  [.K1, .K2, .K3, .K4, .K5, .K6, .K7, .K8, .K9, .K10, .K11, .K12, .K13, .K14, .K15, .frame]

/-- The second half of the stated share of K9's fall: 0 of 1. The draws on which K9's count rests
are marks of the kinds that own them, and the marks are priced apart. -/
def noneNotGood : Nat → Odds := fun _ => ⟨0, 1⟩

/-- **Each kind's falls beyond the first chain's list of the full size, chain by chain.** -/
structure FallSlots (F : FileDescription ProofFile.Inst) where
  first : KindName → List (Fall F.S₁)
  shared : KindName → List (Fall F.S₂)
  second : KindName → List (Fall F.S₃)

/-- **No kind adds a fall.** -/
def FallSlots.nothing (F : FileDescription ProofFile.Inst) : FallSlots F :=
  ⟨fun _ => [], fun _ => [], fun _ => []⟩

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (G₀ : ProofFile.Ground)

/-- How many rounds of the first chain stand in front of K4's first, at the feed-forward segment of
group g, whose member has the number 28 g + 4. No test of K4's fall reads it. -/
def roundsBeforeK4 (g : Nat) : Nat := roundsTo cF.blocksInOrder (28 * g + 4)

/-- The proof file's description. -/
abbrev ProofFileDesc : FileDescription ProofFile.Inst := F0T OnBytes.secondHashFunction Zp Np cF

variable (s : FallSlots (ProofFileDesc Zp Np cF))

/-- A list and what the slots add to it. -/
def withSlots {T : Type} (base more : List T) : List T := base ++ more

theorem withSlots_nil {T : Type} (base : List T) : withSlots base [] = base :=
  List.append_nil base

theorem mem_withSlots {T : Type} {base more : List T} {a : T} (h : a ∈ base) :
    a ∈ withSlots base more :=
  List.mem_append_left more h

/-- **The first chain's falls.** -/
def theFalls₁ : List (Fall (ProofFileDesc Zp Np cF).S₁) :=
  withSlots (T := Fall (ProofFileDesc Zp Np cF).S₁)
    (fallsFull Zp G₀ noneNotGood (roundsBeforeK4 cF)) (allKinds.flatMap s.first)

/-- **The shared chain's falls.** -/
def theFalls₂ : List (Fall (ProofFileDesc Zp Np cF).S₂) := allKinds.flatMap s.shared

/-- **The second chain's falls.** -/
def theFalls₃ : List (Fall (ProofFileDesc Zp Np cF).S₃) := allKinds.flatMap s.second

theorem flatMap_nothing {α β : Type} : ∀ l : List α, (l.flatMap fun _ => ([] : List β)) = []
  | [] => rfl
  | _ :: t => by
    rw [List.flatMap_cons, flatMap_nothing t]
    rfl

/-- **At the slots with nothing in them**: the list of the full size, and two empty lists. -/
theorem theFalls_nothing :
    theFalls₁ Zp Np cF G₀ (FallSlots.nothing _) =
        fallsFull Zp G₀ noneNotGood (roundsBeforeK4 cF) ∧
      theFalls₂ Zp Np cF (FallSlots.nothing _) = [] ∧
      theFalls₃ Zp Np cF (FallSlots.nothing _) = [] := by
  refine ⟨?_, flatMap_nothing _, flatMap_nothing _⟩
  unfold theFalls₁
  show withSlots _ (allKinds.flatMap fun _ => []) = _
  rw [flatMap_nothing, withSlots_nil]

/-- **No record is dropped**, under the premise of the list of the full size. -/
theorem theFalls₁_length {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (theFalls₁ Zp Np cF Bs.G₀ (FallSlots.nothing _)).length = 87 := by
  rw [(theFalls_nothing Zp Np cF Bs.G₀).1]
  exact fallsFull_87 h hB

/-- **K4's fall stands in the list at each of the twelve feed-forward segments.** -/
theorem k4Fall_mem {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : Nat} (hg : g < 12) :
    ∃ hp, Bs.G₀.W.G[g]? = some hp ∧
      K4.k4Fall ⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, roundsBeforeK4 cF g, 2 * g⟩ ∈
        theFalls₁ Zp Np cF Bs.G₀ s := by
  obtain ⟨hp, hh⟩ := Option.isSome_iff_exists.1 (plan_full h hB hg)
  exact ⟨hp, hh, mem_withSlots (fallsHead_k4 hg hh)⟩

/-! ## 2 What acceptance asks of a list -/

section Speaks
variable {S Cl : Type}

/-- The chain's falls speak at member j wherever the test front does. -/
def Speaks (fs : List (Fall S)) (bs : List (Block S Cl)) (j : Nat)
    (front : S → List Fmt.Drawn → Option String) : Prop :=
  ∀ s ds, (front s ds).isSome = true → (fallsBy fs bs j s ds).isSome = true

/-- **A fall of the list at the member's place, whose test speaks wherever front does, is enough.**
-/
theorem speaks_of_mem {fs : List (Fall S)} {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    {front : S → List Fmt.Drawn → Option String} (hb : bs[j]? = some b) {f : Fall S}
    (hf : f ∈ fs) (hp : f.place = b.place)
    (ht : ∀ s ds, (front s ds).isSome = true → (f.test s ds).isSome = true) :
    Speaks fs bs j front := by
  intro s ds h
  unfold fallsBy
  rw [hb]
  show (fallOf fs b.place s ds).isSome = true
  cases e : fallOf fs b.place s ds with
  | some _ => rfl
  | none =>
    unfold fallOf at e
    have z := List.findSome?_eq_none_iff.1 e f (List.mem_filter.2 ⟨hf, beq_iff_eq.2 hp⟩)
    have := ht s ds h
    rw [z] at this
    cases this

/-- **The cover, for every kind**: where the chain's falls are silent at member j, so is each record
of the list at that member's place. -/
theorem silent_of_mem {fs : List (Fall S)} {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    (hb : bs[j]? = some b) {f : Fall S} (hf : f ∈ fs) (hp : f.place = b.place) {s : S}
    {ds : List Fmt.Drawn} (h : fallsBy fs bs j s ds = none) : f.test s ds = none := by
  unfold fallsBy at h
  rw [hb] at h
  unfold fallOf at h
  exact List.findSome?_eq_none_iff.1 h f (List.mem_filter.2 ⟨hf, beq_iff_eq.2 hp⟩)

end Speaks

/-- **The smallness test's cover at the list**: where the list's falls are silent at a segment's
batching, no column of the drawn matrix has the weight 0 there. -/
theorem k8Front_silent {l : Nat} (hl : l < 25) {t : VerifiableInference.Desc.First.S}
    {ds : List Fmt.Drawn}
    (h : fallOf (theFalls₁ Zp Np cF G₀ s) (K8.batchPlace l (oAt l)) t ds = none) :
    K8.k8Front t ds = none :=
  K8.k8Front_of_silent
    (mem_withSlots (fallsHead_front (Zp := Zp) (G₀ := G₀) (cols := K8.k8ColsAt G₀)
      (tau := K8.k8TauAt G₀) (share := P1K8.k8ShareAt Zp G₀) (notGood := noneNotGood)
      (r0 := roundsBeforeK4 cF) hl)) h

/-! ## 3 The number -/

/-- **The factor of one drawn element.** A round's challenge is read off a string of hash blocks: a
word is drawn in at most six tries, then 0. So one named element is shown by slightly more strings
than 1 in the field's size, by at most this factor. The value that the sampler favours is the one
that a fall or a mark forbids. -/
def oneElement : ℝ≥0∞ := Iop.kapSl 128 ^ 3

/-- **A stated share, as a chance at that kit**: its numerator, times the factor over its denominator.
-/
def atKit (κ : ℝ≥0∞) (o : Odds) : ℝ≥0∞ := (o.num : ℝ≥0∞) * (κ / (o.den : ℝ≥0∞))

/-- The chance of one named element in a lookup's round: no such round draws more than 36 elements.
-/
def lookupElement : ℝ≥0∞ := Iop.kapSl 128 ^ 108 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)

/-- The chance of one named element in the output head's rounds. -/
def headElement : ℝ≥0∞ := oneElement / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)

/-- **A mark's price at the kit.** At the lookups and the output head the numerator counts events,
each of one named element. -/
def markPrice (mk : Mark) : ℝ≥0∞ :=
  if mk.place.kind = KindName.K3 then (mk.share.num : ℝ≥0∞) * lookupElement
  else if mk.place.kind = KindName.K6 then (mk.share.num : ℝ≥0∞) * headElement
  else atKit oneElement mk.share

/-- **The marks at the first chain**, kind by kind. -/
def theMarks : List Mark :=
  P1K8.part1Marks Zp G₀ ++ K3.Good.k3Marks Zp G₀ ++ K4.k4MarksWide Zp G₀ ++ K5.k5Marks Zp G₀ ++
    K6.part4Marks Zp G₀

/-- The marks' prices, added. -/
def theMarksPrice : ℝ≥0∞ := ((theMarks Zp G₀).map markPrice).sum

/-- A list's falls at the kit, added. -/
def fallsPrice {S : Type} (fs : List (Fall S)) : ℝ≥0∞ :=
  (fs.map fun f => atKit oneElement f.share).sum

/-- **The falls' number**: the three lists and the marks, each record once, at the kit. -/
def theFallsNumber : ℝ≥0∞ :=
  fallsPrice (theFalls₁ Zp Np cF G₀ s) + fallsPrice (theFalls₂ Zp Np cF s) +
    fallsPrice (theFalls₃ Zp Np cF s) + theMarksPrice Zp G₀

end AtPublicFiles.TheFalls

/-! ## 4 At the return of the maker -/

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (ProverCoinCounts Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles)
open P5J
open AtPublicFiles.TheSides AtPublicFiles.TheFalls

local instance (priority := high) theFallsNonemptyPadZ : Nonempty PadZ := pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) theFallsNonemptyRunValue : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) theFallsInhabitedRunValue : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl)

/-- The sides' type at the return of the maker. -/
abbrev OnlineSides :=
  Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey ProofFile.Honest.Cells Unit
    Unit

/-- The rows' type. -/
abbrev OnlineRows := Rows FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey ProofFile.Honest.Cells Unit Unit

variable (s : FallSlots (ProofFileDesc returned.Z places firstChain))

/-- **G at the return of the maker**: rows, a way of setting their letters, and the lists of falls.
-/
def onlineSides
    (A : Letters (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      ProofFile.Honest.Cells Unit Unit)
    (R : OnlineRows (Z := Z)) : OnlineSides returned places firstChain :=
  theSides (descZ returned.Z places firstChain) A R
    (theFalls₁ returned.Z places firstChain returned.G s)
    (theFalls₂ returned.Z places firstChain s) (theFalls₃ returned.Z places firstChain s)

/-- **Where the rows are the prover's, G.prover H = H.** -/
theorem onlineSides_prover
    (A : Letters (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      ProofFile.Honest.Cells Unit Unit)
    {R : OnlineRows (Z := Z)} (h : R.Fit returned.H) :
    (onlineSides returned places firstChain s A R).prover returned.H = returned.H :=
  theSides_prover h

/-- **The sides hold the lists**: no field of them stands at its default. -/
theorem onlineSides_falls
    (A : Letters (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      ProofFile.Honest.Cells Unit Unit)
    (R : OnlineRows (Z := Z)) :
    (onlineSides returned places firstChain s A R).falls₁ =
        theFalls₁ returned.Z places firstChain returned.G s ∧
      (onlineSides returned places firstChain s A R).falls₂ =
        theFalls₂ returned.Z places firstChain s ∧
      (onlineSides returned places firstChain s A R).falls₃ =
        theFalls₃ returned.Z places firstChain s :=
  ⟨rfl, rfl, rfl⟩

/-- **The ground of the return is the base's**, where the description is the head's. -/
theorem ground_of_head (hM : onlineMaker Z = .ok returned) {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain x)
    (hB : ProofFile.baseOf returned.Z (ProofFile.pureSeat OnBytes.secondHashFunction returned.Z) = .ok Bs) :
    Bs.G₀ = returned.G := by
  obtain ⟨Bs', _, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact Option.some.inj (O.blank.symm.trans (ProofFile.Honest.atPure_ok hM).2.1)

/-- **The sides that completeness spends**: the prover's own rows, letters that say nothing. -/
abbrev sidesForCompleteness : OnlineSides returned places firstChain :=
  onlineSides returned places firstChain s (Letters.bare _ _) (bareRows returned.H)

theorem sidesForCompleteness_prover :
    (sidesForCompleteness returned places firstChain s).prover returned.H = returned.H :=
  onlineSides_prover returned places firstChain s _ (bareRows_fit returned.H)

/-- **The three lists of the prover that the falls' run plays are the return's own**, at any rows that
fit it. -/
theorem provG_lists
    (A : Letters (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      ProofFile.Honest.Cells Unit Unit)
    {R : OnlineRows (Z := Z)} (h : R.Fit returned.H) :
    (provG Z returned.Z places firstChain returned.B (onlineSides returned places firstChain s A R)
        returned.H).first = returned.H.first ∧
      (provG Z returned.Z places firstChain returned.B
        (onlineSides returned places firstChain s A R) returned.H).shared = returned.H.shared ∧
      (provG Z returned.Z places firstChain returned.B
        (onlineSides returned places firstChain s A R) returned.H).second = returned.H.second :=
  ⟨(halves_kept A.first A.keeps₁ R.first).trans h.1.symm,
    (halves_kept A.shared A.keeps₂ R.shared).trans h.2.1.symm,
    (halves_kept A.second A.keeps₃ R.second).trans h.2.2.symm⟩

/-- **The rows at slots are the prover's**, at what the maker returns. -/
theorem rowSlots_fit (hM : onlineMaker Z = .ok returned)
    (r : RowSlots (onlineFilling Z) returned.Z returned.G) : r.rows.Fit returned.H :=
  RowSlots.fit hM r

variable (G : OnlineSides returned places firstChain)

/-- **The falls' measure, as the completeness error reads it**: at each fixed coin, at the inputs of
the relation. -/
def FallsMeasured (Relation : FullSizeMatrix → XF → Prop) (p : ℝ≥0∞) : Prop :=
  FallSmall
    (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H)
    (fallG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H)
    (fun n w a => TiedOut Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H Relation (fun _ _ => ∅) n w (instanceAsPlainRecord a)) p

variable {returned places firstChain G}

/-- A measure at most p is at most a larger q. -/
theorem fallSmall_mono {Relation : FullSizeMatrix → XF → Prop} {p q : ℝ≥0∞}
    (h : FallsMeasured returned places firstChain G Relation p) (hpq : p ≤ q) :
    FallsMeasured returned places firstChain G Relation q :=
  fun n w x c t => le_trans (h n w x c t) hpq

variable (returned places firstChain)

/-- **The room of the falls in the completeness error.** -/
def fallsRoom : ℝ≥0∞ := AtPublicFiles.TheRooms.onlineFallRoom

/-- **The number lies within the room.** -/
def FallsWithinRoom : Prop :=
  theFallsNumber returned.Z places firstChain returned.G s ≤ fallsRoom

/-- **What is owed on the falls at the term**: at the sides that completeness spends, the falls have
at most the number that is read off the same lists, and that number lies within the room. A fall that
speaks everywhere at a small stated share makes the first clause false. -/
def FallsPaid (Relation : FullSizeMatrix → XF → Prop) : Prop :=
  FallsMeasured returned places firstChain (sidesForCompleteness returned places firstChain s)
      Relation (theFallsNumber returned.Z places firstChain returned.G s) ∧
    FallsWithinRoom returned places firstChain s

/-- **The slots at the term**: no kind adds to the lists. -/
abbrev theSlots : FallSlots (ProofFileDesc returned.Z places firstChain) := FallSlots.nothing _

/-- **The one statement on the falls**, at every return of the maker, at any sides whose prover is the
return's and whose lists are the lists at the term: the falls have at most the room. A fall that
speaks everywhere makes it false. FallsPaid is one road to it. -/
def TheFallsArePaid (Z : PublicFiles) (Relation : FullSizeMatrix → XF → Prop) : Prop :=
  ∀ (returned : OnlineReturn Z) (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl),
    onlineMaker Z = .ok returned → H2U.placesOfMade returned.Z.made = .ok places →
      ProofFile.onlineFirstChainAt returned.Z = .ok firstChain →
      ∀ G : OnlineSides returned places firstChain, G.prover returned.H = returned.H →
        G.falls₁ = theFalls₁ returned.Z places firstChain returned.G
          (theSlots returned places firstChain) →
        G.falls₂ = [] → G.falls₃ = [] →
        FallsMeasured returned places firstChain G Relation fallsRoom

/-- **So the falls have at most the room**: the form in which the error spends them. -/
theorem fallsMeasured_room {Relation : FullSizeMatrix → XF → Prop}
    (h : FallsPaid returned places firstChain s Relation) :
    FallsMeasured returned places firstChain (sidesForCompleteness returned places firstChain s)
      Relation fallsRoom :=
  fallSmall_mono h.1 h.2

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.TheFalls.theFalls_nothing
#print axioms AtPublicFiles.TheFalls.theFalls₁_length
#print axioms AtPublicFiles.TheFalls.k4Fall_mem
#print axioms AtPublicFiles.TheFalls.speaks_of_mem
#print axioms AtPublicFiles.TheFalls.silent_of_mem
#print axioms AtPublicFiles.TheFalls.k8Front_silent
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineSides_prover
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineSides_falls
#print axioms AtPublicFiles.AtFiles.HonestTerm.provG_lists
#print axioms AtPublicFiles.AtFiles.HonestTerm.ground_of_head
#print axioms AtPublicFiles.AtFiles.HonestTerm.sidesForCompleteness_prover
#print axioms AtPublicFiles.AtFiles.HonestTerm.rowSlots_fit
#print axioms AtPublicFiles.AtFiles.HonestTerm.fallSmall_mono
#print axioms AtPublicFiles.AtFiles.HonestTerm.fallsMeasured_room
