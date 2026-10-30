-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkCoin.lean: THE COPY's FILE's LINK, THE PROVER's SIDE: THE FINITE TYPE OF ITS
RANDOM VALUES, AND THE MAP FROM IT INTO THE LETTERS LCoins (Johnson/Prover/Link/LinkAll.lean) THAT
THE STRATEGY linkNext READS. Definitions; no theorem but that the type is finite and not empty, and
two closed facts on public numbers. No distribution is stated.

THE TYPES ARE GENERAL IN THE ENTRIES' TYPE (a letter): one text serves field elements and words; the
map coinsOf, the type Kc and the counts stand at the extension field. Every random value stands in a
FINITE FUNCTION, typed at the sizes of the message that holds it. No list, no default inside the
sizes. The order of the fields is the order of sending; in a message: the main rows' tails, row 0
first; the main row's message of a word with a main row and no answer; the pad, if it lies in a main
row; the mask table's entries; the mask rows' tails.

  at2           a finite function read by two numbers: THE WRITTEN 0 FROM EITHER SIZE ON; with one
                number: the library's onNat (Johnson/Top/H/SwitchMaps.lean), which does the like
  FirstK        the one sending in front: for each of the two folded rows' messages: its R rows'
                tails, its pad (one entry) · the first fold's fresh table: its 2 k + 1 coefficients,
                BY THEIR NUMBERS in the polynomial's own order, and its one row's tail
  SwK           the message that a switch sends: its main rows' tails · the entries of its mask
                table that are not carried, by the table's own index, the pad among them · its mask
                rows' tails
  RideK         the next fold's fresh table, which goes with that message where a fold follows: its
                2 k + 1 coefficients, by their numbers, and its rows' tails
  WordK         the word with one main row, one mask row and no answer that goes with the last
                switch's message: its main row's tail, its main row's message, all entries of its
                mask row, that row's tail
  BodyK, LinkK  these along the stages; with FirstK
  FirstK.map, SwK.map, RideK.map, WordK.map, BodyK.map, LinkK.map   one map of entries, entry by
                entry
  BodyK.finite, BodyK.nonempty, LinkK.finite, LinkK.nonempty   finite, not empty
  castW         a family of coefficients by number at the sizes s₁, read BY NAME at sizes s: where
                s = s₁ the name x reads the number wNo x (Johnson/Prover/Link/LinkCoinNo.lean: ONE
                MAP FROM NAMES TO NUMBERS: below 2 k + 1 by wNo_lt; no number under two names by
                wNo_inj; every number under a name by wNo_onto); THE WRITTEN 0 at every other s
  zeroPS, freeAt, bodyW, bodyNew, bodyFr, coinsOf   THE MAP, field by field (below)
  sameCode, kFits   ONE PUBLIC TEST: THE SIZES FIT: the list of stages is the plan's own; the
                library's own sizesOk; the front's vector and its pad have room; the front's sizes
                are the first stage's. coinsOf is total and does not test it. No theorem of this
                file takes kFits as a premise; whether a law elsewhere does is said at that law.
                What kFits gives in this file's own letters is said in
                Johnson/Prover/Link/LinkCoinFits.lean. At sizes that do not
                fit, coinsOf lays its written 0 or cuts, in silence
  frontN, swN, rideN, wordN, bodyN, linkN   the counts
  Kc, coinsFull THE TYPE AND THE MAP AT THE WRITTEN LETTERS, THE FULL SIZE
  fr_kFits, fr_linkN   two closed facts on public numbers there: the sizes fit; the count is 26840

FIELD BY FIELD, what coinsOf lays:
  pad a         FirstK.pad a: a random value
  tN a i q      FirstK.tail a i q at i < R and q < C.r; the written 0 beyond
  psiN q        FirstK.wTail q at q < Z.r; the written 0 beyond
  body.W s j x  at j = 0: FirstK.W; at 0 < j where a fold follows switch j - 1: that switch's
                RideK.W: each AT THE NUMBER wNo x OF THE NAME x, WHERE s IS THE STAGE's OWN SIZES
                (sgOf of stage j); the written 0 at every other s, and at every j from the last
                stage's number on
  body.new j    a structure PS, of which: tabM, tabZ: the written 0 (nextPS overwrites both) · tM,
                tZ: SwK.mainTail, SwK.maskTail inside the new message's sizes, 0 beyond · where a
                fold follows: fT: RideK.tail; fM: the written 0 (sNext overwrites it by the packing
                of W); sM, sT: the written 0 (no reader at such a stage) · at the last switch: row 0
                of fM and of fT: WordK.mask, WordK.maskTail; sM, sT: WordK.main, WordK.mainTail;
                every other row of fM and fT: the written 0
  body.fr j i   SwK.free (i - maskUsed s) at maskUsed s ≤ i < 2 ^ h' * Z'.l; the written 0 elsewhere
                (below maskUsed s, Johnson/Prover/Link/SwitchTab.lean, gMask does not read fr)

Limits. THAT NOTHING IS READ WHERE A WRITTEN 0 STANDS is not stated here: it is read off the texts
of linkAll, bodyAll, nextPS, gMask, packedN, firstColW, stageColW and lastCol, UNDER kFits. Where
kFits says no, coinsOf still lays something: at a switch whose carried entries have no room
SwK.free's size (a truncated difference) is 0; at a list that is not the plan's own the coefficients
are written zeros; at a first stage whose k is larger than aR + 1 firstPS lays one tail at more than
one row. The types are shown finite by injections into products; no equivalence with a product or
with "Fin n → GE" is stated. FirstK's fields hold the two folded rows' messages side by side, not
message by message. Of the 26840 values at the full size 413 are the entries of SwK.free other than
the one that is the pad's place (92 + 108 + 108 + 105). That the counts are the types'
cardinalities' exponents is not stated. fr_kFits and fr_linkN stand under "set_option maxRecDepth
100000 in": a limit of elaboration is raised; the kernel checks the term. The salts of leaves are
not here. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.LinkAll
import Johnson.Prover.Link.SwitchTab
import Johnson.Prover.Link.LinkCoinNo
import Johnson.Desc.K15.TypedV
import Johnson.Desc.K12.Sizes
import Johnson.Top.H.SwitchMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15
open H2K.Pub (sgOf)
open Johnson.Top.H (onNat)

/-! ## Finite functions, read by numbers -/

/-- A finite function read by two numbers: the written 0 from either size on. (With one number: the
library's onNat, Johnson/Top/H/SwitchMaps.lean: "if h : i < n then c ⟨i, h⟩ else 0".) -/
def at2 {m n : ℕ} (c : Fin m → Fin n → GE) (r q : ℕ) : GE :=
  if h : r < m ∧ q < n then c ⟨r, h.1⟩ ⟨q, h.2⟩ else 0

/-! ## The types -/

/-- **The one sending in front.** s₀: the first stage's sizes. -/
structure FirstK (α : Type) (S : Sz) (s₀ : Sg) where
  /-- entry q of the tail of row i of the folded row a's message -/
  tail : Bool → Fin S.P.R → Fin S.P.C.r → α
  /-- the pad of that message's one sample -/
  pad : Bool → α
  /-- the first fold's fresh table's coefficients, by their numbers in the polynomial's own order -/
  W : Fin (2 * (s₀.h + s₀.g) + 1) → α
  /-- that table's one row's tail -/
  wTail : Fin S.P.Z.r → α

/-- **The message that the switch out of a stage of the sizes s into one of the sizes s' sends.** -/
structure SwK (α : Type) (s s' : Sg) where
  mainTail : Fin (2 ^ (s'.h + s'.g)) → Fin s'.C.r → α
  /-- the entries of the mask table from the index maskUsed s on: the library's own count of them
  (Fmt.M1.fillOf, Fmt/M1All.lean: 2 ^ h' * Z'.l - (2 * Z.l + C.r + 2 * Z.r)) -/
  free : Fin (Fmt.M1.fillOf s.st s'.st) → α
  maskTail : Fin (2 ^ s'.h) → Fin s'.Z.r → α

/-- **The fold's own table at a stage of the sizes s.** -/
structure RideK (α : Type) (s : Sg) where
  /-- the coefficients, by their numbers in the polynomial's own order -/
  W : Fin (2 * (s.h + s.g) + 1) → α
  tail : Fin (2 ^ s.h) → Fin s.Z.r → α

/-- **The word with one main row, one mask row and no answer at a last stage of the sizes s.** -/
structure WordK (α : Type) (s : Sg) where
  mainTail : Fin s.C.r → α
  main : Fin s.C.l → α
  mask : Fin s.Z.l → α
  maskTail : Fin s.Z.r → α

/-- **Along the stages**, from a stage on: for each switch its message and what goes with it. -/
def BodyK (α : Type) : Fmt.M1.Stage → List Fmt.M1.Stage → Type
  | _, [] => Unit
  | cur, [next] => SwK α (sgOf cur) (sgOf next) × WordK α (sgOf next)
  | cur, next :: n₂ :: rest =>
    SwK α (sgOf cur) (sgOf next) × RideK α (sgOf next) × BodyK α next (n₂ :: rest)

/-- **All random values of the link's prover**, at the front's sizes and a list of stages. -/
def LinkK (α : Type) (S : Sz) : List Fmt.M1.Stage → Type
  | [] => Unit
  | first :: rest => FirstK α S (sgOf first) × BodyK α first rest

/-! ## One map, entry by entry -/

def FirstK.map {α β : Type} {S : Sz} {s₀ : Sg} (f : α → β) (k : FirstK α S s₀) : FirstK β S s₀ :=
  ⟨fun a i q => f (k.tail a i q), fun a => f (k.pad a), fun x => f (k.W x),
    fun q => f (k.wTail q)⟩
def SwK.map {α β : Type} {s s' : Sg} (f : α → β) (k : SwK α s s') : SwK β s s' :=
  ⟨fun r q => f (k.mainTail r q), fun i => f (k.free i), fun r q => f (k.maskTail r q)⟩
def RideK.map {α β : Type} {s : Sg} (f : α → β) (k : RideK α s) : RideK β s :=
  ⟨fun x => f (k.W x), fun r q => f (k.tail r q)⟩
def WordK.map {α β : Type} {s : Sg} (f : α → β) (k : WordK α s) : WordK β s :=
  ⟨fun q => f (k.mainTail q), fun j => f (k.main j), fun j => f (k.mask j),
    fun q => f (k.maskTail q)⟩
def BodyK.map {α β : Type} (f : α → β) :
    (cur : Fmt.M1.Stage) → (rest : List Fmt.M1.Stage) → BodyK α cur rest → BodyK β cur rest
  | _, [], _ => ()
  | _, [_], k => (k.1.map f, k.2.map f)
  | _, next :: n₂ :: rest, k => (k.1.map f, k.2.1.map f, BodyK.map f next (n₂ :: rest) k.2.2)
def LinkK.map {α β : Type} {S : Sz} (f : α → β) :
    (l : List Fmt.M1.Stage) → LinkK α S l → LinkK β S l
  | [], _ => ()
  | first :: rest, k => (k.1.map f, BodyK.map f first rest k.2)

/-! ## Finite, not empty -/

section
variable {α : Type}

instance [Finite α] (S : Sz) (s₀ : Sg) : Finite (FirstK α S s₀) :=
  Finite.of_injective (fun k => (k.tail, k.pad, k.W, k.wTail)) fun a b h => by
    cases a; cases b; simp_all
instance [Finite α] (s s' : Sg) : Finite (SwK α s s') :=
  Finite.of_injective (fun k => (k.mainTail, k.free, k.maskTail)) fun a b h => by
    cases a; cases b; simp_all
instance [Finite α] (s : Sg) : Finite (RideK α s) :=
  Finite.of_injective (fun k => (k.W, k.tail)) fun a b h => by cases a; cases b; simp_all
instance [Finite α] (s : Sg) : Finite (WordK α s) :=
  Finite.of_injective (fun k => (k.mainTail, k.main, k.mask, k.maskTail)) fun a b h => by
    cases a; cases b; simp_all

theorem BodyK.finite [Finite α] : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
    Finite (BodyK α cur rest)
  | _, [] => inferInstanceAs (Finite Unit)
  | cur, [next] => inferInstanceAs (Finite (SwK α (sgOf cur) (sgOf next) × WordK α (sgOf next)))
  | cur, next :: n₂ :: rest =>
    haveI := BodyK.finite next (n₂ :: rest)
    inferInstanceAs (Finite (SwK α (sgOf cur) (sgOf next) × RideK α (sgOf next) ×
      BodyK α next (n₂ :: rest)))

theorem BodyK.nonempty (a : α) : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
    Nonempty (BodyK α cur rest)
  | _, [] => ⟨()⟩
  | cur, [next] =>
    ⟨((⟨fun _ _ => a, fun _ => a, fun _ _ => a⟩ : SwK α (sgOf cur) (sgOf next)),
      (⟨fun _ => a, fun _ => a, fun _ => a, fun _ => a⟩ : WordK α (sgOf next)))⟩
  | cur, next :: n₂ :: rest =>
    let ⟨b⟩ := BodyK.nonempty a next (n₂ :: rest)
    ⟨((⟨fun _ _ => a, fun _ => a, fun _ _ => a⟩ : SwK α (sgOf cur) (sgOf next)),
      (⟨fun _ => a, fun _ _ => a⟩ : RideK α (sgOf next)), b)⟩

theorem LinkK.finite [Finite α] (S : Sz) : ∀ l : List Fmt.M1.Stage, Finite (LinkK α S l)
  | [] => inferInstanceAs (Finite Unit)
  | first :: rest =>
    haveI := BodyK.finite (α := α) first rest
    inferInstanceAs (Finite (FirstK α S (sgOf first) × BodyK α first rest))

theorem LinkK.nonempty (a : α) (S : Sz) : ∀ l : List Fmt.M1.Stage, Nonempty (LinkK α S l)
  | [] => ⟨()⟩
  | first :: rest =>
    let ⟨b⟩ := BodyK.nonempty a first rest
    ⟨((⟨fun _ _ _ => a, fun _ => a, fun _ => a, fun _ => a⟩ : FirstK α S (sgOf first)), b)⟩

end

/-! ## The map -/

/-- A family of coefficients by number, at the sizes s₁, read BY NAME at sizes s: where s = s₁ the
name x reads the number wNo x (Johnson/Prover/Link/LinkCoinNo.lean), which lies below 2 k + 1 by
wNo_lt; the written 0 at every other s. -/
def castW (s₁ s : Sg) (w : Fin (2 * (s₁.h + s₁.g) + 1) → GE) :
    HIdx (sVars GE 2 (s.h + s.g)) → GE :=
  open Classical in
  if h : s₁ = s then fun x => w ⟨wNo (s.h + s.g) x, by rw [h]; exact wNo_lt _ x⟩ else fun _ => 0

/-- A state of written zeros. -/
def zeroPS : PS :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
    fun _ => 0⟩

/-- The coefficients of the fold at the stage j + 1 behind cur. -/
def bodyW : (cur : Fmt.M1.Stage) → (rest : List Fmt.M1.Stage) → BodyK GE cur rest → (s : Sg) → ℕ →
    HIdx (sVars GE 2 (s.h + s.g)) → GE
  | _, [], _, _, _ => fun _ => 0
  | _, [_], _, _, _ => fun _ => 0
  | _, next :: _ :: _, k, s, 0 => castW (sgOf next) s k.2.1.W
  | _, next :: n₂ :: rest, k, s, j + 1 => bodyW next (n₂ :: rest) k.2.2 s j

/-- What is handed in behind switch number j from cur on. -/
def bodyNew : (cur : Fmt.M1.Stage) → (rest : List Fmt.M1.Stage) → BodyK GE cur rest → ℕ → PS
  | _, [], _, _ => zeroPS
  | _, [_], k, 0 =>
    { zeroPS with
      tM := at2 k.1.mainTail, tZ := at2 k.1.maskTail
      fM := fun r => if r = 0 then onNat k.2.mask else fun _ => 0
      fT := fun r => if r = 0 then onNat k.2.maskTail else fun _ => 0
      sM := onNat k.2.main, sT := onNat k.2.mainTail }
  | _, [_], _, _ + 1 => zeroPS
  | _, _ :: _ :: _, k, 0 =>
    { zeroPS with tM := at2 k.1.mainTail, tZ := at2 k.1.maskTail, fT := at2 k.2.1.tail }
  | _, next :: n₂ :: rest, k, j + 1 => bodyNew next (n₂ :: rest) k.2.2 j

/-- The entries of the new mask table that are not carried, by the table's own index. -/
def freeAt {s s' : Sg} (k : SwK GE s s') (i : ℕ) : GE :=
  if maskUsed s ≤ i then onNat k.free (i - maskUsed s) else 0

/-- The free room of switch number j from cur on. -/
def bodyFr : (cur : Fmt.M1.Stage) → (rest : List Fmt.M1.Stage) → BodyK GE cur rest → ℕ → ℕ → GE
  | _, [], _, _ => fun _ => 0
  | _, [_], k, 0 => freeAt k.1
  | _, [_], _, _ + 1 => fun _ => 0
  | _, _ :: _ :: _, k, 0 => freeAt k.1
  | _, next :: n₂ :: rest, k, j + 1 => bodyFr next (n₂ :: rest) k.2.2 j

/-- **The map into the strategy's letters.** -/
def coinsOf (S : Sz) : (l : List Fmt.M1.Stage) → LinkK GE S l → LCoins
  | [], _ =>
    ⟨fun _ => 0, fun _ _ _ => 0, fun _ => 0, ⟨fun _ _ _ => 0, fun _ => zeroPS, fun _ _ => 0⟩⟩
  | first :: rest, k =>
    { pad := k.1.pad
      tN := fun a => at2 (k.1.tail a)
      ψN := onNat k.1.wTail
      body :=
        { W := fun s j =>
            match j with
            | 0 => castW (sgOf first) s k.1.W
            | j + 1 => bodyW first rest k.2 s j
          new := bodyNew first rest k.2
          fr := bodyFr first rest k.2 } }

/-! ## ONE PUBLIC TEST: the sizes fit -/

/-- Two codes are one, number by number. -/
def sameCode (a b : Fmt.M1.Code) : Bool := a.a == b.a && a.l == b.l && a.r == b.r

/-- **THE SIZES FIT.** Nine clauses, all on public numbers:
(1) the list of stages is the plan's own, which linkAll reads (else castW lays written zeros for the
coefficients) · (2) the plan has one answer to a sample · (3) THE LIBRARY's OWN TEST ON A PROXIMITY
TEST's STAGES at one answer (sizesOk, Johnson/Desc/K12/Sizes.lean: the first conjunct of the test on
the plan of the structure Block that proximityTestKind makes, Johnson/Desc/K12/Frame.lean) · (4), (5) the two
parts of a folded row's vector, the fold of the messages and the fold of the tails, AND ONE ENTRY
MORE, the pad's, have room in the R rows (the structure Sz has the two without the "+ 1": fitM,
fitT, OnBytes/Slice/LinkAt.lean) · (6), (7) the first stage's two codes are the front's · (8) its
fresh table has one row · (9) its k is the front's aR + 1: the two members' blocks of 2 ^ aR rows
fill its 2 ^ k rows. -/
def kFits (P : P15) (S : Sz) (l : List Fmt.M1.Stage) : Bool :=
  decide ((p12Of P).nums.stages = l) && (p12Of P).answers == 1 && sizesOk l 1 &&
    decide (S.P.T.l + 1 ≤ S.P.R * S.P.C.l) && decide (S.P.t0 + S.P.T.r + 1 ≤ S.P.R * S.P.C.l) &&
    match l with
    | [] => false
    | first :: _ =>
      sameCode S.P.C first.C && sameCode S.P.Z first.Z && first.h == 0 && first.k == S.P.aR + 1

/-! ## The counts -/

def frontN (S : Sz) (s₀ : Sg) : ℕ :=
  2 * (S.P.R * S.P.C.r + 1) + (2 * (s₀.h + s₀.g) + 1) + S.P.Z.r
def swN (s s' : Sg) : ℕ :=
  2 ^ (s'.h + s'.g) * s'.C.r + Fmt.M1.fillOf s.st s'.st + 2 ^ s'.h * s'.Z.r
def rideN (s : Sg) : ℕ := (2 * (s.h + s.g) + 1) + 2 ^ s.h * s.Z.r
def wordN (s : Sg) : ℕ := s.C.r + s.C.l + s.Z.l + s.Z.r
def bodyN : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ
  | _, [] => 0
  | cur, [next] => swN (sgOf cur) (sgOf next) + wordN (sgOf next)
  | cur, next :: n₂ :: rest =>
    swN (sgOf cur) (sgOf next) + rideN (sgOf next) + bodyN next (n₂ :: rest)
def linkN (S : Sz) : List Fmt.M1.Stage → ℕ
  | [] => 0
  | first :: rest => frontN S (sgOf first) + bodyN first rest

/-! ## At the written letters, the full size -/

/-- **The type.** -/
def Kc : Type := LinkK GE frS (p12Of frP).nums.stages
instance : Fintype Kc :=
  haveI : Finite Kc := LinkK.finite _ _
  Fintype.ofFinite _
instance : Nonempty Kc := LinkK.nonempty 0 _ _

/-- **The map.** -/
def coinsFull : Kc → LCoins := coinsOf frS (p12Of frP).nums.stages

set_option maxRecDepth 100000 in
/-- The sizes fit there. A closed fact on public numbers, by the kernel's evaluation. -/
theorem fr_kFits : kFits frP frS (p12Of frP).nums.stages = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The count there. A closed fact on public numbers, by the kernel's evaluation. -/
theorem fr_linkN : linkN frS (p12Of frP).nums.stages = 26840 := by decide +kernel

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.BodyK.finite
#print axioms Johnson.Prover.Link.BodyK.nonempty
#print axioms Johnson.Prover.Link.LinkK.finite
#print axioms Johnson.Prover.Link.LinkK.nonempty
#print axioms Johnson.Prover.Link.fr_kFits
#print axioms Johnson.Prover.Link.fr_linkN
