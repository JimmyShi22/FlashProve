-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Statement.lean: THE OUTPUT HEAD's LAW, THE HEAD's HALF, AS CLOSED PROPOSITIONS: a
proposal for the row K06_law of the list of laws owed. Definitions and nothing else. STATED, NOT
PROVED. ON THE FORM OF THE STATEMENTS: (i) WeightsOk.ew is asked BELOW A KEY's LENGTH
alone and WeightsOk.below AT v ≤ V alone: beyond these the block's actual letters hold 0 and the right
sides need not: asked beyond them, no real run could pay the premise ·
(ii) WeightTrue is over atWorld, like all else ·


(iii) TWO LAWS: OUT, TO THE LOOKUP (with the rule) and BACK, FROM THE LOOKUP (no chance) · (iv) TrueReads
is asked BELOW EACH READ's LENGTH alone (`readLen`): at the record the reads' entries lie one behind
the other in one array (HeadSeatAt.lean: position = the read's base + i), so beyond its length a
read's entry is another read's. NOT COMPARED: `readLen`'s numbers are the matrices' numbers of
features as HeadPublic.lean tells them; that the plan's table of reads gives each read at least so
long a stretch (it counts the committed matrices' padded sizes) is for whoever pays TrueReads · (v)
Lemma 2b IS STATED AT THESE LETTERS AND THIS MEASURE, BY NAME (K06CoreStatement)
· the claims are judged AT ANY LEDGER G THAT IS LATER than the one behind the sumcheck (the
relation `Later`, OnBytes/Tie/Pv/Psc/PscLater.lean) · OUT is also stated AT THE BLOCK's ACTUAL
LETTERS, WeightsOk paid (K06OutAtLookupStatement).

WHY. Lemma 1, 2a and 2b (HeadLaw.lean) start at a relation on committed cells at corners, in which
the reads and the claimed sum are FILLED IN AS CONSTANTS at their true values (`formAt`). The block's
claims are forms WITH hidden scalars and entries of reads, judged at the hidden values and at what
was sent. Here the two are tied (THE GLUE), and the three lemmas are laid together over the block's
own named runs of claims, in the two directions in which the block deals with the lookup (OUT, BACK).

THE SHAPE. NOT that of ClaimsSay (Desc/Sound/ChainRule.lean: no rule, no error, one run). CORE and OUT
have a rule on raw rounds: what the rule of composition asks of this block's piece is round-by-round
knowledge soundness at a list of errors (ChainRule.lean: PieceGood | BK.Good). THE BRIDGE "a rule with
a ceiling ⇒ Know at that error" IS NOT HERE: it is other files' to show, one for all
kinds with a sumcheck. The rule runs from behind to in front, and the lookup stands IN FRONT of this
block: OUT is this block's piece; BACK is spent in front of the lookup: so mean = 0, count = 0, the
read rowCount's truth, small and the bounds must ride as "Rest" through this block's and the lookup's
relations. THE LOOKUP IS PAID BY THE CALL, not by the key (one join over all calls; calls 0 and 2 mix
in the normalization's keys): the law per call, with the padding's term, is for others of K6's files
to show; until the normalization's four keys have their OUT no field of CornerKeys has a payer.
clip = 0 and table = 0 of the run "policy" are spent by the rider's law: the lookup's files'.
WHAT OTHER KINDS ARE TO LEAVE STANDS AS NAMED PREMISES, each with its payer:
  TrueReads     K8, the range check: each sent read's entry, below the read's length, is its true
                weighted sum of cells
  small         K8: every cell is below 2^18 in size
  WeightTrue    K11, the merge: the second end value is the named sum over the committed weights
                (NOT COMPARED with what K11's maker has proved: G_head_says)
  CornerKeys    K3, the lookup: every corner key is a row of its table; the row's 21 digits are bytes
  CornerGuests  K3 as host, the rider: clip and table are 0 at every position's corner
  WeightsOk     K6: PAID (HeadInLaw.lean: FromLookupStatement): the
                letters that come in from the lookup's points are the weights that they are taken
                for, under PointsOk
  PointsOk      the block's own third test (HeadFrame.lean: given; with its clause on the key
                points' LENGTHS); that real points pass
                it: K3CallsShareThePoint
  |Wh| ≤ 2^12   NO PAYER: no test, no kind, no request's proof shows it. Where it is
                to stand is not this file's to say.
  |act| ≤ 2047  the normalization's half (lemma1N's act_le)
  Canonical     the test on the view in front of all blocks
  WellLaid      the verifier's own making of the ledger

WHAT IT DOES NOT SAY. The normalization's half (CellRelN): its own statement. That the claims are 0:
the batching's and the last equation's laws. y IS A FREE LETTER under y < V, tied to no seat here (the
next token's laws stand beside). small, the weights' bound and TableOk are asked AT EVERY INDEX (so
they stand in HeadLaw.lean): payable only by a payer that lays the cells 0, and tab at least 1, beyond
the bounds; and all payers must speak of THE SAME cells. THE LEDGER: that the ledger at which the
batching judges IS later than F1: each block's own law (this block's: Keeps.lean; F1 is the ledger
that this block lays: hear_last). bad sees the head's own tail of the block's rounds: who joins
shifts it by the normalization's rounds. TIME: that cells, mask entries and F0 are fixed before the first
draw is said by the order of the letters alone. How probable a bad draw is: lists are counted.
-/
import OnBytes.Tie.Pv.Psc.PscLater
import Johnson.Desc.Kinds.HeadLaw
import Johnson.Desc.Kinds.HeadInLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)

/-- A form at the hidden scalars AND at the sent reads. ent: entry idx of virtual row `row` of array
`tree`, as it was sent. -/
def atWorld (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) (f : Form) : E :=
  f.ents.foldl (fun s x => s + x.coef * ent x.tree x.row x.idx) (atHidden F mask f)

variable [Sizes] [Policy] [Request] [Token]

/-- The number of a read's entries. The matrices' numbers of features are HeadPublic.lean's: wide:
4 d and six limbs for each of JV vocabulary entries; act: two limbs a feature; row: the
normalization's NR digits and the head's 21. A read under long weights has an entry for each block of
S2 features, one under short weights an entry for each feature. -/
def readLen : Read → Nat
  | .wideAtKeys | .wideAtCosts => (4 * d + 6 * JV) / S2
  | .actAtLogits => 2 * d
  | .rowAtCosts | .rowCount => NR + 21

section Letters
variable [FinalNorm.In] [In]

/-- The letters that come in are the weights that they are taken for: BELOW A KEY's LENGTH an entry's
weight is its block's times the equality weight of zl at its place in the block; the three sums are
sums of the entries' weights. -/
structure WeightsOk : Prop where
  ew : ∀ k x, x < len k → In.ew k x = ewh k (x / S2) * eq FinalNorm.zl (x % S2)
  wsum : ∀ k, In.wsum k = ∑ x < len k, In.ew k x
  wx : ∀ k, In.wx k = ∑ x < len k, if first k + x < V then In.ew k x else 0
  below : ∀ v, v ≤ V → In.below v = ∑ x < v, In.ew .marginTop x

/-- The point of HeadLaw.lean's lemmas, of the letters. -/
def ptOf : Pt := { zt := FinalNorm.zt, zl := FinalNorm.zl, ewh := ewh }

variable [Heard]

/-- K11's: the second end value's hidden scalar is the sum that the claim on the weights names. -/
def WeightTrue (c : Cells) (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) : Prop :=
  atWorld F mask ent forTheMerge.value.var =
    (∑ v < V, ∑ k < d, forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k * ofInt (c.Wh k v))

variable [Reads]

/-- K8's: each sent read's entry, below the read's length, is its true weighted sum of cells. -/
def TrueReads (c : Cells) (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) : Prop :=
  ∀ r i, i < readLen r → atWorld F mask ent (entry r i) = readAt c r.of i

end Letters

/-- K3's: what the lookup is to leave of the head's five keys, and of the normalization's key
`digits` at the head's 21 entries: CellRel's fields of these names. -/
structure CornerKeys (c : Cells) (tab : Nat → Nat) : Prop where
  bytes : ∀ t, t < T → ∀ j, j < 21 →
    0 ≤ c.cell .row (NR + j) t + 128 ∧ c.cell .row (NR + j) t + 128 < 256
  top : ∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c (corner x t) .marginTop)
  mid : ∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c (corner x t) .marginMid)
  low : ∀ t, t < T → ∀ x, x < JV → InBits 8 (keyAt c (corner x t) .marginLow)
  rowA : ∀ t, t < T → ∀ x, x < len .tableA → IsRow tab (keyAt c (corner x t) .tableA)
  rowB : ∀ t, t < T → ∀ x, x < len .tableB → IsRow tab (keyAt c (corner x t) .tableB)

/-- The rider's: the two guests are 0 at every position's corner. -/
def CornerGuests (c : Cells) : Prop :=
  ∀ t, t < T → clipAt c (corner 0 t) = 0 ∧ tableAt c (corner 0 t) = 0

/-- **THE GLUE.** No chance in it. At letters that are the weights they are taken for, with the reads
true and the claimed sum's hidden scalar true: each key and each of the policy's four forms, AT THE
HIDDEN SCALARS AND THE SENT READS, is the element that HeadLaw.lean's lemmas speak of. With Lemma 2a:
it is the sum of its corner values under the weights: what the lookup and its rider take from us. -/
def K06GlueStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Heard] [Reads] (c : Cells) (F : Fork)
    (mask : Nat → E) (ent : Nat → Nat → Nat → E),
    Request.ok = true → y < V → WeightsOk → (FinalNorm.zt).size = lt →
    TrueReads c F mask ent →
    (2 ^ lPd : E) * atWorld F mask ent logits.claimed.var = trueSum c →
    (∀ k, atWorld F mask ent (key k) = keyAt c ptOf k) ∧
      atWorld F mask ent clip = clipAt c ptOf ∧ atWorld F mask ent table = tableAt c ptOf ∧
      atWorld F mask ent mean = meanAt c ∧ atWorld F mask ent count = countAt c

/-- **THE CORE: LEMMA 2b AT THE LETTERS THAT CAME IN AND AT THE SENT READS.** HERE THE CHANCE IS. The
letters in front of `∃ bad` are fixed before the head's sumcheck is heard. bad: a rule from the front
of a transcript to a list of elements, with Lemma 2b's ceiling. Then: at a hearing of the sumcheck
that returns with the ledger F1, AT ANY LEDGER G LATER THAN F1: the block's run "logits" (`claims`, by
name) 0 at the hidden scalars and the sent reads, the reads true, the claim on the weights true, and
no bad draw: 2^lPd times the claimed sum's hidden scalar is the true sum. AGAINST HeadLaw.lean's Lemma
2b: the weights are the letters In, not a point's filling; the reads are forms with entries, judged
at what was sent, not constants; the measure is atWorld, not atHidden. It asks nothing of the weights
(no WeightsOk): UH and the claim on the weights read the same letters. -/
def K06CoreStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Cells) (mask : Nat → E) (F0 : Fork),
    Request.ok = true → y < V → WellLaid F0 → (FinalNorm.zt).size = lt →
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
        [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] [Reads],
        Canonical t →
        sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) → Later F1 G →
        let _ : Heard := { logits := S }
        TrueReads c G mask ent → WeightTrue c G mask ent →
        (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
        NoBad bad t →
        (2 ^ lPd : E) * atWorld G mask ent logits.claimed.var = trueSum c

/-- **OUT, TO THE LOOKUP.** The core's premises, and the letters are the weights that they are taken
for: WHAT THE BLOCK HANDS THE LOOKUP AT ITS POINT IS THE SUM OF THE CORNER VALUES UNDER THE BLOCK's OWN
WEIGHTS: each of the five keys; and the two guests under the weights of zt. The corner values are
functions of the cells and of public data alone (Lemma 2a's). The top digit's key holds the claimed
sum: that is where the core is spent. -/
def K06OutStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Cells) (mask : Nat → E) (F0 : Fork),
    Request.ok = true → y < V → WellLaid F0 → WeightsOk → (FinalNorm.zt).size = lt →
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
        [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] [Reads],
        Canonical t →
        sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) → Later F1 G →
        let _ : Heard := { logits := S }
        TrueReads c G mask ent → WeightTrue c G mask ent →
        (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
        NoBad bad t →
        (∀ k, atWorld G mask ent (key k) =
          ∑ x < len k, ∑ t < T, In.ew k x * eq FinalNorm.zt t * keyAt c (corner x t) k) ∧
        atWorld G mask ent clip = (∑ t < T, eq FinalNorm.zt t * clipAt c (corner 0 t)) ∧
        atWorld G mask ent table = (∑ t < T, eq FinalNorm.zt t * tableAt c (corner 0 t))

/-- **OUT, TO THE LOOKUP, AT THE BLOCK's ACTUAL LETTERS**: In laid as HeadIn.lean's `fromLookup` makes it
of the lookup's point zx and the calls' key points zk. WeightsOk and zt's length are paid; in their
place, on the carried record and public numbers alone: PointsOk; every key's length below 2^41;
S2 | JVa. -/
def K06OutAtLookupStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (floor : Nat) (zx : Point) (zk : Nat → Point) (c : Cells)
    (mask : Nat → E) (F0 : Fork),
    Request.ok = true → y < V → WellLaid F0 →
    (∀ k, lenOf k < 2 ^ 41) → S2 ∣ JVa → PointsOk floor zx zk →
    let _ := (fromLookup floor zx zk).norm
    let _ := (fromLookup floor zx zk).head
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
        [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] [Reads],
        Canonical t →
        sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) → Later F1 G →
        let _ : Heard := { logits := S }
        TrueReads c G mask ent → WeightTrue c G mask ent →
        (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
        NoBad bad t →
        (∀ k, atWorld G mask ent (key k) =
          ∑ x < len k, ∑ t < T, In.ew k x * eq FinalNorm.zt t * keyAt c (corner x t) k) ∧
        atWorld G mask ent clip = (∑ t < T, eq FinalNorm.zt t * clipAt c (corner 0 t)) ∧
        atWorld G mask ent table = (∑ t < T, eq FinalNorm.zt t * tableAt c (corner 0 t))

/-- **BACK, FROM THE LOOKUP.** NO CHANCE IN IT, and no rule. What the lookup and its rider leave at the
corners, what the range check leaves, and mean and count (the first two forms of the block's run
"policy") 0 at the hidden scalars and the sent reads: the relation on cells of Lemma 1 holds, and
with it (a), (b), (c). Eight of the relation's nine fields ARE premises here, under their payers'
names; the ninth is won from mean and count. -/
def K06BackStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat) (c : Cells),
    planOk sT = true → Request.ok = true → y < V → TableOk tab →
    (∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) →
    (∀ t, t < T → ∀ k, k < d → (act c t k).natAbs ≤ 2047) →
    ∀ (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) [FinalNorm.In] [In] [Heard] [Reads],
      (∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) → TrueReads c F mask ent →
      atWorld F mask ent mean = 0 → atWorld F mask ent count = 0 →
      CornerKeys c tab → CornerGuests c →
      CellRel c tab ∧ Says c

end VerifiableInference.Desc.Kinds.Head.Law
