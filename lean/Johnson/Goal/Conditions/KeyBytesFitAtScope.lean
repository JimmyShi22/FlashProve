-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Conditions/KeyBytesFitAtScope.lean: AT EVERY THREE PUBLIC FILES IN THE GOALS' SCOPE THE
PARAMETER BYTES OF THE KEY's ONE-TIME CHAIN ARE FEWER THAN 2 ^ 64: the test `keyBytesFitB`
(Johnson/Flat/PlanDepthZero.lean) says yes there.

Why. `bigZFull_oneLeaf` gives "the key's binding tree has one leaf" from that test's yes; whoever
pays the key file's hypothesis on soundness at the named description is handed the scope alone.
How. The bytes are `Fmt.paramsBytes P1.plan cfg (oneTimeItems z)` (`configure_oneTime_bytes`); in
scope z is the typed value `keyFull` (`key_eq_at_scope`,
  Johnson/Goal/PlanValues/KeyFullAtScope.lean); the
plan's entries are the list `oneTimeListAt keyFull n L` (`oneTimePlan_is`,
OnBytes/Plan/PlanListsKey.lean); an entry's size reads of its round the name alone (`size_round`);
n and L stand in two sendings only, whose names are fixed: so the sum of the sizes is a closed
number (`wtKey keyFull`), which the kernel counts; so are the five items' sizes.
  `RoundSpec.nm` `wtS` `wtL`   a described round's name; its entry's size; a list's
  `configure_oneTime_bytes`  what `configure` spells for the key's one-time chain
  `wtL_oneTimeListAt`        the list's size does not hang on n or L
  `wtKey_full` `ranges_full` `others_full` `names_small`   four evaluations in the kernel
  `size_spellRanges`         the long item's size as sums, so that its bytes are never laid in a row
  `keyOneTime_size_at_scope` **fewer than 2 ^ 23 bytes**
  `keyBytesFit_at_scope`     **the test says yes at every Z in scope**
  `oneLeaf_at_scope`         so `(bigZFull ⟨Z.pol, Z.lay, Z.KL⟩).k.oneTime.binding.logLeaves = 0`
Limits. One direction: where the planner refuses the test says yes by its text. Nothing on
  soundness.

-/
import Johnson.Goal.PlanValues.KeyFullAtScope
import Johnson.Flat.PlanDepthZero
import Johnson.Flat.ParamsSize
import OnBytes.Plan.PlanListsKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- A described round's name. -/
def RoundSpec.nm : RoundSpec → String
  | .said name _ _ _ _ _ _ => name
  | .silent name _ _ => name
  | .record _ _ _ => "RECORD"

/-- The size of the entry that a described round gets in a plan's bytes. -/
def wtS (y : RoundSpec) : Nat := 96 + (Fmt.ascii y.nm).size

/-- The size of a list's entries. -/
def wtL (l : List RoundSpec) : Nat := (l.map wtS).sum

theorem wtL_append (a b : List RoundSpec) : wtL (a ++ b) = wtL a + wtL b := by
  unfold wtL
  rw [List.map_append, List.sum_append]

theorem wtL_cons (y : RoundSpec) (l : List RoundSpec) : wtL (y :: l) = wtS y + wtL l := by
  unfold wtL
  rw [List.map_cons, List.sum_cons]

/-- An entry's size reads of its round the name alone. -/
theorem size_round (s : Setting) (c : Scope) (y : RoundSpec) :
    (y.round s c).entry.bytes.size = wtS y := by
  rw [Fmt.size_entry]
  cases y <;> rfl

theorem sum_rounds (s : Setting) (c : Scope) (l : List RoundSpec) :
    ((l.map fun y => (y.round s c).entry).map fun e => e.bytes.size).sum = wtL l := by
  unfold wtL
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun y _ => size_round s c y

/-- What `configure` spells for the key's one-time chain: the plan that `oneTimePlan` returned. -/
theorem configure_oneTime_bytes {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    ∃ P1, Plan.oneTimePlan made.sized.key = .ok P1 ∧
      made.keyOneTime = Fmt.paramsBytes P1.plan cfg (Plan.oneTimeItems made.sized.key) := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨P1, h1, h⟩ := exc_bind h
  obtain ⟨P2, h2, h⟩ := exc_bind h
  obtain ⟨P3, h3, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    exact ⟨P1, h1, rfl⟩
  · cases h

end OnBytes.Params

namespace OnBytes.Plan
open OnBytes.Params

/-- The size of a sending's two entries. -/
def wtSend : Nat := (96 + (Fmt.ascii "SEND seed").size) + (96 + (Fmt.ascii "SEND answer").size)

theorem wtL_sendList (s : Setting) (o : List SampleSize) (roots : Nat) :
    wtL (sendList s o roots) = wtSend := by
  unfold sendList
  rw [wtL_cons, wtL_cons]
  rfl

/-- The size of the entries of the plan of a key's one-time chain: of the sizes alone. -/
def wtKey (z : KeySized) : Nat :=
  wtL (recordList z.set z.once.table) + (wtSend + ((wtSend +
    (wtL ((lookupSizes z.ranges.x z.ranges.matrix).map (lookupList z.set)).flatten +
      (wtL (ioppList z.set .once z.ranges.test.stages (Wf.rowsBatched z.ranges.x z.ranges.matrix)
          (if z.ranges.x.choice.masksRide then 0 else 1) z.ranges.x.choice.masksRide) +
        wtL (if 1 < z.ranges.pending then
          .said "BAT-sigma" .field (powersError z.set z.ranges.pending)
              { drawE := 1, rows := z.ranges.pending, priced := .asSaid } 0 0 0 ::
            pscList z.set { degree := List.replicate z.ranges.matrix.kCol 3, withY := false }
        else [])))) + (wtSend + wtL [sealRound])))

/-- **The list's size does not hang on n or L.** -/
theorem wtL_oneTimeListAt (z : KeySized) (n : Nat) (L : LinSize) :
    wtL (oneTimeListAt z n L) = wtKey z := by
  unfold oneTimeListAt rangesListAt wtKey
  simp only [wtL_append, wtL_sendList]

end OnBytes.Plan

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Plan

/-- The kernel counts the entries' bytes at the typed sizes. -/
theorem wtKey_full : wtKey keyFull < 2 ^ 22 := by decide +kernel

/-- The item "ranges" is long (some 39,000 bytes): its size as sums over its lookups, their parts
and these parts' runs, so that the kernel never lays the bytes in a row. -/
theorem size_spellRanges (x : WfPublic) : (spellRanges x).size =
    (8 + (x.lookups.map fun l =>
      (spellRow [l.d, l.mu, l.live]).size + (Fmt.list Fmt.elt l.digitWeight).size +
        (Fmt.elt l.offset).size + (Fmt.elt l.paddingKey).size +
        (8 + (l.parts.map fun p => 8 + (8 + (p.runs.map fun r => (spellRun r).size).sum)).sum) +
        (spellWords l.firstBound).size).sum) +
      (spellNotice x.message).size + 8 + (spellStages x.stages).size +
      (spellChoice x.choice).size := by
  unfold spellRanges
  simp only [ByteArray.size_append, Fmt.size_list, spellLookup, spellPart, spellWord,
    Fmt.size_u64n]

theorem ranges_full : (spellRanges keyFull.ranges.x).size < 2 ^ 17 := by
  rw [size_spellRanges]
  decide +kernel

/-- The kernel counts the other four items' bytes, and the five names'. -/
theorem others_full :
    (Fmt.ascii "index-mask message").size + (spellNotice keyFull.once.input).size +
      (Fmt.ascii "ranges").size + (Fmt.ascii "binding tree").size +
      (spellBinding keyFull.binding).size + (Fmt.ascii "codes").size +
      (spellCodes keyFull.codes).size + (Fmt.ascii "the test on the table").size +
      (spellLin keyFull.once.shape).size < 2 ^ 16 := by
  decide +kernel

/-- The five items' bytes, as a sum: at a letter. -/
theorem sum_items (z : KeySized) :
    ((oneTimeItems z).map fun x => (Fmt.item x.1 x.2).size).sum =
      (16 + (Fmt.ascii "index-mask message").size + (spellNotice z.once.input).size) +
        ((16 + (Fmt.ascii "ranges").size + (spellRanges z.ranges.x).size) +
          ((16 + (Fmt.ascii "binding tree").size + (spellBinding z.binding).size) +
            ((16 + (Fmt.ascii "codes").size + (spellCodes z.codes).size) +
              ((16 + (Fmt.ascii "the test on the table").size + (spellLin z.once.shape).size) +
                0)))) := by
  unfold oneTimeItems
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fmt.size_item]

/-- The five items' bytes at the typed sizes. -/
theorem items_full :
    ((oneTimeItems keyFull).map fun x => (Fmt.item x.1 x.2).size).sum < 2 ^ 18 := by
  have r := ranges_full
  have o := others_full
  rw [sum_items]
  omega

theorem names_small :
    (Fmt.ascii Fmt.versionName).size + (Fmt.ascii Fmt.configName).size < 2 ^ 10 := by
  decide +kernel

/-- **In scope the parameter bytes of the key's one-time chain are fewer than 2 ^ 23.** -/
theorem keyOneTime_size_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    (p.chains.bytes .keyOneTime).size < 2 ^ 23 := by
  have h32 := (Model.Verify.planned_spelled hp).1
  have hk := key_eq_at_scope hZ hp
  have hm : ∃ l x bits, configure l x p.cfg bits = .ok p.chains.made := by
    have h := hp
    unfold Model.Verify.planned at h
    obtain ⟨X, _, h⟩ := exc_bind h
    dsimp only at h
    obtain ⟨chains, hc, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    obtain ⟨shapes, hm⟩ := Model.Verify.chainsOf_made hc
    exact ⟨_, _, _, hm⟩
  obtain ⟨l, x, bits, hm⟩ := hm
  obtain ⟨P1, h1, e1⟩ := configure_oneTime_bytes hm
  rw [hk] at h1 e1
  obtain ⟨n, L, _, _, _, hP⟩ := oneTimePlan_is h1
  have b1 : p.chains.bytes .keyOneTime = p.chains.made.keyOneTime := rfl
  rw [b1, e1, Fmt.size_paramsBytes, h32, hP.entries, sum_rounds, wtL_oneTimeListAt]
  have a1 := wtKey_full
  have a2 := items_full
  have a3 := names_small
  omega

end Lk6.AtPlan

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.K OnBytes.K.ArmsAtFiles

/-- **The test on the bytes says yes at every three public files in the goals' scope.** -/
theorem keyBytesFit_at_scope (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.InScope Z = true) :
    keyBytesFitB ⟨Z.pol, Z.lay, Z.KL⟩ = true := by
  unfold keyBytesFitB
  cases hp : OnBytes.Flat.planOf ⟨Z.pol, Z.lay, Z.KL⟩ with
  | error e => rfl
  | ok p =>
    have h := Lk6.AtPlan.keyOneTime_size_at_scope hZ (p := p) hp
    exact decide_eq_true (Nat.lt_trans h (by decide))

/-- So in scope the key's binding tree has one leaf in the data made of the three files. -/
theorem oneLeaf_at_scope (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.InScope Z = true) :
    (bigZFull ⟨Z.pol, Z.lay, Z.KL⟩).k.oneTime.binding.logLeaves = 0 :=
  bigZFull_oneLeaf (keyBytesFit_at_scope Z hZ)

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Params.configure_oneTime_bytes
#print axioms OnBytes.Plan.wtL_oneTimeListAt
#print axioms Lk6.AtPlan.wtKey_full
#print axioms Lk6.AtPlan.ranges_full
#print axioms Lk6.AtPlan.others_full
#print axioms Lk6.AtPlan.items_full
#print axioms Lk6.AtPlan.keyOneTime_size_at_scope
#print axioms VerifiableInference.OnPublicFiles.keyBytesFit_at_scope
#print axioms VerifiableInference.OnPublicFiles.oneLeaf_at_scope
