-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/KeyPin.lean: the two readings of a key file with the public digests laid in and NO table
of any hash function in their terms: the key file's part pinned at three strings alone; the key's
reading with no pin at all.

OnBytes/Tie/Decl/KeyPre.lean and OnBytes/Tie/Decl/KeyHead.lean have the two readings `preT` and
`preK` pinned at every string that has a property Pt, by a table that must then say something at
every such string. At Pt := "the string of a call with the number 169" a tie to the program asks
that table to hold the fixed hash function's own answers at all these strings: so a term that serves
both a bound over a drawn function and the tie holds that function's table as a constant. By
OnBytes/Tie/Decl/KeyAsks169.lean the key file's asking reading asks three such strings and no other,
and the derivation of a table's seeds asks none. So three answers are enough for the first, and none
for the second. Definitions, statements and proofs.

Main names:
  `setK k`, `mem_setK`, `setK_169`: the strings of the calls on the parameter bytes of k's three
  chains.
  `tab3 e k`: the table made of three digests e: no filler: it says the third wherever the first two
  tests fail.
  `preTQ key3 cfgOf ksAt asm`: `preT`'s text with the pin at `setK` and the table `tab3 (key3 d)`.
  `preTQ_off` (it asks no string of a call with the number 169), `preTQ_noCoin`, `preTQ_asks_one`
    (`preT_asks_one`'s number): no premise beyond that law's.
  `preTQ_det`: under EVERY family of oracle functions its value is `preT`'s at that property, at
    every table that holds the three digests at the three strings, whatever else it holds (asked
    at the given d alone, and at the parameters that the plain steps return on the given file): so
    every law on `preT`'s value carries over.
  `preTQ_unseen`: where the three digests are g's own answers, its value under g is that of the
  unpinned reading.
  `preKQ cfgOf f sh mk`: `preK`'s text without a pin. `preKQ_off`, `preKQ_noCoin`, `preKQ_asks`: no
  premise.
  `preKQ_det`: under every family its value is `preK`'s at that property, at every table.
Limits: cfgOf, ksAt, asm, mk and key3 are letters. Nothing on what the readings return. That two of
the three strings may be one string is not shut out: then the earlier test wins. No probability.
Nothing on soundness.
"No table of any hash function" is said of tables. ksAt is a letter; at the use that
OnBytes/Tie/Decl/KeyPre.lean names for it, it is the planner's text, and with it a fixed hash, the
format's earlier one, comes into the terms beside the drawn function.
The planner's text (`plannedAt`) hashes with it at seven places, which read the three public files
alone (the head of OnBytes/K/TopG.lean counts them): constants where the three public files are
fixed before g is drawn (a reader's count at `publicOf`'s text; no theorem).
No file that the prover names is hashed with it in a key file's reading.

-/
import OnBytes.Tie.Decl.DetCongr
import Johnson.Top.Pub.ReaderPin
import OnBytes.Tie.Decl.KeyAsks169
import OnBytes.Tie.Decl.KeyHead
import OnBytes.KeyLink.KeyCountOne

set_option autoImplicit false

noncomputable section

namespace OnBytes.Tie

open Rom
open OnBytes.Params (TableName KeyChains IndexShape)
open OnBytes.Proof (TailRead)
open OnBytes.Slice (IsCall169 pinOn det_pinOn queryBound_pinOn noCoin_pinOn)
open OnBytes.KeyLink (keyCount typedKR_asks1 headAt_ks)
open _root_.Iop (Dig)
open _root_.Run (digToBytes)

/-- The three strings. -/
def setK (k : KeyChains) : Finset (List Bool) :=
  {strPar k.oneTime.given.bytes, strPar k.shared.given.bytes, strPar k.second.given.bytes}

theorem mem_setK {k : KeyChains} {s : List Bool} :
    s ∈ setK k ↔ s = strPar k.oneTime.given.bytes ∨ s = strPar k.shared.given.bytes ∨
      s = strPar k.second.given.bytes := by
  unfold setK
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Each is the string of a call with the number 169. -/
theorem setK_169 {k : KeyChains} {s : List Bool} (h : s ∈ setK k) : IsCall169 s := by
  rcases mem_setK.1 h with e | e | e <;> subst e <;>
    exact ⟨0, 0, 1, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

/-- The table made of three digests. -/
def tab3 (e : Dig 256 × Dig 256 × Dig 256) (k : KeyChains) : List Bool → Dig 256 := fun s =>
  if s = strPar k.oneTime.given.bytes then e.1
  else if s = strPar k.shared.given.bytes then e.2.1 else e.2.2

section Part
variable {D Out : Type} (key3 : D → Dig 256 × Dig 256 × Dig 256) (cfgOf : D → Dig 256)
  (ksAt : ByteArray → Option KeyChains)
  (asm : KeyChains → ByteArray → TableName → TailRead → Option Out)

/-- **The key file's part, pinned at three strings.** -/
def preTQ (d : D) (keyFile : ByteArray) : OComp (rom 256) (Option Out) :=
  match headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => .pure none
  | some a => pinOn (setK a.1) (tab3 (key3 d) a.1)
      (typedKR (asm a.1 keyFile a.2.1) a.1 a.2.1 keyFile a.2.2)

/-- **It asks no string of a call with the number 169.** -/
theorem preTQ_off (d : D) (keyFile : ByteArray) :
    (preTQ key3 cfgOf ksAt asm d keyFile).AsksIn fun _ (s : List Bool) => ¬ IsCall169 s := by
  unfold preTQ
  cases headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => trivial
  | some a =>
    exact OComp.AsksIn.mono (fun _ s hs h9 => hs.2 (mem_setK.2 (hs.1 h9)))
      (OnBytes.K.Arm.Pub.asksIn_pinOn_and _ _ _ _
        (keyOnly169 (asm a.1 keyFile a.2.1) a.1 a.2.1 keyFile a.2.2))

theorem preTQ_noCoin (d : D) (keyFile : ByteArray) :
    (preTQ key3 cfgOf ksAt asm d keyFile).NoCoin := by
  unfold preTQ
  cases headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => trivial
  | some a => exact noCoin_pinOn _ _ _ (typedKR_noCoin _ _ _ _ _)

/-- **One number at every digest and every file.** -/
theorem preTQ_asks_one (K₀ : KeyChains) (t₀ : TableName)
    (hw : ∀ d k, ksAt (digToBytes (cfgOf d)) = some k → k.wipe = K₀.wipe) (d : D)
    (keyFile : ByteArray) :
    (preTQ key3 cfgOf ksAt asm d keyFile).QueryBound (keyCount K₀ t₀) := by
  unfold preTQ
  cases h : headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => trivial
  | some a =>
    have e : keyCount a.1 a.2.1 = keyCount K₀ t₀ := by
      have e1 : keyCount a.1.wipe t₀ = keyCount K₀.wipe t₀ := by
        rw [hw _ _ (headAt_ks ksAt h)]
      exact e1
    show (pinOn _ _ _).QueryBound _
    rw [← e]
    exact queryBound_pinOn _ _ _ _ (typedKR_asks1 _ _ _ _ _)

/-- **Under every family its value is `preT`'s**, at every table that, at this d and at the
parameters that the plain steps return on this file, holds the three digests at the three strings.
-/
theorem preTQ_det [DecidablePred IsCall169] (tab : D → KeyChains → List Bool → Dig 256)
    (g : Fam (rom 256)) (d : D) (keyFile : ByteArray)
    (ht : ∀ a, headAt ksAt (digToBytes (cfgOf d)) keyFile = some a →
      ∀ s ∈ setK a.1, tab d a.1 s = tab3 (key3 d) a.1 s) :
    (preTQ key3 cfgOf ksAt asm d keyFile).det g =
      (preT IsCall169 tab cfgOf ksAt asm d keyFile).det g := by
  unfold preTQ preT
  cases h : headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => rfl
  | some a =>
    show (pinOn _ _ _).det g = (pinP _ _ _).det g
    rw [det_pinOn, det_pinP]
    refine det_congr_asks _ _ _ (fun s hs => ?_) _
      (keyOnly169 (asm a.1 keyFile a.2.1) a.1 a.2.1 keyFile a.2.2)
    by_cases h9 : IsCall169 s
    · have hm : s ∈ setK a.1 := mem_setK.2 (hs h9)
      rw [OnBytes.Slice.over_mem _ g hm]
      unfold overP
      rw [if_pos h9, ht a h s hm]
    · have hn : s ∉ setK a.1 := fun hm => h9 (setK_169 hm)
      rw [OnBytes.Slice.over_not_mem _ g hn]
      unfold overP
      rw [if_neg h9]

/-- **Where the three digests are g's own answers the pin is not seen.** -/
theorem preTQ_unseen (g : Fam (rom 256)) (d : D) (keyFile : ByteArray) {k : KeyChains}
    {t : TableName} {j : Nat} (h : headAt ksAt (digToBytes (cfgOf d)) keyFile = some (k, t, j))
    (hg : ∀ s ∈ setK k, tab3 (key3 d) k s = g () s) :
    (preTQ key3 cfgOf ksAt asm d keyFile).det g = (typedKR (asm k keyFile t) k t keyFile j).det g
        := by
  unfold preTQ
  rw [h]
  show (pinOn _ _ _).det g = _
  rw [det_pinOn]
  refine det_congr_asks (fun _ => True) _ _ (fun s _ => ?_) _
    (OComp.AsksIn.mono (fun _ _ _ => trivial) (keyOnly169 (asm k keyFile t) k t keyFile j))
  by_cases hm : s ∈ setK k
  · rw [OnBytes.Slice.over_mem _ g hm, hg s hm]
  · rw [OnBytes.Slice.over_not_mem _ g hm]

end Part

section Head
variable {D Out : Type} (cfgOf : D → Dig 256) (f : Fmt.Fld) (sh : IndexShape)
  (mk : TableName → List (List E × E) → Out)

/-- The seeds, asked, ask no string of a call with the number 169. -/
theorem seedsKR_off169 (c : ByteArray) (t : TableName) :
    (seedsKR f sh mk c t).AsksIn fun _ (s : List Bool) => ¬ IsCall169 s := by
  unfold seedsKR
  refine OComp.AsksIn.bind ?_ (seedsBy_off169 f _ _ _)
  intro _
  trivial

/-- **The key's reading, with no pin.** -/
def preKQ (d : D) (uK : ByteArray) : OComp (rom 256) (Option Out) :=
  match Key.readTable sh (digToBytes (cfgOf d)) uK with
  | .error _ => .pure none
  | .ok x => seedsKR f sh mk (digToBytes (cfgOf d)) x.1

theorem preKQ_off (d : D) (uK : ByteArray) :
    (preKQ cfgOf f sh mk d uK).AsksIn fun _ (s : List Bool) => ¬ IsCall169 s := by
  unfold preKQ
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => trivial
  | ok x => exact seedsKR_off169 f sh mk _ _

theorem preKQ_noCoin (d : D) (uK : ByteArray) : (preKQ cfgOf f sh mk d uK).NoCoin := by
  unfold preKQ
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => trivial
  | ok x => exact seedsKR_noCoin f sh mk _ _

theorem preKQ_asks (d : D) (uK : ByteArray) :
    (preKQ cfgOf f sh mk d uK).QueryBound (2 * Slice.seedCalls sh.cubeBits sh.answers + 1) := by
  unfold preKQ
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => trivial
  | ok x => exact seedsKR_asks f sh mk _ _

/-- **Under every family its value is `preK`'s**, at every table. -/
theorem preKQ_det [DecidablePred IsCall169] (tab : D → List Bool → Dig 256) (g : Fam (rom 256))
    (d : D) (uK : ByteArray) :
    (preKQ cfgOf f sh mk d uK).det g = (preK IsCall169 tab cfgOf f sh mk d uK).det g := by
  unfold preKQ preK
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => rfl
  | ok x =>
    show _ = (pinP _ _ _).det g
    rw [det_pinP]
    refine det_congr_asks _ _ _ (fun s hs => ?_) _ (seedsKR_off169 f sh mk _ _)
    unfold overP
    rw [if_neg hs]

end Head

end OnBytes.Tie

#print axioms OnBytes.Tie.preTQ_off
#print axioms OnBytes.Tie.preTQ_det
#print axioms OnBytes.Tie.preTQ_unseen
#print axioms OnBytes.Tie.preKQ_off
#print axioms OnBytes.Tie.preKQ_det
