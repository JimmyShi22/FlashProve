-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchPricesLit.lean: written numbers at which the caller `switchOf` of the code switch
meets the conditions on the prices (`SendLocPrices`) at the very list bounds and the very radius at
which Johnson/G/SwitchAtFull.lean and Johnson/G/SwitchAtSmall.lean have its own condition
(`SendLocRide.OK`), at both examples.

OnBytes/Tie/Pv/Switch/SendLocPrices.lean names it as not said that numbers exist which meet both:
the block's condition wants a list bound of at least a member's list and laws at the radius; the
prices want that bound to be at most the planner's list size, and the radius to be at least the
upper radius. Johnson/Top/H/SwitchPrices.lean leaves the prices' conditions as conditions on the
planner's numbers. Here the planner's own functions are evaluated in Lean's kernel at a written
setting and written groups, as OnBytes/Tie/Pv/KeyStages.lean does for the five stages of a key's
own test. Definitions, statements and proofs.
Main names:
  `setLit`: the setting: the library's `keySet`. `setLit_eq`: written out. `setLit_card`: its
    extension field has the size of the library's.
  `oOf cs pg l`, `idxOf`: for a sending l: a sample for each message, with the message's cube
    (`bitsZ`), priced by the one group pg; the enumeration by place.
  `frontFull`, `priceFull`, `swSendsFull`, and the same three with Small: three groups in front of
    a switch; two groups by which samples are priced; the sendings of the 25 and of the 5 switches.
  `frontFull_ok`, `frontSmall_ok`: each group in front is priced under the Johnson rule, its count
    has that source and is not marked bad, and the joint radius passes `upperRadiusTest`.
  `listsFull_ok`, `listsSmall_ok`: `lOf` at every message of these sendings is at most the planner's
    list size at either pricing group.
  `prices_full`, `prices_small`: `SendLocPrices` of `switchOf`, at every group with that joint
    radius and every choice of kept messages, every one of these sendings, either pricing group
    and every one of the three groups in front.
  `both_full`, `both_small`: at the groups of the two files named above: `SendLocRide.OK` and
    `SendLocPrices` of one caller, under the one premise `Hd.Laws`.
Limits: the theorems speak of written numbers. That the setting, the groups, the cubes and the
pairing of sendings with groups are the planner's at the two examples' public files was seen by an
evaluation outside this file (at each switch: the samples' cubes are the messages' `bitsZ`; every
sample is priced by one group, the first of the two, at the last switch the second; the group in
front is one of the three); no test in this file holds it. `Hd.Laws` is shown of no Hd here. That a
switch of the programs' protocol is a value of `switchOf` is not said. `SendLocPrices` bounds shares
with the proof of work not counted. No bound is evaluated here.

-/
import Johnson.Top.H.SwitchPrices
import Johnson.G.SwitchAtFull
import Johnson.G.SwitchAtSmall
import OnBytes.Slice.RatesToy
import OnBytes.Tie.Pv.KeyStages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch

/-- The setting: the library's `keySet` (OnBytes/Tie/Pv/KeyStages.lean), under a short name. -/
abbrev setLit : Setting := Cb.Pv.Tower.keySet

/-- Written out: every field is the record's default, but for the bits of work before a draw of
positions. -/
theorem setLit_eq : setLit = { workQuery := ⟨20, 28, 32⟩ } := rfl

theorem setLit_card : setLit.cardE = Fintype.card GE := by
  rw [card_GE]
  rfl

section
variable (cs : Codes) (pg : GroupSize) (l : List (OracleShape × ℕ))

/-- A sample for each message of a sending: its cube, priced by the group pg. -/
def oOf : List SampleSize := l.map fun y => ⟨bitsZ cs y.1, [pg]⟩

/-- The enumeration by place. -/
def idxOf : Fin l.length ≃ Fin (oOf cs pg l).length :=
  finCongr (List.length_map _).symm

theorem oOf_get (i : Fin l.length) :
    (oOf cs pg l).get (idxOf cs pg l i) = ⟨bitsZ cs (l.get i).1, [pg]⟩ := by
  unfold oOf idxOf
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

theorem oOf_cube (i : Fin l.length) :
    ((oOf cs pg l).get (idxOf cs pg l i)).cubeBits = bitsZ cs (l.get i).1 := by
  rw [oOf_get]

theorem oOf_groups (i : Fin l.length) :
    ((oOf cs pg l).get (idxOf cs pg l i)).groups = [pg] := by
  rw [oOf_get]

end

/-! ### The full example -/

/-- A group of the first proof chain, as the planner sizes it. -/
def grpFull (k slots : ℕ) (overE : Bool) : GroupSize :=
  { main := ⟨23, 4194304, 219, overE⟩, mask := ⟨17, 8192, 219, true⟩, k := k, h := 0,
    slots := slots, rule := .johnson, m := 258 }

/-- The groups in front of a switch. -/
def frontFull : List GroupSize := [grpFull 8 16 false, grpFull 7 4 false, grpFull 8 1 false]

/-- The groups by which a switch's samples are priced. -/
def priceFull : List GroupSize := [grpFull 8 16 false, grpFull 1 1 true]

/-- The sendings of the 25 switches: every third of the frame's, from the fourth on. -/
def swSendsFull : List (List (OracleShape × ℕ)) :=
  (List.range 25).map fun i => frameFullLit.getD (3 * (i + 1)) []

set_option maxRecDepth 1000000 in
/-- They are sendings of the written list. -/
theorem swSendsFull_mem : ∀ l ∈ swSendsFull, (codesFull2, l) ∈ packFullLit := by decide +kernel

/-- The four conditions on the group in front, at the joint radius. -/
theorem frontFull_ok : ∀ g ∈ frontFull, g.rule = .johnson ∧
    (analysisOfM setLit g).mainAt.source = .johnson ∧
    (analysisOfM setLit g).mainAt.count.bad = false ∧
    upperRadiusTest setLit g radFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The library's bound on a member's list is at most the planner's list size. -/
theorem listsFull_ok : ∀ l ∈ swSendsFull, ∀ x ∈ l, ∀ pg ∈ priceFull,
    lOf codesFull2 x.1 x.2 ≤ largestList setLit [pg] := by decide +kernel

/-- The conditions on the prices. -/
theorem prices_full {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
    [DecidablePred kp] (Hd : GHeld Sh kp) (he : G.e = radFull) {B Kc St₀ Wp : Type} [Fintype B]
    (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) {l : List (OracleShape × ℕ)}
    (hl : l ∈ swSendsFull) {pg g : GroupSize} (hp : pg ∈ priceFull) (hg : g ∈ frontFull)
    (cutN : (sigOf codesFull2 l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
    (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw) :
    SendLocPrices (switchOf Hd Sb sl Z A₀ codesFull2 l cutN t w₀ Cw) setLit
      (oOf codesFull2 pg l) g (idxOf codesFull2 pg l) :=
  switchOf_prices Hd Sb sl Z A₀ codesFull2 l cutN t w₀ Cw setLit (oOf codesFull2 pg l) g
    (idxOf codesFull2 pg l) setLit_card rfl (oOf_cube codesFull2 pg l)
    (fun i => by
      rw [oOf_groups]
      exact listsFull_ok l hl (l.get i) (List.get_mem l i) pg hp)
    (frontFull_ok g hg).1 (frontFull_ok g hg).2.1 (frontFull_ok g hg).2.2.1
    (by rw [he]; exact (frontFull_ok g hg).2.2.2)

/-- One caller meets both, under the kept messages' laws. -/
theorem both_full (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit)
    (mem : Fin lo.length → Prop) [DecidablePred mem]
    {Sh : GShape (grpOf codesFull2 lo mem logFull radFull)}
    {kp : (sigOf codesFull2 lo).O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (hL : Hd.Laws)
    {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) (grpOf codesFull2 lo mem logFull radFull).C.J)
    (Z : Evader GE ((grpOf codesFull2 lo mem logFull radFull).Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub kp).Msg × Wp))
    {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsFull) {pg g : GroupSize}
    (hp : pg ∈ priceFull) (hg : g ∈ frontFull)
    (cutN : (sigOf codesFull2 l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
    (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf Hd Sb sl Z A₀ codesFull2 l cutN t w₀ Cw) ∧
      SendLocPrices (switchOf Hd Sb sl Z A₀ codesFull2 l cutN t w₀ Cw) setLit
        (oOf codesFull2 pg l) g (idxOf codesFull2 pg l) :=
  ⟨switch_ok_full lo hlo mem Hd hL Sb sl Z A₀ (swSendsFull_mem l hl) cutN t w₀ Cw,
    prices_full Hd rfl Sb sl Z A₀ hl hp hg cutN t w₀ Cw⟩

/-! ### The small example -/

/-- A group of the first proof chain, as the planner sizes it. -/
def grpSmall (k slots : ℕ) (overE : Bool) : GroupSize :=
  { main := ⟨18, 131072, 218, overE⟩, mask := ⟨17, 8192, 218, true⟩, k := k, h := 0,
    slots := slots, rule := .johnson, m := 517 }

/-- The groups in front of a switch. -/
def frontSmall : List GroupSize := [grpSmall 9 8 false, grpSmall 7 2 false, grpSmall 8 1 false]

/-- The groups by which a switch's samples are priced. -/
def priceSmall : List GroupSize := [grpSmall 9 8 false, grpSmall 1 1 true]

/-- The sendings of the 5 switches: every third of the frame's, from the fourth on. -/
def swSendsSmall : List (List (OracleShape × ℕ)) :=
  (List.range 5).map fun i => frameSmallLit.getD (3 * (i + 1)) []

set_option maxRecDepth 1000000 in
/-- They are sendings of the written list. -/
theorem swSendsSmall_mem : ∀ l ∈ swSendsSmall, (codesSmall2, l) ∈ packSmallLit := by decide +kernel

/-- The four conditions on the group in front, at the joint radius. -/
theorem frontSmall_ok : ∀ g ∈ frontSmall, g.rule = .johnson ∧
    (analysisOfM setLit g).mainAt.source = .johnson ∧
    (analysisOfM setLit g).mainAt.count.bad = false ∧
    upperRadiusTest setLit g radSmall = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The library's bound on a member's list is at most the planner's list size. -/
theorem listsSmall_ok : ∀ l ∈ swSendsSmall, ∀ x ∈ l, ∀ pg ∈ priceSmall,
    lOf codesSmall2 x.1 x.2 ≤ largestList setLit [pg] := by decide +kernel

/-- The conditions on the prices. -/
theorem prices_small {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
    [DecidablePred kp] (Hd : GHeld Sh kp) (he : G.e = radSmall) {B Kc St₀ Wp : Type} [Fintype B]
    (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) {l : List (OracleShape × ℕ)}
    (hl : l ∈ swSendsSmall) {pg g : GroupSize} (hp : pg ∈ priceSmall) (hg : g ∈ frontSmall)
    (cutN : (sigOf codesSmall2 l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
    (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw) :
    SendLocPrices (switchOf Hd Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw) setLit
      (oOf codesSmall2 pg l) g (idxOf codesSmall2 pg l) :=
  switchOf_prices Hd Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw setLit (oOf codesSmall2 pg l) g
    (idxOf codesSmall2 pg l) setLit_card rfl (oOf_cube codesSmall2 pg l)
    (fun i => by
      rw [oOf_groups]
      exact listsSmall_ok l hl (l.get i) (List.get_mem l i) pg hp)
    (frontSmall_ok g hg).1 (frontSmall_ok g hg).2.1 (frontSmall_ok g hg).2.2.1
    (by rw [he]; exact (frontSmall_ok g hg).2.2.2)

/-- One caller meets both, under the kept messages' laws. -/
theorem both_small (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit)
    (mem : Fin lo.length → Prop) [DecidablePred mem]
    {Sh : GShape (grpOf codesSmall2 lo mem logSmall radSmall)}
    {kp : (sigOf codesSmall2 lo).O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (hL : Hd.Laws)
    {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) (grpOf codesSmall2 lo mem logSmall radSmall).C.J)
    (Z : Evader GE ((grpOf codesSmall2 lo mem logSmall radSmall).Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub kp).Msg × Wp))
    {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsSmall) {pg g : GroupSize}
    (hp : pg ∈ priceSmall) (hg : g ∈ frontSmall)
    (cutN : (sigOf codesSmall2 l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
    (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf Hd Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw) ∧
      SendLocPrices (switchOf Hd Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw) setLit
        (oOf codesSmall2 pg l) g (idxOf codesSmall2 pg l) :=
  ⟨switch_ok_small lo hlo mem Hd hL Sb sl Z A₀ (swSendsSmall_mem l hl) cutN t w₀ Cw,
    prices_small Hd rfl Sb sl Z A₀ hl hp hg cutN t w₀ Cw⟩

end Johnson.G

#print axioms Johnson.G.setLit_eq
#print axioms Johnson.G.frontFull_ok
#print axioms Johnson.G.listsFull_ok
#print axioms Johnson.G.frontSmall_ok
#print axioms Johnson.G.listsSmall_ok
#print axioms Johnson.G.prices_full
#print axioms Johnson.G.prices_small
#print axioms Johnson.G.both_full
#print axioms Johnson.G.both_small
