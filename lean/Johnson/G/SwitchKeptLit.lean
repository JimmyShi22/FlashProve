-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchKeptLit.lean: at the written numbers of both examples, one caller of the code
switch, behind the fold of a group with kept members, meets its own condition (`SendLocRide.OK`) and
the conditions on the prices (`SendLocPrices`): no premise on laws is left.

Johnson/G/SwitchPricesLit.lean has both under the one premise `GHeld.Laws`.
Johnson/Top/H/SwitchKept.lean has a choice of kept messages over the programs' shapes at which that
premise is a theorem (`heldPort_laws`). Here the two are laid together. Definitions, statements and
proofs.
Main names:
  `kept_both_full`, `kept_both_small`: for each written list lo of a link's sampled messages; every
    set mem of members and every stage s with as many positions as the written common length,
    under whose two codes the members' tables stand; every set kp of kept members, each with a main
    row and no mask row; all corners, rows, coefficients, carried joints; each written sending l of
    a switch, either pricing group and each of the three groups in front: `SendLocRide.OK` and
    `SendLocPrices` of `switchOf` at `heldPort`.
  `memMain lo`: the messages of a list that have a main row. `tablesFull_ok`, `tablesSmall_ok`: at
    the stage of the sizes of each of the three groups in front (`stageOf`), these stand under
    the stage's two codes. `keepableFull`, `keepableSmall`: each list has one without a mask row.
  `rowsAtFull`, `heldAtFull`, `rowsAtSmall`, `heldAtSmall`: the group's data and the choice of kept
    messages at these members and stages.
  `kept_both_full_at`, `kept_both_small_at`: the same there: the one premise on data that is left:
    a kept member has no mask row.
Limits: those of Johnson/G/SwitchPricesLit.lean and Johnson/Top/H/SwitchKept.lean. That the members
of a link's group in the programs are the messages with a main row, and which of them the programs
keep, is not said. Which list stands in front of which sending is not said. The rows and their
forms, the coefficients, the carried joint, the reading `cutN`, the witness w₀ and the rider's code
are letters; no value of them is written here, so that each can be laid is not shown here. That a
switch of the programs' protocol is a value of this caller is not said. The fold's own conditions
are not treated. No bound is evaluated.

-/
import Johnson.Top.H.SwitchKept
import Johnson.G.SwitchPricesLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch

/-- The messages of a list that have a main row. -/
def memMain (lo : List (OracleShape × ℕ)) (i : Fin lo.length) : Prop := (lo.get i).1.mainRows ≠ 0

instance decMemMain (lo : List (OracleShape × ℕ)) : DecidablePred (memMain lo) := fun i =>
  inferInstanceAs (Decidable ((lo.get i).1.mainRows ≠ 0))

/-! ### The full example -/

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (mem : Fin lo.length → Prop)
  [DecidablePred mem] (s : Sg) (hs : s.C.a = logFull) (oM oZ : Fin lo.length → ℕ)
  (hM : ∀ i, mem i → (lo.get i).1.mainRows ≠ 0 → cMain codesFull2 (lo.get i).1 = s.C)
  (hZ : ∀ i, mem i → (lo.get i).1.maskRows ≠ 0 → cMask codesFull2 (lo.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (lo.get a.1).1.mainRows ≠ 0)
  (h0 : ∀ a, kp a → (lo.get a.1).1.maskRows = 0)
  (kq : Fin lo.length → Prop) [DecidablePred kq]

local notation "HdA" => heldPort codesFull2 lo mem s radFull oM oZ hM hZ kp h1 h0 kq

variable {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort codesFull2 lo mem s radFull oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort codesFull2 lo mem s radFull oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub kq).Msg × Wp))

include hlo hs in
/-- One caller, with kept members, meets both; no premise on laws is left. -/
theorem kept_both_full {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsFull) {pg g : GroupSize}
    (hp : pg ∈ priceFull) (hg : g ∈ frontFull)
    (cutN : (sigOf codesFull2 l).Msg → ((HdA).foldD Sb sl Z A₀).Cf.N.Wit)
    (t : ℕ) (w₀ : ((HdA).foldD Sb sl Z A₀).tgt.W)
    {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf HdA Sb sl Z A₀ codesFull2 l cutN t w₀ Cw) ∧
      SendLocPrices (switchOf HdA Sb sl Z A₀ codesFull2 l cutN t w₀ Cw)
        setLit (oOf codesFull2 pg l) g (idxOf codesFull2 pg l) :=
  ⟨switchKept_ok codesFull2 lo mem s radFull oM oZ hM hZ kp h1 h0 kq Sb sl Z A₀ codesFull2 l cutN
      t w₀ Cw
      (List.all_eq_true.1 packFullLit_meets _ (swSendsFull_mem l hl))
      (fun i _ => by
        rw [hs]
        exact (links_fit lo hlo (lo.get i) (List.get_mem lo i)).le)
      (fun i _ => by
        rw [hs]
        exact (links_fit lo hlo (lo.get i) (List.get_mem lo i)).near),
    prices_full HdA rfl Sb sl Z A₀ hl hp hg cutN t w₀ Cw⟩

end

set_option maxRecDepth 1000000 in
/-- At each of the three groups in front: the stage of its sizes has the common length, and every
message of the written lists that has a main row stands under that stage's two codes. -/
theorem tablesFull_ok : ∀ g ∈ frontFull, (stageOf g 0).C.a = logFull ∧
    ∀ lo ∈ linksFullLit, ∀ x ∈ lo, x.1.mainRows ≠ 0 →
      cMain codesFull2 x.1 = (stageOf g 0).C ∧
        (x.1.maskRows ≠ 0 → cMask codesFull2 x.1 = (stageOf g 0).Z) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each written list has a message with a main row and no mask row. -/
theorem keepableFull : ∀ lo ∈ linksFullLit, ∃ x ∈ lo, x.1.mainRows ≠ 0 ∧ x.1.maskRows = 0 := by
  decide +kernel

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (t₀ : ℕ) (oM oZ : Fin lo.length → ℕ)

include hlo hgs in
theorem hMFull : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
    cMain codesFull2 (lo.get i).1 = (stageOf gs t₀).C :=
  fun i k _ => ((tablesFull_ok gs hgs).2 lo hlo (lo.get i) (List.get_mem lo i) k).1

include hlo hgs in
theorem hZFull : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
    cMask codesFull2 (lo.get i).1 = (stageOf gs t₀).Z :=
  fun i k => ((tablesFull_ok gs hgs).2 lo hlo (lo.get i) (List.get_mem lo i) k).2

/-- The group's data: the messages with a main row, at the stage of a group in front. -/
noncomputable abbrev rowsAtFull : Rows (sigOf codesFull2 lo) :=
  rowsPort codesFull2 lo (memMain lo) (stageOf gs t₀) radFull oM oZ (hMFull lo hlo gs hgs t₀)
    (hZFull lo hlo gs hgs t₀)

variable (kp : {i // memMain lo i} → Prop) [DecidablePred kp]
  (h0 : ∀ a, kp a → (lo.get a.1).1.maskRows = 0) (kq : Fin lo.length → Prop)

/-- The choice of kept messages there. -/
noncomputable abbrev heldAtFull : GHeld ((rowsAtFull lo hlo gs hgs t₀ oM oZ).keep kp).Sh kq :=
  heldPort codesFull2 lo (memMain lo) (stageOf gs t₀) radFull oM oZ (hMFull lo hlo gs hgs t₀)
    (hZFull lo hlo gs hgs t₀) kp (fun a _ => a.2) h0 kq

local notation "HdB" => heldAtFull lo hlo gs hgs t₀ oM oZ kp h0 kq

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAtFull lo hlo gs hgs t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAtFull lo hlo gs hgs t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub kq).Msg × Wp))

/-- No premise on data is left but that a kept member has no mask row. -/
theorem kept_both_full_at {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsFull)
    {pg g : GroupSize} (hp : pg ∈ priceFull) (hg : g ∈ frontFull)
    (cutN : (sigOf codesFull2 l).Msg → ((HdB).foldD Sb sl Z A₀).Cf.N.Wit)
    (t : ℕ) (w₀ : ((HdB).foldD Sb sl Z A₀).tgt.W)
    {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf HdB Sb sl Z A₀ codesFull2 l cutN t w₀ Cw) ∧
      SendLocPrices (switchOf HdB Sb sl Z A₀ codesFull2 l cutN t w₀ Cw)
        setLit (oOf codesFull2 pg l) g (idxOf codesFull2 pg l) :=
  kept_both_full lo hlo (memMain lo) (stageOf gs t₀) (tablesFull_ok gs hgs).1 oM oZ
    (hMFull lo hlo gs hgs t₀) (hZFull lo hlo gs hgs t₀) kp (fun a _ => a.2) h0 kq Sb sl Z A₀ hl
    hp hg cutN t w₀ Cw

end

/-! ### The small example -/

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (mem : Fin lo.length → Prop)
  [DecidablePred mem] (s : Sg) (hs : s.C.a = logSmall) (oM oZ : Fin lo.length → ℕ)
  (hM : ∀ i, mem i → (lo.get i).1.mainRows ≠ 0 → cMain codesSmall2 (lo.get i).1 = s.C)
  (hZ : ∀ i, mem i → (lo.get i).1.maskRows ≠ 0 → cMask codesSmall2 (lo.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (lo.get a.1).1.mainRows ≠ 0)
  (h0 : ∀ a, kp a → (lo.get a.1).1.maskRows = 0)
  (kq : Fin lo.length → Prop) [DecidablePred kq]

local notation "HdC" => heldPort codesSmall2 lo mem s radSmall oM oZ hM hZ kp h1 h0 kq

variable {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort codesSmall2 lo mem s radSmall oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort codesSmall2 lo mem s radSmall oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub kq).Msg × Wp))

include hlo hs in
/-- One caller, with kept members, meets both; no premise on laws is left. -/
theorem kept_both_small {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsSmall) {pg g : GroupSize}
    (hp : pg ∈ priceSmall) (hg : g ∈ frontSmall)
    (cutN : (sigOf codesSmall2 l).Msg → ((HdC).foldD Sb sl Z A₀).Cf.N.Wit)
    (t : ℕ) (w₀ : ((HdC).foldD Sb sl Z A₀).tgt.W)
    {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf HdC Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw) ∧
      SendLocPrices (switchOf HdC Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw)
        setLit (oOf codesSmall2 pg l) g (idxOf codesSmall2 pg l) :=
  ⟨switchKept_ok codesSmall2 lo mem s radSmall oM oZ hM hZ kp h1 h0 kq Sb sl Z A₀ codesSmall2 l cutN
      t w₀ Cw
      (List.all_eq_true.1 packSmallLit_meets _ (swSendsSmall_mem l hl))
      (fun i _ => by
        rw [hs]
        exact (links_fit_small lo hlo (lo.get i) (List.get_mem lo i)).le)
      (fun i _ => by
        rw [hs]
        exact (links_fit_small lo hlo (lo.get i) (List.get_mem lo i)).near),
    prices_small HdC rfl Sb sl Z A₀ hl hp hg cutN t w₀ Cw⟩

end

set_option maxRecDepth 1000000 in
/-- At each of the three groups in front: the stage of its sizes has the common length, and every
message of the written lists that has a main row stands under that stage's two codes. -/
theorem tablesSmall_ok : ∀ g ∈ frontSmall, (stageOf g 0).C.a = logSmall ∧
    ∀ lo ∈ linksSmallLit, ∀ x ∈ lo, x.1.mainRows ≠ 0 →
      cMain codesSmall2 x.1 = (stageOf g 0).C ∧
        (x.1.maskRows ≠ 0 → cMask codesSmall2 x.1 = (stageOf g 0).Z) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each written list has a message with a main row and no mask row. -/
theorem keepableSmall : ∀ lo ∈ linksSmallLit, ∃ x ∈ lo, x.1.mainRows ≠ 0 ∧ x.1.maskRows = 0 := by
  decide +kernel

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (t₀ : ℕ) (oM oZ : Fin lo.length → ℕ)

include hlo hgs in
theorem hMSmall : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
    cMain codesSmall2 (lo.get i).1 = (stageOf gs t₀).C :=
  fun i k _ => ((tablesSmall_ok gs hgs).2 lo hlo (lo.get i) (List.get_mem lo i) k).1

include hlo hgs in
theorem hZSmall : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
    cMask codesSmall2 (lo.get i).1 = (stageOf gs t₀).Z :=
  fun i k => ((tablesSmall_ok gs hgs).2 lo hlo (lo.get i) (List.get_mem lo i) k).2

/-- The group's data: the messages with a main row, at the stage of a group in front. -/
noncomputable abbrev rowsAtSmall : Rows (sigOf codesSmall2 lo) :=
  rowsPort codesSmall2 lo (memMain lo) (stageOf gs t₀) radSmall oM oZ (hMSmall lo hlo gs hgs t₀)
    (hZSmall lo hlo gs hgs t₀)

variable (kp : {i // memMain lo i} → Prop) [DecidablePred kp]
  (h0 : ∀ a, kp a → (lo.get a.1).1.maskRows = 0) (kq : Fin lo.length → Prop)

/-- The choice of kept messages there. -/
noncomputable abbrev heldAtSmall : GHeld ((rowsAtSmall lo hlo gs hgs t₀ oM oZ).keep kp).Sh kq :=
  heldPort codesSmall2 lo (memMain lo) (stageOf gs t₀) radSmall oM oZ (hMSmall lo hlo gs hgs t₀)
    (hZSmall lo hlo gs hgs t₀) kp (fun a _ => a.2) h0 kq

local notation "HdD" => heldAtSmall lo hlo gs hgs t₀ oM oZ kp h0 kq

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAtSmall lo hlo gs hgs t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAtSmall lo hlo gs hgs t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub kq).Msg × Wp))

/-- No premise on data is left but that a kept member has no mask row. -/
theorem kept_both_small_at {l : List (OracleShape × ℕ)} (hl : l ∈ swSendsSmall)
    {pg g : GroupSize} (hp : pg ∈ priceSmall) (hg : g ∈ frontSmall)
    (cutN : (sigOf codesSmall2 l).Msg → ((HdD).foldD Sb sl Z A₀).Cf.N.Wit)
    (t : ℕ) (w₀ : ((HdD).foldD Sb sl Z A₀).tgt.W)
    {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf HdD Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw) ∧
      SendLocPrices (switchOf HdD Sb sl Z A₀ codesSmall2 l cutN t w₀ Cw)
        setLit (oOf codesSmall2 pg l) g (idxOf codesSmall2 pg l) :=
  kept_both_small lo hlo (memMain lo) (stageOf gs t₀) (tablesSmall_ok gs hgs).1 oM oZ
    (hMSmall lo hlo gs hgs t₀) (hZSmall lo hlo gs hgs t₀) kp (fun a _ => a.2) h0 kq Sb sl Z A₀ hl
    hp hg cutN t w₀ Cw

end

end Johnson.G

#print axioms Johnson.G.kept_both_full
#print axioms Johnson.G.kept_both_small
#print axioms Johnson.G.tablesFull_ok
#print axioms Johnson.G.keepableFull
#print axioms Johnson.G.tablesSmall_ok
#print axioms Johnson.G.keepableSmall
#print axioms Johnson.G.kept_both_full_at
#print axioms Johnson.G.kept_both_small_at
