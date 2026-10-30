-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ServedLaws.lean: a whole call of verify-on-bytes that passes, without the options -policy
and -no-proof-of-work, passes `servedAt` at the files as read. For proofs only; the program does
not import this file.

  `common_fields`: the common beginning of the stages holds what the planner made of the public
    files.
  `keyFound_of`, `leafFound_of`, `requestFound_of`: what a stage returns is what the like function
    of OnBytes/K/Served.lean returns, which looks at no file but the public ones, the request and
    the reply.
  `keyStage_eq`, `leafStage_eq`: where the file's check says yes, the stage key, or leaf, is equal
    to the like function, also where that refuses.
  `keyStage_closed`, `leafStage_closed`: the stage for all inputs: the accounting, then the file's
    check, then the like function.
  `readCall_cp`: what a whole call knows of the ID and of its options, field by field.
  `wholeCall_tail`: a whole call that passes ends as `tailAt` says, at the planner's value, the
    user's statement as read, the ID in lower-case digits and the printed digest.
  `wholeCall_yes`: without the option -policy a whole call that passes ends in a yes, not within
    limits.
  `wholeCall_served`: so, with the served options, `servedAt` is true at the three public files as
    read.
What is not claimed: see the head of OnBytes/K/Served.lean. Nothing on soundness.

-/
import OnBytes.K.Served
import OnBytes.K.ExitStages
import OnBytes.Model.VerifyLawsId
import OnBytes.Model.VerifyLawsOption

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages
open OnBytes.Params (exc_bind exc_guard exc_either)

theorem named_of {α : Type} {x : Except String α} {a : α} (h : x = .ok a) : named x = .ok a := by
  rw [h]
  rfl

/-- The common beginning of the stages holds what the planner made of the public files. -/
theorem common_fields {r : Read} {C : Common} {p : Planned} (h : commonOfCall r = .ok C)
    (hp : planned r.pol r.KL r.layout = .ok p) :
    C.X = p.X ∧ C.chains = p.chains ∧ C.built = p.built := by
  unfold commonOfCall at h
  rw [hp] at h
  have h1 : commonOf p.X p.cfg p.chains p.built r.key r.id.asked = .ok C := h
  unfold commonOf at h1
  dsimp only at h1
  split at h1
  · obtain ⟨first, h2, h1⟩ := exc_bind h1
    cases h2
    obtain ⟨_, _, h1⟩ := exc_bind h1
    cases h1
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨_, h2, _⟩ := exc_bind h1
    cases h2

/-- Where `Key.check` says yes, the stage key is `keyFound`, refusals among it. -/
theorem keyStage_eq {C : Common} {n : Nat} {key : ByteArray} {t : Params.TableName}
    (h : Key.check C.chains.key key = .ok t) : keyStage C n key = keyFound C n := by
  unfold keyStage keyFound
  rw [h]

/-- Where `Entry.check` says yes, the stage leaf is `leafFound`, refusals among it. -/
theorem leafStage_eq {C : Common} {n : Nat} {e : ByteArray} {t : Params.TableName}
    (h : Entry.check C.chains.made.entryLink C.first e = .ok t) :
    leafStage C n e = leafFound C n := by
  unfold leafStage leafFound
  rw [h]

/-- The stage key, for all inputs: the accounting, then `Key.check`, then `keyFound`. -/
theorem keyStage_closed (C : Common) (n : Nat) (key : ByteArray) :
    keyStage C n key = (do
      let _ ← named (C.acct C.chains.made.key n "key")
      match Key.check C.chains.key key with
      | .error e => checkerRefused e "key-refused" "internal-key-parameters"
      | .ok _ => keyFound C n) := by
  unfold keyStage keyFound
  cases h1 : named (C.acct C.chains.made.key n "key") <;>
    cases h2 : Key.check C.chains.key key <;> simp [bind, Except.bind]

/-- The stage leaf, for all inputs: the accounting, then `Entry.check`, then `leafFound`. -/
theorem leafStage_closed (C : Common) (n : Nat) (e : ByteArray) :
    leafStage C n e = (do
      let _ ← named (C.acct [C.chains.made.entry] n "leaf")
      match Entry.check C.chains.made.entryLink C.first e with
      | .error r => checkerRefused r "entry-refused" "internal-entry-parameters"
      | .ok _ => leafFound C n) := by
  unfold leafStage leafFound
  cases h1 : named (C.acct [C.chains.made.entry] n "leaf") <;>
    cases h2 : Entry.check C.chains.made.entryLink C.first e <;> simp [bind, Except.bind]

theorem keyFound_of {C : Common} {n : Nat} {key : ByteArray} {y : Found}
    (h : keyStage C n key = .ok y) : keyFound C n = .ok y := by
  obtain ⟨ac, _, h1, _, h3, rfl⟩ := (keyStage_iff C n key y).1 h
  unfold keyFound
  simp only [named_of h1, named_of h3, bind, Except.bind, pure, Except.pure]

theorem leafFound_of {C : Common} {n : Nat} {e : ByteArray} {y : Found}
    (h : leafStage C n e = .ok y) : leafFound C n = .ok y := by
  obtain ⟨ac, _, h1, _, h3, rfl⟩ := (leafStage_iff C n e y).1 h
  unfold leafFound
  simp only [named_of h1, named_of h3, bind, Except.bind, pure, Except.pure]

theorem requestFound_of {C : Common} {o : Options} {r : Read} {entry : ByteArray} {y : Found}
    (h : requestStage C o r entry = .ok y) :
    requestFound C o r.pol r.KL r.request r.y r.layout.isSome = .ok y := by
  unfold requestStage at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  have hx := named_ok hx
  split at h
  · cases h
  · obtain ⟨_, hw, h⟩ := exc_bind h
    have hw := named_ok hw
    have h0 := Except.ok.inj h
    unfold requestRun at hx
    obtain ⟨_, g0, hx⟩ := exc_bind hx
    obtain ⟨so, g1, hx⟩ := exc_bind hx
    obtain ⟨cov, g2, hx⟩ := exc_bind hx
    obtain ⟨further, _, hx⟩ := exc_bind hx
    obtain ⟨a, g4, hx⟩ := exc_bind hx
    cases hi : Proof.requestItem r.pol r.KL r.request with
    | none =>
      rw [hi] at hx
      cases hx
    | some item =>
      rw [hi] at hx
      obtain ⟨_, hp, hx⟩ := exc_bind hx
      cases hp
      obtain ⟨_, g5, hx⟩ := exc_bind hx
      obtain ⟨links, g6, hx⟩ := exc_bind hx
      cases hx
      unfold requestFound
      rw [hi]
      have gi : named (Except.ok item : Except String ByteArray) = .ok item := rfl
      simp only [named_of g0, named_of g1, named_of g2, named_of g4, gi, named_of g5, named_of g6,
        named_of hw, bind, Except.bind, pure, Except.pure]
      exact congrArg Except.ok h0

/-- What the first tests of a call return on the ID and the options, field by field. -/
theorem readFirst_cp {o : Options} {f : Verify.Files} {r : Read} (h : readFirst o f true = .ok r) :
    ∃ hp, hPar r.pol r.KL r.layout = .ok hp ∧ r.id = cpAt o r.id.asked (hex64 hp) := by
  have hc : ∀ {x : Except String ByteArray} {a : ByteArray}, callNamed x = .ok a → x = .ok a := by
    intro x a hx
    cases x with
    | error e => cases hx
    | ok b =>
      cases hx
      rfl
  unfold readFirst at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (obtain ⟨_, ha, _⟩ := exc_bind h
       cases ha
       done)
    | (obtain ⟨asked, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨⟨pol, kl, lay⟩, _, h⟩ := exc_bind h
       dsimp only at h
       obtain ⟨key, _, h⟩ := exc_bind h
       obtain ⟨hp, hh, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       obtain ⟨_, _, h⟩ := exc_bind h
       cases h
       exact ⟨hp, hc hh, rfl⟩)

/-- The first tests of a whole call keep it. -/
theorem readCall_cp {o : Options} {f : Verify.Files} {r : Read} (h : readCall o f = .ok r) :
    ∃ hp, hPar r.pol r.KL r.layout = .ok hp ∧ r.id = cpAt o r.id.asked (hex64 hp) := by
  unfold readCall at h
  replace h := exc_guard h
  obtain ⟨r0, h0, h⟩ := exc_bind h
  have h1 := readFirst_cp h0
  extract_lets next at h
  have hj : next () = .ok r := by
    split at h
    · obtain ⟨_, h⟩ := exc_either h
      exact h
    · obtain ⟨_, _, h⟩ := exc_bind h
      exact h
  obtain ⟨_, _, hj⟩ := exc_bind hj
  obtain ⟨request, _, hj⟩ := exc_bind hj
  obtain ⟨y, _, hj⟩ := exc_bind hj
  obtain ⟨_, hj⟩ := exc_either hj
  obtain ⟨proof, _, hj⟩ := exc_bind hj
  obtain ⟨k, _, hj⟩ := exc_bind hj
  cases hj
  exact h1

/-- The user's statement at the files that a whole call's first tests return. -/
def stmAt (r : Read) (lay : ByteArray) (o : Options) : UserStm :=
  ⟨r.pol, lay, r.KL, r.request, r.y, o⟩

/-- A whole call that passes ends as `tailAt` says. -/
theorem wholeCall_tail {o : Options} {f : Verify.Files} {entry : FileIn} {r : Read}
    {ent lay : ByteArray} {C : Common} {p : Planned}
    (h : (wholeCall o { f with entry := entry }).passing = true)
    (hr : readCall o f = .ok r) (he : entry = some ent) (hC : commonOfCall r = .ok C)
    (hl : r.layout = some lay) (hp : planned r.pol r.KL (some lay) = .ok p) :
    ∃ hpar, hPar r.pol r.KL (some lay) = .ok hpar ∧
      wholeCall o { f with entry := entry } = tailAt p (stmAt r lay o) r.id.asked (hex64 hpar) := by
  obtain ⟨⟨a1, w1, e1⟩, ⟨a2, w2, e2⟩, ⟨a3, w3, e3⟩, _⟩ := wholeCall_stages h hr he hC
  obtain ⟨hpar, c1, c2⟩ := readCall_cp hr
  rw [hl] at c1
  obtain ⟨f1, f2, f3⟩ := common_fields hC (by rw [hl]; exact hp)
  obtain ⟨i1, _, _, _⟩ := readCall_id hr
  subst he
  have hw : wholeCall o { f with entry := some ent } =
      cpStagesRun [C.oneTimeOut .key (keyStage C o.bits r.key),
        C.oneTimeOut .leaf (leafStage C o.bits ent),
        stageOut .request C.idHex (requestStage C o r ent)] none (askedBelowBar o.bits) o.bits r.id
        (some (words32 r.request, C.policyLines)) := by
    unfold wholeCall
    rw [readCall_entry, hr]
    simp only [stagesOf, hC]
  rw [hw] at h
  obtain ⟨j1, j2⟩ := cpStagesRun_id h
  have hasked : r.id.asked = C.idHex := by
    rw [j2 (j1 i1)]
    exact stageOut_idHex .key C.idHex (keyStage C o.bits r.key)
  refine ⟨hpar, c1, ?_⟩
  rw [hw, e1, e2, e3, ← keyFound_of e1, ← leafFound_of e2, ← requestFound_of e3, hl]
  obtain ⟨X, ch, b, t, i⟩ := C
  cases f1
  cases f2
  cases f3
  cases hasked
  rw [c2]
  rfl

/-- The end of a whole call never says that a part has passed. -/
theorem cpStagesRun_whole {stages : List StageOut} {belowBar : Bool} {asked : Nat} {id : CpId}
    {about : Option (Array UInt32 × PolicyLines)} {s : StageName} {c : Closing} :
    cpStagesRun stages none belowBar asked id about ≠ .partPassed s c := by
  intro h
  unfold cpStagesRun at h
  dsimp only at h
  split at h
  · split at h <;> cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i who hwho
  have hw : ∃ a, who = .inr a := by
    cases about with
    | none => cases hwho
    | some a =>
      have hwho' : (cpCovered a.1 a.2).map Sum.inr = .ok who := hwho
      cases hc : cpCovered a.1 a.2 with
      | error e =>
        rw [hc] at hwho'
        cases hwho'
      | ok w =>
        rw [hc] at hwho'
        cases hwho'
        exact ⟨w, rfl⟩
  obtain ⟨a, rfl⟩ := hw
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hq; cases hq)

/-- Without the option -policy a whole call that passes ends in a yes. -/
theorem wholeCall_yes {o : Options} {f : Verify.Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k) (h : (wholeCall o { f with entry := entry }).passing = true)
    (ho : o.policy = none) : isYes (wholeCall o { f with entry := entry }) = true := by
  cases hw : wholeCall o { f with entry := entry } with
  | yes a c => rfl
  | withinLimits a c =>
    have := wholeCall_within hk hw
    rw [ho] at this
    cases this
  | partPassed s c =>
    exfalso
    obtain ⟨r, ent, _, _, _, _, g1, _, g3, _⟩ := wholeCall_passed hk h
    subst g3
    unfold wholeCall at hw
    rw [readCall_entry, g1] at hw
    dsimp only at hw
    exact cpStagesRun_whole hw
  | notVer a b c => rw [hw] at h; cases h
  | refusedBy a b c => rw [hw] at h; cases h
  | wrongId => rw [hw] at h; cases h
  | policy a => rw [hw] at h; cases h
  | no a => rw [hw] at h; cases h
  | notChecked a => rw [hw] at h; cases h
  | unreadable a => rw [hw] at h; cases h
  | usage a => rw [hw] at h; cases h

/-- A whole call that passes, with the served options, is served at the three public files as
read. -/
theorem wholeCall_served {o : Options} {f : Verify.Files} {k : Nat} {entry : FileIn} {r : Read}
    {ent lay : ByteArray} {C : Common} {p : Planned} (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true)
    (hr : readCall o f = .ok r) (he : entry = some ent) (hC : commonOfCall r = .ok C)
    (hl : r.layout = some lay) (hp : planned r.pol r.KL (some lay) = .ok p)
    (ho : optionsServed o = true) :
    servedAt ⟨r.pol, lay, r.KL⟩ (stmAt r lay o) = true := by
  obtain ⟨hpar, c1, c2⟩ := wholeCall_tail h hr he hC hl hp
  have ho' := ho
  unfold optionsServed at ho'
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at ho'
  have hy := wholeCall_yes hk h ho'.2
  rw [c2] at hy
  obtain ⟨_, _, i3, _⟩ := readCall_id hr
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 ho'.1.1.1
  have hid : o.id.bind idAsked = some r.id.asked := by
    rw [ht]
    exact i3 t ht
  unfold servedAt
  simp only [stmAt, decide_true, Bool.true_and, ho, hid, c1, hp]
  exact hy

end OnBytes.K

#print axioms OnBytes.K.common_fields
#print axioms OnBytes.K.keyStage_closed
#print axioms OnBytes.K.leafStage_closed
#print axioms OnBytes.K.keyStage_eq
#print axioms OnBytes.K.leafStage_eq
#print axioms OnBytes.K.cpStagesRun_whole
#print axioms OnBytes.K.wholeCall_tail
#print axioms OnBytes.K.wholeCall_yes
#print axioms OnBytes.K.wholeCall_served
