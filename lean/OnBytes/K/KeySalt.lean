-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/KeySalt.lean: the number of bytes of a salt in the plan of a key file's one-time chain, as
the Lean program `verify-on-bytes` (OnBytes/Main.lean) reads that plan back from its own parameter
bytes, is the word `salt` of the parameter file's lines.

Statements and proofs. `Model.Verify.planned` makes all chains' plans at one setting, that of the
lines (`Params.settingOf`); it spells each plan into parameter bytes and reads these bytes back. The
reader takes the plan's third word as it stands. So the word that is read back is the lines' word,
as a word of 64 bits. No file but the three public files is looked at, and no yes of the program is
asked.

Main theorems.
 `Params.Given.read_salt`     what `Given.read` returns on bytes spelled from a plan P holds P's
                              salt as a word of 64 bits. No bound on the bytes' length is asked.
 `Params.configure_oneTime_salt`  the one-time chain's parameter bytes that `configure` returns are
                              spelled from a plan whose salt is the lines'.
 `Model.Verify.planned_key_salt`  where `planned` returns p: the lines l are read from the parameter
                              file, and the salt in p's one-time chain is l's, as a word of 64 bits.
 `Flat.salt_atPlan`           for a ground (OnBytes/Tie/EntryGround.lean) whose link's plan has the
                              salt of its lines, below 2^64: if G is at the plan of Z (`AtPlan`,
                              OnBytes/Flat/BigAt.lean) and Z's parameter file says the ground's
                              lines, the salt of the ground's link's plan is the salt of the plan of
                              G's key's one-time chain.
 `Flat.salt_atPlan_full`, `Flat.salt_atPlan_small`   at the library's two grounds.

What is not claimed. Nothing on the other words of the plan or on its entries. Nothing on the shared
and the second chain (`TieK.KeyChainsFacts`, OnBytes/TieK/ChainsRead.lean, ties their settings to
the one-time chain's). That `planned` returns at
any files. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.BigAt
import OnBytes.Model.VerifyDigest
import OnBytes.Plan.PlanListsConfigure
import OnBytes.Tie.EntryGrounds

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- If the reader of a plan returns a value at the place where a plan's spelling begins, the salt in
that value is the plan's, as a word of 64 bits. -/
theorem rdPlan_salt {P P' : Plan} {pre post : ByteArray} {k : Nat}
    (h : rdPlan (pre ++ P.bytes ++ post) pre.size = some (P', k)) :
    P'.salt = (UInt64.ofNat P.salt).toNat := by
  rw [plan_bytes] at h
  have a := undoes_many undoes_word (P.words.map UInt64.ofNat) (fun _ _ => trivial) pre
    (cat (P.entries.map Entry.bytes) ++ post)
  have e1 : pre ++
        (cat ((P.words.map UInt64.ofNat).map u64) ++ cat (P.entries.map Entry.bytes)) ++ post =
      pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        (cat (P.entries.map Entry.bytes) ++ post) := by
    simp only [ByteArray.append_assoc]
  have hw : (P.words.map UInt64.ofNat).length = 8 := rfl
  rw [hw] at a
  generalize cat ((P.words.map UInt64.ofNat).map u64) = W at a e1 h
  unfold rdPlan at h
  rw [e1, a] at h
  simp only [Plan.words, List.map_cons, List.map_nil, fldOf_num] at h
  split at h
  · obtain ⟨x, _, h2⟩ := Option.map_eq_some_iff.1 h
    cases h2
    rfl
  · cases h

/-- The same for the reader of parameter bytes. -/
theorem paramsRead_salt {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (h : paramsRead (paramsBytes P cfg others) = some x) :
    x.plan.salt = (UInt64.ofNat P.salt).toNat := by
  generalize hv : item versionName (versionValue P.field) = V
  generalize hcf : item configName cfg = Cf
  have eb : paramsBytes P cfg others = V ++ P.bytes ++ Cf ++ items others := by
    simp only [paramsBytes, paramsHead, hv, hcf]
  have a :=
    undoes_item _ (version_ok P.field) ByteArray.empty (P.bytes ++ Cf ++ items others)
  simp only [hv, ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at a
  have e1 : V ++ P.bytes ++ Cf ++ items others = V ++ (P.bytes ++ Cf ++ items others) := by
    simp only [ByteArray.append_assoc]
  have e2 : V ++ P.bytes ++ Cf ++ items others = V ++ P.bytes ++ (Cf ++ items others) := by
    simp only [ByteArray.append_assoc]
  rw [← e1] at a
  rw [eb] at h
  unfold paramsRead at h
  rw [a] at h
  simp only at h
  split at h
  · rename_i P' j hP
    rw [e2] at hP
    have hs := rdPlan_salt hP
    split at h
    · split at h
      · split at h
        · obtain ⟨_, _, h2⟩ := Option.map_eq_some_iff.1 h
          cases h2
          exact hs
        · cases h
      · cases h
    · cases h
  · cases h

/-- The same for `Given.read`, the program's reader of parameter bytes. -/
theorem Given.read_salt {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (h : Given.read (paramsBytes P cfg others) = some g) :
    g.plan.salt = (UInt64.ofNat P.salt).toNat := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P cfg others) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      exact paramsRead_salt hp
    · cases h

/-- The parameter bytes of the key's one-time chain that `configure` returns are spelled from a plan
whose salt is the lines'. -/
theorem configure_oneTime_salt {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    ∃ P I, made.keyOneTime = Fmt.paramsBytes P cfg I ∧ P.salt = l.salt := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨oneTime, ho, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, _, h⟩ := exc_bind h
  have hs : oneTime.plan.salt = l.salt := by
    show oneTime.set.saltBytes = l.salt
    rw [finishHeld_set ho, (Plan.keySized_oneTime (sized_key hz)).2]
    rfl
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
    exact ⟨_, _, rfl, hs⟩
  · cases h

end OnBytes.Params

namespace OnBytes.Model.Verify

open OnBytes.Params (exc_bind)

/-- If `planned` returns p on the three public files, `Params.readLines` reads lines l from the
parameter file, and what p's chains hold as made is what `Params.configure` returns on l, some
shapes, the digest in p and 0 bits. -/
theorem planned_madeKey {pol KL lay : ByteArray} {p : Planned}
    (h : planned pol KL (some lay) = .ok p) :
    ∃ l rest shapes, Params.readLines pol = .ok (l, rest) ∧
      Params.configure l shapes p.cfg 0 = .ok p.chains.made := by
  unfold planned at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨chains, hc, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  obtain ⟨rest, hr⟩ := polScan_frame (publicOf_scan hX)
  obtain ⟨shapes, hm⟩ := chainsOf_made hc
  exact ⟨X.P.frame, rest, shapes, hr, hm⟩

/-- **The salt in the plan of the key's one-time chain, as read back, is the lines'**, as a word of
64 bits. -/
theorem planned_key_salt {pol KL lay : ByteArray} {p : Planned}
    (h : planned pol KL (some lay) = .ok p) :
    ∃ l rest, Params.readLines pol = .ok (l, rest) ∧
      p.chains.key.oneTime.given.plan.salt = (UInt64.ofNat l.salt).toNat := by
  obtain ⟨l, rest, shapes, hr, hm⟩ := planned_madeKey h
  obtain ⟨P, I, e, es⟩ := Params.configure_oneTime_salt hm
  obtain ⟨k1, -, -⟩ := Params.KeyChains.read_parts (planned_read h).1
  have hg := Params.OneTime.read_given k1
  have e' : p.chains.bytes .keyOneTime = Fmt.paramsBytes P p.cfg I := e
  rw [e'] at hg
  exact ⟨l, rest, hr, by rw [Params.Given.read_salt hg, es]⟩

end OnBytes.Model.Verify

namespace OnBytes.Flat

open OnBytes.Tie

/-- **The salt of the ground's link's plan is the salt of the plan of G's key's one-time chain**, if
G is at the plan of Z and Z's parameter file says the ground's lines. hq, hs: two facts on the
ground alone. -/
theorem salt_atPlan (D : EntryGround) (hq : D.q.given.plan.salt = D.lines.salt)
    (hs : D.lines.salt < 2 ^ 64) {X R : Type} {Z : OnBytes.K.Pub} {G : FilesParameters X R} (hG : AtPlan Z G)
    (hl : D.SaysLines Z.pol) : D.q.given.plan.salt = G.k.oneTime.given.plan.salt := by
  obtain ⟨p, hp, hk, -, -⟩ := hG
  obtain ⟨l, rest, h1, h2⟩ := Model.Verify.planned_key_salt hp
  have e : l = D.lines := by
    unfold EntryGround.SaysLines at hl
    rw [h1] at hl
    exact Option.some.inj hl
  rw [hk, h2, e, hq, Fmt.toNat_ofNat_lt _ hs]

/-- At the full size. -/
theorem salt_atPlan_full {X R : Type} {Z : OnBytes.K.Pub} {G : FilesParameters X R} (hG : AtPlan Z G)
    (hl : recordGround.SaysLines Z.pol) :
    recordGround.q.given.plan.salt = G.k.oneTime.given.plan.salt :=
  salt_atPlan recordGround rfl (by decide) hG hl

/-- At the small example. -/
theorem salt_atPlan_small {X R : Type} {Z : OnBytes.K.Pub} {G : FilesParameters X R} (hG : AtPlan Z G)
    (hl : smallRecordGround.SaysLines Z.pol) :
    smallRecordGround.q.given.plan.salt = G.k.oneTime.given.plan.salt :=
  salt_atPlan smallRecordGround rfl (by decide) hG hl

end OnBytes.Flat
