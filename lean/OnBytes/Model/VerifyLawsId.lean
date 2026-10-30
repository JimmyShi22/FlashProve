-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyLawsId.lean: the commitment ID and the bits of a whole call that ends with a
passing result.

OnBytes/Model/VerifyLawsWhole.lean says which three functions said yes if a whole call passes. This
file adds two things that such a call has tested: the options hold a commitment ID, and it is the ID
that the call formed itself; and the requested bits are exactly 128.

Main theorems.
- `cpStagesRun_id`: if the result of a call is a passing one, then an ID that is needed was named,
  and a named ID is the first stage's (the empty string, if there is no stage).
- `wholeCall_id`: if `wholeCall` returns a passing result, the options hold an ID, and in lower-case
  digits it is the hexadecimal form of `Key.commitmentId` on the tables' shape and the digest in p,
  the value that `planned` returned on the three configuration files, and on the table that
  `Key.check` returned. The requested bits are 128.

What is not claimed. Nothing on soundness. What the commitment ID fixes is not stated here:
`Key.commitmentId` is a function of the shape, of the digest of the three configuration files, and
of the table's root and answers (the record's seeds, which the hashed string also holds, are drawn
by the hash from shape, digest and root), and nothing is proved here of the hash in it, nor of
`Fmt.hex`: that equal digits mean equal bytes is not stated here; OnBytes/Tie/IdKey.lean proves it
(`hex_inj`). That what enters the hashed string is coded one to one is proved in
OnBytes/Tie/IdKeySeed.lean, of a string that is `Fmt.publishedBytes` by
OnBytes/Tie/IdKeySeedFmt.lean; OnBytes/Tie/IdKey.lean proves the like of the string without the
seeds, which is not what the ID hashes. Neither this file nor OnBytes/Tie/ZeroId.lean says what two
whole calls that returned 0 under one ID share. The key's proofs,
the entry, the request, the reply and the proof file do not enter the ID. That the digest in p,
which enters the ID, is the digest that the chains in p hold, under which the three checks read, is
not stated here: see OnBytes/Tie/SameChains.lean. That the caller took the ID from where the
commitment is published is the caller's matter. The number 128 is what the options' field for the
requested bits holds, which is also its value if the call names no bits: that any round's error is
below 2^-128 is not stated. The other limits in the head of OnBytes/Model/VerifyLawsWhole.lean hold
here too, but for the one on the commitment ID. For proofs only; the program does not import this
file.
-/
import OnBytes.Model.VerifyLawsWhole

set_option autoImplicit false

namespace OnBytes.Model

open OnBytes.Params (exc_bind exc_guard exc_either)

namespace Stages

/-- If the result of a call is a passing one: an ID that is needed was named, and a named ID is the
one that the first stage in the list holds, or the empty string if the list of stages is empty. The
callers in OnBytes/Model/Verify.lean pass one stage or three. -/
theorem cpStagesRun_id {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)}
    (h : (cpStagesRun stages part belowBar asked id about).passing = true) :
    (id.needed = true → id.named = true) ∧
      (id.named = true →
        id.asked = (((stages.map StageOut.asRead).head?).map (·.idHex)).getD "") := by
  unfold cpStagesRun at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    constructor
    · intro hn
      simp_all
    · intro hn
      simp_all

end Stages

namespace Verify

open OnBytes.Model.Stages

/-- In what the first tests of a call return: `needed` is the argument of that name; `named` says
whether the options hold an ID; `asked` is that ID in lower-case digits. The requested bits are at
most `hashLeast`. -/
theorem readFirst_id {o : Options} {f : Files} {needed : Bool} {r : Read}
    (h : readFirst o f needed = .ok r) :
    r.id.needed = needed ∧ r.id.named = o.id.isSome ∧
      (∀ t, o.id = some t → idAsked t = some r.id.asked) ∧ o.bits ≤ hashLeast := by
  have hbits : ∀ {u : Unit},
      callNeeds (decide (o.bits ≤ hashLeast)) "cp-bits-above-digest" = .ok u →
        o.bits ≤ hashLeast := by
    intro u hb
    unfold callNeeds at hb
    split at hb
    · rename_i hd
      exact of_decide_eq_true hd
    · cases hb
  unfold readFirst at h
  dsimp only at h
  split at h
  · rename_i hid
    obtain ⟨asked, ha, h⟩ := exc_bind h
    obtain ⟨_, hb, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨⟨pol, kl, lay⟩, _, h⟩ := exc_bind h
    dsimp only at h
    obtain ⟨key, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    cases ha
    refine ⟨rfl, rfl, fun t ht => ?_, hbits hb⟩
    rw [hid] at ht
    cases ht
  · rename_i t hid
    split at h
    · rename_i x hx
      obtain ⟨asked, ha, h⟩ := exc_bind h
      obtain ⟨_, hb, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨⟨pol, kl, lay⟩, _, h⟩ := exc_bind h
      dsimp only at h
      obtain ⟨key, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      cases h
      cases ha
      refine ⟨rfl, rfl, fun t' ht => ?_, hbits hb⟩
      rw [hid] at ht
      cases ht
      exact hx
    · obtain ⟨_, ha, _⟩ := exc_bind h
      cases ha

/-- The first tests of a whole call keep what `readFirst` returns on the ID, with an ID needed. The
requested bits are at most `hashLeast`. -/
theorem readCall_id {o : Options} {f : Files} {r : Read} (h : readCall o f = .ok r) :
    r.id.needed = true ∧ r.id.named = o.id.isSome ∧
      (∀ t, o.id = some t → idAsked t = some r.id.asked) ∧ o.bits ≤ hashLeast := by
  unfold readCall at h
  replace h := exc_guard h
  obtain ⟨r0, h0, h⟩ := exc_bind h
  have h1 := readFirst_id h0
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

/-- The ID in what the common beginning of the stages returns is the hexadecimal form of
`Key.commitmentId` on the tables' shape and the digest in p and on the first table. -/
theorem commonOfCall_id {r : Read} {C : Common} {p : Planned} (h : commonOfCall r = .ok C)
    (hp : planned r.pol r.KL r.layout = .ok p) :
    C.idHex = Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg C.first) := by
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
    rfl
  · obtain ⟨_, h2, _⟩ := exc_bind h1
    cases h2

/-- A stage's result holds the ID that it was given. -/
theorem stageOut_idHex (name : StageName) (idHex : String) (x : Except Refused Found) :
    (stageOut name idHex x).idHex = idHex := by
  match x with
  | .error _ => rfl
  | .ok (_, _, _) => rfl

/-- The whole call. If the tests before the entry is read returned a number, and `wholeCall` on the
same files with the entry returns a passing result, then for the files r that `readCall` returned,
the value p that `planned` returned on them and the table that `Key.check` returned: the options
hold an ID t, and t in lower-case digits is the hexadecimal form of `Key.commitmentId` on the
tables' shape and the digest in p and on that table. The requested bits are 128: that is the field
of the options, which is also its value if the call names no bits, and no bound on an error. -/
theorem wholeCall_id {o : Options} {f : Files} {k : Nat} {entry : FileIn} {r : Read} {p : Planned}
    {table : Params.TableName} (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) (hr : readCall o f = .ok r)
    (hp : planned r.pol r.KL r.layout = .ok p) (ht : Key.check p.chains.key r.key = .ok table) :
    (∃ t, o.id = some t ∧
      idAsked t = some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg table))) ∧
      o.bits = 128 := by
  obtain ⟨r', ent, p', C, table', further, g1, _, g3, g4, g5, g6, g7, _, _, g10⟩ :=
    wholeCall_passed hk h
  have er : r' = r := Except.ok.inj (g1.symm.trans hr)
  subst er
  have ep : p' = p := Except.ok.inj (g4.symm.trans hp)
  subst ep
  have et : table' = table := Except.ok.inj (g7.symm.trans ht)
  subst et
  obtain ⟨i1, i2, i3, i4⟩ := readCall_id hr
  subst g3
  unfold wholeCall at h
  rw [readCall_entry, hr] at h
  dsimp only at h
  unfold stagesOf at h
  rw [g5] at h
  obtain ⟨j1, j2⟩ := cpStagesRun_id h
  have hnamed := j1 i1
  have hasked : r'.id.asked = C.idHex := by
    rw [j2 hnamed]
    exact stageOut_idHex .key C.idHex (keyStage C o.bits r'.key)
  obtain ⟨p2, j, k1, _, k3⟩ := commonOfCall_ok g5
  have e2 : p2 = p' := Except.ok.inj (k1.symm.trans g4)
  subst e2
  obtain ⟨j', d1⟩ := keyCheck_table g7
  have e1 : C.first = table' := readTable_same k3 d1
  constructor
  · cases ho : o.id with
    | none =>
      rw [ho] at i2
      rw [i2] at hnamed
      cases hnamed
    | some t =>
      refine ⟨t, rfl, ?_⟩
      rw [i3 t ho, hasked, commonOfCall_id g5 g4, e1]
  · have b1 : bar = 128 := rfl
    have b2 : hashLeast = 128 := rfl
    unfold askedBelowBar at g10
    have b3 := of_decide_eq_false g10
    omega

end Verify

end OnBytes.Model

#print axioms OnBytes.Model.Verify.wholeCall_id
