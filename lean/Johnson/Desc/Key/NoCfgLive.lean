-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/NoCfgLive.lean: the key file's description as its makers return it is THE SAME at
every digest of the public files but 32 zero bytes, wherever its test on the file says yes.
Johnson/Desc/Key/NoCfgAt.lean leaves the test on the file (`fileOk`) open; here its four clauses
that read the digest are followed.

Main names.
  fileOk_atCfg: at a source carried to the digest c: if `fileOk` says yes at the source, c is not 32
    zero bytes, and the clause "read" says yes at the carried values, then `fileOk` says yes at the
    carried source.
  readOk_at: the clause "read" at what the planner returns at another digest.
  descOfMade_live, descAt_live: where `descAt X lay c` returns F with F.fileOk = true,
    `descAt X lay c'` returns F.
  same_of_planOk: where `descAt` returns at two digests and both descriptions say yes on the plan,
    they are one. No premise names 32 zero bytes; BUT A YES ON THE PLAN HOLDS THE CLAUSE "digest":
    so both digests are other than that.
  laidAt_live_of: where `keyDataAndDecisionAtDigest X lay c` (Johnson/Desc/Key/Slot.lean) returns data and a decision,
    and the door says yes at the carried record too, `keyDataAndDecisionAtDigest X lay c'` returns the same two.

Limits. Asked: both digests have 32 bytes; c' is not 32 zero bytes; of `descAt` also: the seven
strings of parameter bytes have fewer than 2 ^ 64 bytes each (where the piece is laid the door has
asked that: Johnson/Desc/Key/Asks.lean). No law here hangs on the door's list but through
`asks_bytes`, which Johnson/Desc/Key/AsksFirstTest.lean (the pin of the door's list of one test) holds.
`descAt_live` and `laidAt_live_of` go one way: from a value that is made at c. AT c = 32 ZERO BYTES
NOTHING IS LAID (the clause "digest"), while at another c' a value may be: whoever lays the piece at
a constant digest does not ask that the files' own digest is not 32 zero bytes. The words of a
refusal are not followed. Of the decision on three views alone: what the transcript's hashing starts
from is not here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.NoCfgAt
import Johnson.Desc.Key.AsksLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Tie OnBytes.Params OnBytes.Model.Verify
open Johnson.G.OfPlan (Made)

/-- Entry by entry: a yes in the first list gives a yes in the second. -/
abbrev Carries (l l' : List (String × Bool)) : Prop :=
  List.Forall₂ (fun a b => a.2 = true → b.2 = true) l l'

theorem all_of_carries : ∀ {l l' : List (String × Bool)}, Carries l l' →
    l.all (·.2) = true → l'.all (·.2) = true
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, hl => by
    rw [List.all_cons, Bool.and_eq_true] at hl ⊢
    exact ⟨h hl.1, all_of_carries t hl.2⟩

theorem carries_refl : ∀ l : List (String × Bool), Carries l l
  | [] => .nil
  | _ :: l => .cons id (carries_refl l)

theorem carries_append : ∀ {l₁ l₁' l₂ l₂' : List (String × Bool)}, Carries l₁ l₁' →
    Carries l₂ l₂' → Carries (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a t, h => .cons a (carries_append t h)

theorem sameGiven_atCfg (g : Given) (c : ByteArray) (h : sameGiven g g = true) :
    sameGiven (g.atCfg c) (g.atCfg c) = true := by
  unfold sameGiven at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, h9⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨beq_self_bytes _, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, beq_self_bytes _⟩, h9⟩

theorem sameKey_atCfg (k : KeyChains) (c : ByteArray) (h : sameKeyChains k k = true) :
    sameKeyChains (keyAtCfg k c) (keyAtCfg k c) = true := by
  unfold sameKeyChains at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨sameGiven_atCfg _ c a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, sameGiven_atCfg _ c a6⟩, a7⟩,
    a8⟩, sameGiven_atCfg _ c a9⟩

/-- What the planner returns holds the key's three chains as read off its own three strings. -/
theorem chainsOf_reads {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X lay c = .ok ch) :
    KeyChains.read ch.made.keyOneTime ch.made.keyShared ch.made.keySecond = some ch.key := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, e1, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨z, e2, h⟩ := exc_bind h
  obtain ⟨u, e3, h⟩ := exc_bind h
  obtain ⟨made, e4, h⟩ := exc_bind h
  split at h
  · rename_i key link proof hk hl hp
    obtain rfl : _ = ch := Except.ok.inj h
    exact hk
  · cases h

/-- Where the planner returns the carried chains, the clause "read" at the carried key is the key
held against itself. -/
theorem readOk_carried {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X lay c = .ok (chainsAtCfg ch c)) :
    readAgainOk (keyAtCfg ch.key c) = sameKeyChains (keyAtCfg ch.key c) (keyAtCfg ch.key c) := by
  have r : KeyChains.read (keyAtCfg ch.key c).oneTime.given.bytes
      (keyAtCfg ch.key c).shared.given.bytes (keyAtCfg ch.key c).second.given.bytes =
      some (keyAtCfg ch.key c) := chainsOf_reads h
  unfold readAgainOk
  rw [r]

/-- **The clause "read" at another digest.** -/
theorem readOk_at {X : Public} {lay : Option ByteArray} {c c' : ByteArray} {ch : Chains}
    (hc : c.size = 32) (hc' : c'.size = 32) (hb : ∀ n : ChainName, (ch.bytes n).size < 2 ^ 64)
    (h : chainsOf X lay c = .ok ch) (hr : readAgainOk ch.key = true) :
    readAgainOk (keyAtCfg ch.key c') = true := by
  have e : chainsAtCfg ch c = ch := chainsAtCfg_self hc hb h
  have ek : keyAtCfg ch.key c = ch.key := congrArg (·.key) e
  have s : sameKeyChains ch.key ch.key = true := by
    have t := readOk_carried (chainsOf_at hc hc hb h)
    rw [ek] at t
    exact t.symm.trans hr
  rw [readOk_carried (chainsOf_at hc hc' hb h)]
  exact sameKey_atCfg _ c' s

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (c : ByteArray)

theorem clauses_atCfg (hr : readAgainOk (keyAtCfg X.Y.k c) = true) :
    Carries (sourceClauses X.Y) (sourceClauses (X.atCfg c).Y) := by
  unfold sourceClauses
  refine .cons id (.cons ?_ (.cons id (.cons id (.cons id (.cons (fun _ => hr) ?_)))))
  · intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨sameSetting_atCfg _ _ c h.1.1.1, sameSetting_atCfg _ _ c h.1.1.2⟩, h.1.2⟩, h.2⟩
  · repeat (first | exact .nil | refine .cons id ?_)

theorem shapeClauses_atCfg (made : LinShape) :
    Carries (shapeClauses X.Y.k made) (shapeClauses (X.atCfg c).Y.k made) := by
  unfold shapeClauses
  refine .cons id (.cons id (.cons id (.cons id (.cons id (.cons id (.cons id (.cons id (.cons id
    (.cons ?_ (.cons id (.cons id .nil)))))))))))
  intro h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨sameSetting_atCfg _ _ c h.1.1.1.1.1, sameSetting_atCfg _ _ c h.1.1.1.1.2⟩,
    h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem fileClauses_atCfg (r₁ r₂ r₃ : Nat) (hd : (c != Fmt.zero32) = true)
    (hr : readAgainOk (keyAtCfg X.Y.k c) = true) :
    Carries (fileClauses X N P r₁ r₂ r₃) (fileClauses (X.atCfg c) N P r₁ r₂ r₃) := by
  unfold fileClauses
  refine carries_append (carries_append (carries_append (clauses_atCfg X c hr)
    (shapeClauses_atCfg X c _)) (carries_refl _)) ?_
  refine .cons id (.cons id (.cons id (.cons id (.cons id (.cons id (.cons id (.cons id
    (.cons (fun _ => hd) (.cons id (.cons id (.cons id .nil)))))))))))

/-- **The test on the file at a carried source.** -/
theorem fileOk_atCfg (h : (descriptionFromSource X N P).fileOk = true) (hd : (c != Fmt.zero32) = true)
    (hr : readAgainOk (keyAtCfg X.Y.k c) = true) : (descriptionFromSource (X.atCfg c) N P).fileOk = true := by
  have h2 := Bool.and_eq_true_iff.1 h
  exact Bool.and_eq_true_iff.2
    ⟨all_of_carries (fileClauses_atCfg X N P c _ _ _ hd hr) h2.1, h2.2⟩

/-- The clause "read" is one of the test on the file's. -/
theorem readOk_of_fileOk (h : (descriptionFromSource X N P).fileOk = true) : readAgainOk X.Y.k = true := by
  have h2 := Bool.and_eq_true_iff.1 h
  exact List.all_eq_true.1 h2.1 ("read", readAgainOk X.Y.k)
    (by unfold fileClauses sourceClauses; simp)

omit X N P c in
/-- The maker keeps what the planner returns. -/
theorem madeAt_chains {X : Public} {lay c : ByteArray} {m : Made} (h : madeAt X lay c = .ok m) :
    chainsOf X (some lay) c = .ok m.p.chains := by
  unfold madeAt at h
  obtain ⟨ch, h1, h⟩ := exc_bind h
  obtain ⟨b, h2, h⟩ := exc_bind h
  obtain ⟨l, h3, h⟩ := exc_bind h
  split at h
  · obtain rfl : _ = m := Except.ok.inj h
    exact h1
  · cases h

omit X N P c in
/-- The source's three chains' values are the planner's. -/
theorem sourceOf_k {m : Made} {X : Source} (h : sourceOf m = .ok X) : X.Y.k = m.p.chains.key := by
  unfold sourceOf at h
  obtain ⟨D, h1, h⟩ := exc_bind h
  obtain ⟨T, h2, h⟩ := exc_bind h
  obtain rfl : _ = X := Except.ok.inj h
  rfl

omit X N P c in
/-- The maker keeps what it was handed of the public files. -/
theorem madeAt_public {X : Public} {lay c : ByteArray} {m : Made} (h : madeAt X lay c = .ok m) :
    m.p.X = X := by
  unfold madeAt at h
  obtain ⟨ch, h1, h⟩ := exc_bind h
  obtain ⟨b, h2, h⟩ := exc_bind h
  obtain ⟨l, h3, h⟩ := exc_bind h
  split at h
  · obtain rfl : _ = m := Except.ok.inj h
    rfl
  · cases h

omit X N P c in
/-- **The description off the carried record is the same**, where its test on the file says yes and
the other digest is not 32 zero bytes. -/
theorem descOfMade_live {X : Public} {lay c c' : ByteArray} {m : Made} {F : FileDescription Xi}
    (hc : c.size = 32) (hc' : c'.size = 32) (hz : (c' != Fmt.zero32) = true)
    (hb : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64) (hm : madeAt X lay c = .ok m)
    (h : descriptionFromPlan m = .ok F) (hF : F.fileOk = true) : descriptionFromPlan (madeAtCfg m c') = .ok F := by
  obtain ⟨S, N, P, hS, hN, hP, rfl⟩ := descOfMade_is m F h
  have hr : readAgainOk (keyAtCfg S.Y.k c') = true := by
    rw [sourceOf_k hS]
    refine readOk_at hc hc' hb (madeAt_chains hm) ?_
    rw [← sourceOf_k hS]
    exact readOk_of_fileOk S N P hF
  unfold descriptionFromPlan
  rw [sourceOf_atCfg m c' S hS, rangesNumbers_atCfg, hN, placesK_atCfg, hP]
  show Except.ok (descriptionFromSource (S.atCfg c') N P) = _
  rw [desc_atCfg, fileOk_atCfg S N P c' hF hz hr, ← hF]

omit X N P c in
/-- **The description is the same at every digest but 32 zero bytes**, where its test on the file
says yes. -/
theorem descAt_live {X : Public} {lay c c' : ByteArray} {F : FileDescription Xi} (hc : c.size = 32)
    (hc' : c'.size = 32) (hz : (c' != Fmt.zero32) = true)
    (hb : ∀ m, madeAt X lay c = .ok m → ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (h : descAt X lay c = .ok F) (hF : F.fileOk = true) : descAt X lay c' = .ok F := by
  obtain ⟨m, S, N, P, hm, -, -, -, -⟩ := descAt_is X lay c F h
  have hd : descriptionFromPlan m = .ok F := by
    unfold descAt at h
    rw [hm] at h
    exact h
  unfold descAt
  rw [madeAt_at hc hc' (hb m hm) hm]
  exact descOfMade_live hc hc' hz (hb m hm) hm hd hF

omit X N P c in
/-- The test on the file is one of the tests on the plan. -/
theorem fileOk_of_planOk (F : FileDescription Xi) (h : F.planOk = true) : F.fileOk = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1

omit X N P c in
/-- **Where both say yes on the plan, the descriptions at two digests are one.** (A yes on the plan
holds the clause "digest": so neither digest is 32 zero bytes.) -/
theorem same_of_planOk {X : Public} {lay c c' : ByteArray} {F F' : FileDescription Xi} (hc : c.size = 32)
    (hc' : c'.size = 32)
    (hb : ∀ m, madeAt X lay c = .ok m → ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (h : descAt X lay c = .ok F) (h' : descAt X lay c' = .ok F') (hp : F.planOk = true)
    (hp' : F'.planOk = true) : F' = F := by
  obtain ⟨b, hb'⟩ := descAt_at hc hc' hb h
  obtain rfl : { F with fileOk := b } = F' := Except.ok.inj (hb'.symm.trans h')
  have e : b = true := fileOk_of_planOk _ hp'
  rw [e, ← fileOk_of_planOk F hp]

omit X N P c in
/-- The seven strings have the same lengths at the carried record. -/
theorem bytes_atCfg {X : Public} {lay c c' : ByteArray} {m : Made} (hc : c.size = 32)
    (hc' : c'.size = 32) (hb : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hm : madeAt X lay c = .ok m) :
    ∀ n : ChainName, ((madeAtCfg m c').p.chains.bytes n).size < 2 ^ 64 := fun n =>
  (size_bytes_chainsAtCfg hc hc' hb (madeAt_chains hm) n).trans_lt (hb n)

omit X N P c in
/-- **The key file's piece is the same at every digest but 32 zero bytes**, where it is made: the
same data and the same decision: WHERE THE DOOR SAYS YES AT THE CARRIED RECORD TOO. That it does is
the premise `ha'`. -/
theorem laidAt_live_of {X : Public} {lay c c' : ByteArray} {D : Maker.WholeD} {r : KeyRun}
    (hc : c.size = 32) (hc' : c'.size = 32) (hz : (c' != Fmt.zero32) = true)
    (h : keyDataAndDecisionAtDigest X lay c = .ok (D, r))
    (ha' : ∀ m F, madeAt X lay c = .ok m → descriptionFromPlan m = .ok F →
      (∀ t ∈ lawsAsk X lay m F D, t.2 = true) →
      ∀ t ∈ lawsAsk X lay (madeAtCfg m c') F D, t.2 = true) :
    keyDataAndDecisionAtDigest X lay c' = .ok (D, r) := by
  obtain ⟨m, S, N, P, hm, -, -, -, hF, hp, hw, ho, ha, hd, rfl⟩ := laidAt_is X lay c D r h
  have hb := asks_bytes ha
  have hF' : descriptionFromPlan m = .ok (descriptionFromSource S N P) := by
    unfold descAt at hF
    rw [hm] at hF
    exact hF
  exact laidAt_of X lay c' (madeAtCfg m c') (descriptionFromSource S N P) D (madeAt_at hc hc' hb hm)
    (descOfMade_live hc hc' hz hb hm hF' (fileOk_of_planOk _ hp)) hp hw ho hd
    (ha' m _ hm hF' ha)

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.readOk_at
#print axioms VerifiableInference.Desc.Key.fileClauses_atCfg
#print axioms VerifiableInference.Desc.Key.fileOk_atCfg
#print axioms VerifiableInference.Desc.Key.readOk_of_fileOk
#print axioms VerifiableInference.Desc.Key.madeAt_public
#print axioms VerifiableInference.Desc.Key.descOfMade_live
#print axioms VerifiableInference.Desc.Key.descAt_live
#print axioms VerifiableInference.Desc.Key.same_of_planOk
#print axioms VerifiableInference.Desc.Key.bytes_atCfg
#print axioms VerifiableInference.Desc.Key.laidAt_live_of
